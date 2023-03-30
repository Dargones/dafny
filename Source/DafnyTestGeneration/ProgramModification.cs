#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using Microsoft.Dafny;
using Program = Microsoft.Boogie.Program;

namespace DafnyTestGeneration {
  public class Modifications {
    private readonly DafnyOptions options;
    public Modifications(DafnyOptions options) {
      this.options = options;
    }

    private readonly Dictionary<string, ProgramModification> idToModification = new();
    public ProgramModification GetProgramModification(Program program,
      Implementation impl, HashSet<int> coversBlocks, HashSet<string> capturedStates, string procedure,
      string uniqueId) {
      if (!idToModification.ContainsKey(uniqueId)) {
        idToModification[uniqueId] =
          new ProgramModification(options, program, impl, coversBlocks, capturedStates, procedure, uniqueId);
      }
      return idToModification[uniqueId];
    }

    public IEnumerable<ProgramModification> Values => idToModification.Values;

    public int NumberOfBlocksCovered(Implementation implementation, bool onlyIfTestsExists = false) {
      return NumberOfBlocksCovered(implementation, implementation.Blocks
        .Where(block => block.Cmds.Count != 0)
        .Select(block => block.UniqueId).ToHashSet(), onlyIfTestsExists);
    }

    public int NumberOfBlocksCovered(Implementation implementation, HashSet<int> blockIds, bool onlyIfTestsExists = false) {
      var relevantModifications = ModificationsForImplementation(implementation).Where(modification =>
        modification.counterexampleStatus == ProgramModification.Status.Success && (!onlyIfTestsExists || (modification.testMethod != null && modification.testMethod.IsValid)));
      return blockIds.Count(blockId =>
        relevantModifications.Any(mod => mod.coversBlocks.Contains(blockId)));
    }

    public IEnumerable<ProgramModification> ModificationsForImplementation(Implementation implementation) =>
      Values.Where(modification =>
        modification.implementation == implementation ||
        options.TestGenOptions.TargetMethod != null);

    internal int ModificationsWithStatus(Implementation implementation, ProgramModification.Status status) =>
      ModificationsForImplementation(implementation)
        .Count(mod => mod.counterexampleStatus == status);
  }

  /// <summary>
  /// Records a modification of the boogie program under test. The modified
  /// program has an assertion that should fail provided a certain block is
  /// visited / path is taken.
  /// </summary>
  public class ProgramModification {
    private DafnyOptions Options { get; }

    internal enum Status { Success, Failure, Untested }

    internal Status counterexampleStatus;
    public readonly Implementation implementation; // implementation under test

    private readonly string uniqueId;
    public readonly HashSet<string> CapturedStates;

    private readonly string procedure; // procedure to start verification from
    private Program/*?*/ program;
    internal readonly HashSet<int> coversBlocks;
    private string/*?*/ counterexampleLog;
    internal TestMethod testMethod;

    public ProgramModification(DafnyOptions options, Program program, Implementation impl,
      HashSet<int> coversBlocks, HashSet<string> capturedStates,
      string procedure, string uniqueId) {
      Options = options;
      implementation = impl;
      counterexampleStatus = Status.Untested;
      this.program = Utils.DeepCloneProgram(options, program);
      this.procedure = procedure;
      this.coversBlocks = coversBlocks;
      CapturedStates = capturedStates;
      this.uniqueId = uniqueId;
      counterexampleLog = null;
      testMethod = null;
    }

    /// <summary>
    /// Setup CommandLineArguments to prepare verification. This is necessary
    /// because the procsToCheck field in CommandLineOptions (part of Boogie)
    /// is private meaning that the only way of setting this field is by calling
    /// options.Parse() on a new DafnyObject.
    /// </summary>
    private static DafnyOptions SetupOptions(DafnyOptions original, string procedure) {
      var options = DafnyOptions.Create();
      options.Parse(new[] { "/proc:" + procedure });
      options.NormalizeNames = false;
      options.EmitDebugInformation = true;
      options.ErrorTrace = 1;
      options.EnhancedErrorMessages = 1;
      options.ModelViewFile = "-";
      var proverOptions = new SMTLibSolverOptions(original);
      proverOptions.Parse(original.ProverOptions);
      var z3Version = DafnyOptions.GetZ3Version(proverOptions.ProverPath);
      options.ProverOptions = new List<string>() {
        "O:model_evaluator.completion=true",
        "O:model.completion=true"
      };
      foreach (var option in original.ProverOptions) {
        options.ProverOptions.Add(option);
      }
      if (z3Version is null || z3Version < new Version(4, 8, 6)) {
        options.ProverOptions.Insert(0, "O:model.compress=false");
      } else {
        options.ProverOptions.Insert(0, "O:model.compact=false");
      }

      options.Prune = !original.TestGenOptions.DisablePrune;
      options.ProverOptions.AddRange(original.ProverOptions);
      options.LoopUnrollCount = original.LoopUnrollCount;
      options.DefiniteAssignmentLevel = original.DefiniteAssignmentLevel;
      options.WarnShadowing = original.WarnShadowing;
      options.VerifyAllModules = original.VerifyAllModules;
      options.TimeLimit = original.TimeLimit;
      return options;
    }

    /// <summary>
    /// Return the counterexample log produced by trying to verify this modified
    /// version of the original boogie program. Return null if this
    /// counterexample does not cover any new SourceModifications.
    /// </summary>
    public async Task<string>/*?*/ GetCounterExampleLog(Modifications cache) {
      if (counterexampleStatus != Status.Untested ||
          (coversBlocks.Count != 0 && IsCovered(cache))) {
        return counterexampleLog;
      }
      var options = SetupOptions(Options, procedure);
      var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      var guid = Guid.NewGuid().ToString();
      program.Resolve(options);
      program.Typecheck(options);
      engine.EliminateDeadVariables(program);
      engine.CollectModSets(program);
      engine.Inline(program);
      var writer = new StringWriter();
      var result = await Task.WhenAny(engine.InferAndVerify(writer, program,
            new PipelineStatistics(), null,
            _ => { }, guid),
          Task.Delay(TimeSpan.FromSeconds(Options.TimeLimit <= 0 ?
            TestGenerationOptions.DefaultTimeLimit : Options.TimeLimit)));
      program = null; // allows to garbage collect what is no longer needed
      counterexampleStatus = Status.Failure;
      counterexampleLog = null;
      if (result is not Task<PipelineOutcome>) {
        if (Options.TestGenOptions.Verbose) {
          Console.WriteLine(
            $"// No test can be generated for {uniqueId} " +
            "because the verifier timed out.");
        }
        return counterexampleLog;
      }
      var log = writer.ToString();
      // make sure that there is a counterexample (i.e. no parse errors, etc):
      var stringReader = new StringReader(log);
      while (await stringReader.ReadLineAsync() is { } line) {
        if (line.StartsWith("Block |")) {
          counterexampleLog = log;
          counterexampleStatus = Status.Success;
          var blockId = int.Parse(Regex.Replace(line, @"\s+", "").Split('|')[2]);
          coversBlocks.Add(blockId);
          if (Options.TestGenOptions.Verbose &&
              Options.TestGenOptions.Mode != TestGenerationOptions.Modes.Path) {
            Console.WriteLine($"// Test targeting block {uniqueId} also covers block {blockId}");
          }
        }
      }
      if (Options.TestGenOptions.Verbose && counterexampleLog == null) {
        if (log == "") {
          Console.WriteLine(
            $"// No test is generated for {uniqueId} " +
            "because the verifier proved that no inputs could cause this block to be visited.");
        } else if (log.Contains("MODEL") || log.Contains("anon0")) {
          Console.WriteLine(
            $"// No test is generated for {uniqueId} " +
            "because there is no enhanced error trace. This can be caused " +
            "by a bug in boogie counterexample model parsing.");
        } else {
          Console.WriteLine(
            $"// No test is generated for {uniqueId} " +
            "because the verifier timed out.");
        }
      }
      return counterexampleLog;
    }

    public async Task<TestMethod> GetTestMethod(Modifications cache, DafnyInfo dafnyInfo, bool returnNullIfNotUnique = true) {
      if (Options.TestGenOptions.Verbose) {
        Console.WriteLine(
          $"// Extracting the test for {uniqueId} from the counterexample...");
      }
      var log = await GetCounterExampleLog(cache);
      if (log == null) {
        return null;
      }
      testMethod = new TestMethod(dafnyInfo, log);
      if (!testMethod.IsValid || !returnNullIfNotUnique) {
        return testMethod;
      }
      var duplicate = cache.ModificationsForImplementation(implementation)
        .Where(mod => mod != this && Equals(mod.testMethod, testMethod))
        .FirstOrDefault((ProgramModification)null);
      if (Options.TestGenOptions.Verbose && duplicate != null) {
        Console.WriteLine(
          $"// Test for {uniqueId} is a duplicate of a test previously generated " +
          $"for {duplicate.uniqueId}. This happens when test generation tool " +
          $"does not know how to differentiate between counterexamples, " +
          $"e.g. if branching is conditional on the result of a trait instance " +
          $"method call.");
      }
      return testMethod;
    }

    public bool IsCovered(Modifications cache) => cache.NumberOfBlocksCovered(implementation, coversBlocks) == coversBlocks.Count;
  }
}
