using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny;

using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration {

  public static class Main {

    /// <summary>
    /// This method returns each capturedState that is unreachable, one by one,
    /// and then a line with the summary of how many such states there are, etc.
    /// Note that loop unrolling may cause false positives and the absence of
    /// loop unrolling may cause false negatives.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<string> GetDeadCodeStatistics(Program program) {

      var modifications = GetModifications(program).ToList();
      var blocksReached = modifications.Count;
      HashSet<string> allStates = new();
      HashSet<string> allDeadStates = new();

      // Generate tests based on counterexamples produced from modifications
      for (var i = modifications.Count - 1; i >= 0; i--) {
        await modifications[i].GetCounterExampleLog();
        var deadStates = ((BlockBasedModification)modifications[i]).GetKnownDeadStates();
        if (deadStates.Count != 0) {
          foreach (var capturedState in deadStates) {
            yield return $"Code at {capturedState} is potentially unreachable.";
          }
          blocksReached--;
          allDeadStates.UnionWith(deadStates);
        }
        allStates.UnionWith(((BlockBasedModification)modifications[i]).GetAllStates());
      }

      yield return $"Out of {modifications.Count} basic blocks " +
                   $"({allStates.Count} capturedStates), {blocksReached} " +
                   $"({allStates.Count - allDeadStates.Count}) are reachable. " +
                   $"There might be false negatives if you are not unrolling " +
                   $"loops. False positives are always possible.";
    }

    public static async IAsyncEnumerable<string> GetDeadCodeStatistics(string sourceFile) {
      var source = await new StreamReader(sourceFile).ReadToEndAsync();
      var program = Utils.Parse(source, sourceFile);
      if (program == null) {
        yield return "Cannot parse program";
        yield break;
      }

      await foreach (var line in GetDeadCodeStatistics(program)) {
        yield return line;
      }
    }

    private static IEnumerable<ProgramModification> GetModifications(Program program) {
      // Translate the Program to Boogie:
      var oldPrintInstrumented = DafnyOptions.O.PrintInstrumented;
      DafnyOptions.O.PrintInstrumented = true;
      var boogiePrograms = Translator
        .Translate(program, program.Reporter)
        .ToList().ConvertAll(tuple => tuple.Item2);
      DafnyOptions.O.PrintInstrumented = oldPrintInstrumented;

      // Create modifications of the program with assertions for each block\path
      ProgramModifier programModifier =
        DafnyOptions.O.TestGenOptions.Mode == TestGenerationOptions.Modes.Path
          ? new PathBasedModifier()
          : new BlockBasedModifier();
      return programModifier.GetModifications(boogiePrograms);
    }

    /// <summary>
    /// Generate test methods for a certain Dafny program.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<TestMethod> GetTestMethodsForProgram(
      Program program, DafnyInfo? dafnyInfo = null) {

      dafnyInfo ??= new DafnyInfo(program);
      var modifications = GetModifications(program).ToList();

      // Generate tests based on counterexamples produced from modifications
      var testMethods = new ConcurrentBag<TestMethod>();
      for (var i = modifications.Count - 1; i >= 0; i--) {
        var log = await modifications[i].GetCounterExampleLog();
        if (log == null) {
          continue;
        }
        var testMethod = new TestMethod(dafnyInfo, log);
        if (testMethods.Contains(testMethod)) {
          continue;
        }
        testMethods.Add(testMethod);
        yield return testMethod;
      }
    }

    public static IEnumerable<string> GetTestClassPrelude(string sourceFile, DafnyInfo dafnyInfo) {

        var rawName = Path.GetFileName(sourceFile).Split(".").First();

        string EscapeDafnyStringLiteral(string str) {
          return $"\"{str.Replace(@"\", @"\\")}\"";
        }

        yield return $"include {EscapeDafnyStringLiteral(sourceFile)}";
        yield return $"module {rawName}UnitTests {{";
        foreach (var module in dafnyInfo.ToImport) {
          yield return $"import {module}";
        }
    }

    private static async Task<string> RetMethodIfVerified(string sourceFile, DafnyInfo dafnyInfo, string methodStr) {
      try {
        string testClassPrelude = GetTestClassPrelude(sourceFile, dafnyInfo).Aggregate("", (x, y) => x = x + y + '\n');
        string testClassWithSingleMethod = testClassPrelude + methodStr 
          + TestMethod.EmitSynthesizeMethods() + "\n}";
        Program? dafnyProgram = Utils.Parse(testClassWithSingleMethod, 
          Path.GetFileName(sourceFile), new ErrorReporterSink());

        if (dafnyProgram != null) {
          var engine = Microsoft.Boogie.ExecutionEngine.CreateWithoutSharedCache(DafnyOptions.O);
          var boogiePrograms = Translator.Translate(dafnyProgram, dafnyProgram.Reporter).ToList().ConvertAll(tuple => tuple.Item2);
          var boogieProgram = ProgramModifier.MergeBoogiePrograms(boogiePrograms);
          var writer = new StringWriter();
          var uniqueId = System.Guid.NewGuid().ToString();

          Task<(Microsoft.Boogie.PipelineOutcome, Microsoft.Boogie.PipelineStatistics)> 
            boogieTask = Microsoft.Dafny.Main.BoogieOnce(writer, engine, "", "", boogieProgram, uniqueId);

          var task = await Task.WhenAny(
            boogieTask,
            Task.Delay(System.TimeSpan.FromSeconds(DafnyOptions.O.TestGenOptions.Timeout)));

          if (task == boogieTask) {
            var (outcome, stats) = await boogieTask;

            if (Microsoft.Dafny.Main.IsBoogieVerified(outcome, stats)) 
              return methodStr;
          }
        }
        return "";
      } catch (System.Exception) {
        return "";
      }
    }

    /// <summary>
    /// Return a Dafny class (list of lines) with tests for the given Dafny file
    /// </summary>
    public static async IAsyncEnumerable<string> GetTestClassForProgram(string sourceFile) {

      TestMethod.ClearTypesToSynthesize();
      var source = new StreamReader(sourceFile).ReadToEnd();
      var program = Utils.Parse(source, sourceFile);
      if (program == null) {
        yield break;
      }
      var dafnyInfo = new DafnyInfo(program);

      foreach (var line in GetTestClassPrelude(sourceFile, dafnyInfo))
        yield return line;

      await foreach (var method in GetTestMethodsForProgram(program, dafnyInfo)) {
        string methodStr = method.ToString();
        if (DafnyOptions.O.TestGenOptions.PruneFailedTests) {
          yield return await RetMethodIfVerified(sourceFile, dafnyInfo, methodStr);
        } else {
          yield return methodStr;
        }
      }

      yield return TestMethod.EmitSynthesizeMethods();

      yield return "}";
    }
  }
}