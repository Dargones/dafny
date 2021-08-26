using System.Collections.Generic;
using System.IO;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace DafnyTestGeneration {
  public class BlockBasedModification : ProgramModification {

    private readonly int blockId;
    private static readonly ISet<int> covered = new HashSet<int>();
    // set of states (points in Dafny code) captured by the block in question:
    private readonly ISet<string> capturedStates;

    public BlockBasedModification(Program program, string procedure,
      int blockId, ISet<string> capturedStates) : base(program, procedure) {
      this.blockId = blockId;
      this.capturedStates = capturedStates;
    }

    /// <summary>
    /// Return the log or null if the counterexample in the log does not
    /// cover any new blocks.
    /// </summary>
    public override string? Log {
      get {
        if (covered.Contains(blockId) || log == null) {
          return null;
        }
        string? line;
        var stringReader = new StringReader(log);
        var newBlocksCovered = false;
        while ((line = stringReader.ReadLine()) != null) {
          if (!line.StartsWith("Block |")) {
            continue;
          }
          var newId = int.Parse(Regex.Replace(line, @"\s+", "").Split('|')[2]);
          if (covered.Contains(newId)) {
            continue;
          }
          newBlocksCovered = true;
          covered.Add(newId);
        }
        return newBlocksCovered ? log : null;
      }
    }

    /// <summary>
    /// If the corresponding block was not mentioned in any of the logs
    /// generated so far, return the set of captured states it represents, if
    /// any. Return an empty set otherwise. Make sure to run
    /// GetCounterExampleLog before calling this method.
    /// </summary>
    public ISet<string> GetKnownDeadStates() {
      if (covered.Contains(blockId)) {
        return new HashSet<string>();
      }
      return capturedStates;
    }

    public ISet<string> GetAllStates() {
      return capturedStates;
    }
  }
}