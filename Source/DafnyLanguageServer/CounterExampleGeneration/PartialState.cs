// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration; 

public class PartialState {

  public string isGuard = null;
  public List<string> loopGuards = new();
  internal readonly DafnyModel Model;
  internal readonly Model.CapturedState State;
  private const string InitialStateName = "<initial>";
  private static readonly Regex StatePositionRegex = new(
    @".*\((?<line>\d+),(?<character>\d+)\)",
    RegexOptions.IgnoreCase | RegexOptions.Singleline
  );

  private const string BoundVarPrefix = "boundVar";

  internal PartialState(DafnyModel model, Model.CapturedState state) {
    Model = model;
    State = state;
    SetupBoundVars();
    SetupVars();
  }
  
  /// <summary>
  /// Start with the union of vars and boundVars and expand the set by adding 
  /// variables that represent fields of any object in the original set or
  /// elements of any sequence in the original set, etc. This is done
  /// recursively in breadth-first order and only up to a certain maximum
  /// depth.
  /// </summary>
  /// <param name="maxDepth">The maximum depth up to which to expand the
  /// variable set.</param>
  /// <returns>Set of variables</returns>
  public HashSet<PartialValue> ExpandedVariableSet(int maxDepth) {
    HashSet<PartialValue> expandedSet = new();
    // The following is the queue for elements to be added to the set. The 2nd
    // element of a tuple is the depth of the variable w.r.t. the original set
    List<Tuple<PartialValue, int>> varsToAdd = new();
    PartialValue.AllPartialValuesForState(this).ForEach(variable => varsToAdd.Add(new(variable, 0)));
    while (varsToAdd.Count != 0) {
      var (next, depth) = varsToAdd[0];
      varsToAdd.RemoveAt(0);
      if (expandedSet.Contains(next)) {
        continue;
      }
      if (depth == maxDepth) {
        break;
      }
      expandedSet.Add(next);
      // fields of primitive types are skipped:
      foreach (var v in next.GetRelatedValues().
          Where(variable => !expandedSet.Contains(variable) && !variable.IsPrimitive)) {
        varsToAdd.Add(new(v, depth + 1));
      }
    }
    return expandedSet;
  }
  
  public Statement AsAssumption() {
    var variables = ExpandedVariableSet(-1).ToArray();
    var boundVars = new List<BoundVar>();
    // TODO: make sure bound variable identifiers are not already taken
    for (int i = 0; i < variables.Length; i++) {
      if (!variables[i].HasCompleteDefinition) {
        boundVars.Add(new BoundVar(Token.NoToken, BoundVarPrefix + boundVars.Count, variables[i].Type));
        variables[i].AddDefinition(new IdentifierExpr(Token.NoToken, boundVars.Last()), new());
      }
    }
    var constraints = new HashSet<Expression>();
    foreach (var variable in variables) {
      foreach (var constraint in variable.ResolvableConstraints) {
        constraints.Add(constraint);
      }
    }

    Expression expression = null;
    if (constraints.Count == 0) {
      expression = new LiteralExpr(Token.NoToken, true);
    }
    if (constraints.Count == 1) {
      expression = constraints.First();
    } else {
      foreach (var constraint in constraints) {
        if (expression == null) {
          expression = constraint;
          continue;
        }

        expression = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, expression, constraint);
      }
    }

    if (constraints.Count > 1 && boundVars.Count > 0) {
      expression = new ExistsExpr(Token.NoToken, RangeToken.NoToken, boundVars, null, expression, null);
    }

    if (loopGuards.Count != 0) {
      Expression loopGuard = new IdentifierExpr(Token.NoToken, loopGuards[0]);
      for (int i = 1; i < loopGuards.Count; i++) {
        loopGuard = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, loopGuard,
          new IdentifierExpr(Token.NoToken, loopGuards[i]));
      }
      expression = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Imp, loopGuard, expression);
    }

    if (isGuard == null) {
      return new AssumeStmt(RangeToken.NoToken, expression, null);
    }
    return new UpdateStmt(RangeToken.NoToken, new List<Expression>() { new IdentifierExpr(Token.NoToken, isGuard) },
        new List<AssignmentRhs>() { new ExprRhs(expression) });
  }

  /// <summary>
  /// Initialize the vars list, which stores all variables relevant to
  /// the counterexample except for the bound variables
  /// </summary>
  private void SetupVars() {
    var names = Enumerable.Empty<string>();
    foreach (var partialState in Model.States) {
      names = names.Concat(partialState.State.Variables);
    }
    names = names.Concat(State.Variables).Distinct().ToList();
    var notDefinitelyAssigned = new HashSet<string>();
    foreach (var name in names) {
      if (!name.StartsWith("defass#")) {
        continue;
      }
      var val = State.TryGet(name);
      if (val == null) {
        continue;
      }
      if (val is Model.Boolean { Value: false }) {
        notDefinitelyAssigned.Add(name[7..]);
      }
    }
    foreach (var v in names) {
      if (!DafnyModel.IsUserVariableName(v) || notDefinitelyAssigned.Contains(v)) {
        continue;
      }
      var val = State.TryGet(v);
      if (val == null) {
        continue; // This variable has no value in the model, so ignore it.
      }

      var value = PartialValue.Get(val, this);
      value.AddDefinition(new IdentifierExpr(Token.NoToken, v.Split("#").First()), new());
    }
  }

  /// <summary>
  /// Instantiate BoundVariables
  /// </summary>
  private void SetupBoundVars() {
    foreach (var f in Model.Model.Functions) {
      if (f.Arity != 0) {
        continue;
      }
      int n = f.Name.IndexOf('!');
      if (n == -1) {
        continue;
      }
      var name = f.Name[..n];
      if (!name.Contains('#') || name.Contains('$')) {
        continue;
      }

      var value = PartialValue.Get(f.GetConstant(), this);
      value.AddDefinition(new IdentifierExpr(Token.NoToken, name), new());
    }
  }
  
  public string FullStateName => State.Name;

  private string ShortenedStateName => ShortenName(State.Name, 20);

  public bool IsInitialState => FullStateName.Equals(InitialStateName);

  public int GetLineId() {
    var match = StatePositionRegex.Match(ShortenedStateName);
    if (!match.Success) {
      throw new ArgumentException(
        $"state does not contain position: {ShortenedStateName}");
    }
    return int.Parse(match.Groups["line"].Value);
  }

  public int GetCharId() {
    var match = StatePositionRegex.Match(ShortenedStateName);
    if (!match.Success) {
      throw new ArgumentException(
        $"state does not contain position: {ShortenedStateName}");
    }
    return int.Parse(match.Groups["character"].Value);
  }

  private static string ShortenName(string name, int fnLimit) {
    var loc = TryParseSourceLocation(name);
    if (loc != null) {
      var fn = loc.Filename;
      int idx = fn.LastIndexOfAny(new[] { '\\', '/' });
      if (idx > 0) {
        fn = fn[(idx + 1)..];
      }
      if (fn.Length > fnLimit) {
        fn = fn[..fnLimit] + "..";
      }
      var addInfo = loc.AddInfo;
      if (addInfo != "") {
        addInfo = ":" + addInfo;
      }
      return $"{fn}({loc.Line},{loc.Column}){addInfo}";
    }
    return name;
  }

  /// <summary>
  /// Parse a string (typically the name of the captured state in Boogie) to
  /// extract a SourceLocation from it. An example of a string to be parsed:
  /// @"c:\users\foo\bar.c(12,10) : random string"
  /// The ": random string" part is optional.
  /// </summary>
  private static SourceLocation TryParseSourceLocation(string name) {
    int par = name.LastIndexOf('(');
    if (par <= 0) {
      return null;
    }
    var res = new SourceLocation { Filename = name[..par] };
    var words = name[(par + 1)..]
      .Split(',', ')', ':')
      .Where(x => x != "")
      .ToArray();
    if (words.Length < 2) {
      return null;
    }
    if (!int.TryParse(words[0], out res.Line) ||
        !int.TryParse(words[1], out res.Column)) {
      return null;
    }
    int colon = name.IndexOf(':', par);
    res.AddInfo = colon > 0 ? name[(colon + 1)..].Trim() : "";
    return res;
  }

  private class SourceLocation {
    public string Filename;
    public string AddInfo;
    public int Line;
    public int Column;
  }
  
}