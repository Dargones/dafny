﻿// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Token = Microsoft.Dafny.Token;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using LiteralExpr = Microsoft.Boogie.LiteralExpr;
using LocalVariable = Microsoft.Boogie.LocalVariable;
using Parser = Microsoft.Boogie.Parser;
using Program = Microsoft.Boogie.Program;
using Type = Microsoft.Boogie.Type;

namespace DafnyTestGeneration {

  /// <summary>
  /// Contains functionality that allows to generate various modifications
  /// of a Boogie program with assertions that fail when a particular
  /// condition is met (such as when a block is visited or a path is taken)
  /// </summary>
  public abstract class ProgramModifier {
    internal static readonly string ImplPrefix = "Impl$$";
    internal static readonly string CtorPostfix = "__ctor";
    protected DafnyInfo DafnyInfo;

    /// <summary>
    /// Create tests and return the list of bpl test files
    /// </summary>
    public IEnumerable<ProgramModification> GetModifications(
      Program program,
      DafnyInfo dafnyInfo) {
      DafnyInfo = dafnyInfo;
      var options = dafnyInfo.Options;
      var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      engine.CoalesceBlocks(program); // removes redundant basic blocks
      program = new AnnotationVisitor(this, options).VisitProgram(program);
      AddAxioms(options, program);
      program.Resolve(options);
      program.Typecheck(options);
      // TODO: Uncomment the following 5 lines once Boogie > 2.16.9 is merged to optimize performance.
      // TODO: Also make TODO marked changes in ImplementationIsToBeTested and ProgramModification
      /*engine.EliminateDeadVariables(program);
      engine.CollectModSets(program);
      engine.Inline(program);
      program.RemoveTopLevelDeclarations(declaration => declaration is Implementation or Procedure && Utils.DeclarationHasAttribute(declaration, "inline"));
      program = new RemoveChecks(options).VisitProgram(program);*/
      if (options.TestGenOptions.PrintBpl != null) {
        File.WriteAllText(options.TestGenOptions.PrintBpl,
          Utils.GetStringRepresentation(options, program));
      }
      return GetModifications(program);
    }

    protected abstract IEnumerable<ProgramModification> GetModifications(Program p);

    protected bool ImplementationIsToBeTested(Implementation impl) =>
      // TODO: Remove the second clause once Boogie > 2.16.9 is merged to optimize performance. 
      // TODO: Also make TODO marked changes in ProgramModification and ProgramModifier
      (Utils.DeclarationHasAttribute(impl, TestGenerationOptions.TestEntryAttribute) || 
       Utils.DeclarationHasAttribute(impl, "inline")) &&
      impl.Name.StartsWith(ImplPrefix) && !impl.Name.EndsWith(CtorPostfix) &&
      !DafnyInfo.IsGhost(impl.VerboseName.Split(" ").First());

    /// <summary>
    /// Add axioms necessary for counterexample generation to work efficiently
    /// </summary>
    private static void AddAxioms(DafnyOptions options, Program program) {
      if (options.TestGenOptions.SeqLengthLimit == 0) {
        return;
      }
      var limit = (uint)options.TestGenOptions.SeqLengthLimit;
      Parser.Parse($"axiom (forall<T> y: Seq T :: " +
                   $"{{ Seq#Length(y) }} Seq#Length(y) <= {limit});",
        "", out var tmpProgram);
      program.AddTopLevelDeclaration(
        (Axiom)tmpProgram.TopLevelDeclarations.ToList()[0]);
    }

    /// <summary>
    /// Create an assume command that prints objects in the
    /// <param name="data">list</param> as part of error trace.
    /// </summary>
    private static AssumeCmd GetAssumePrintCmd(
      List<object> data,
      string separator = " | ") {
      // first insert separators between the things being printed
      var toPrint = new List<object>();
      data.Iter(obj => toPrint.AddRange(new List<object> { obj, separator }));
      if (toPrint.Count() != 0) {
        toPrint.RemoveAt(toPrint.Count() - 1);
      }
      // now create the assume command
      var annotation = new QKeyValue(new Token(), "print", toPrint, null);
      return new AssumeCmd(new Token(),
        new LiteralExpr(new Token(), true), annotation);
    }

    /// <summary>
    /// Create a new local variable with a name that has not been reserved
    /// </summary>
    protected static LocalVariable GetNewLocalVariable(
      Implementation impl,
      Type type,
      string baseName = "tmp") {
      string name = baseName;
      if (impl.LocVars.Exists(v => v.Name == name)) {
        int id = 0;
        while (impl.LocVars.Exists(v => v.Name == baseName + id)) {
          id++;
        }
        name = baseName + id;
      }
      var newLocalVar = new LocalVariable(new Token(),
        new TypedIdent(new Token(), name, type));
      impl.LocVars.Add(newLocalVar);
      return newLocalVar;
    }

    /// <summary>
    /// Annotate the AST with "assume true" print statements inserted at:
    /// (1)     the beginning of each implementation, to get the parameter types
    ///         and values leading to assertion or post-condition violation.
    /// (2)     the end of each block, to get execution trace.
    /// </summary>
    private class AnnotationVisitor : StandardVisitor {
      private DafnyOptions options;
      private Implementation/*?*/ implementation;
      private readonly ProgramModifier modifier;

      public AnnotationVisitor(ProgramModifier modifier, DafnyOptions options) {
        this.modifier = modifier;
        this.options = options;
      }

      public override Block VisitBlock(Block node) {
        var state = Utils.GetBlockId(node);
        if (state == node.Label) {
          return base.VisitBlock(node); // ignore blocks with zero commands
        }
        var data = new List<object>
          { "Block", implementation.Name, state };
        int afterPartition = node.cmds.FindIndex(cmd =>
          cmd is not AssumeCmd assumeCmd || assumeCmd.Attributes == null || assumeCmd.Attributes.Key != "partition");
        node.cmds.Insert(afterPartition, GetAssumePrintCmd(data));
        return node;
      }

      public override Implementation VisitImplementation(Implementation node) {
        implementation = node;
        // print parameter types:
        var data = new List<object> { "Types" };
        data.AddRange(node.InParams.Select(var =>
          var.TypedIdent.Type.ToString()));
        node.Blocks[0].cmds.Insert(0, GetAssumePrintCmd(data));

        // record parameter values:
        data = new List<object> { "Impl", node.VerboseName.Split(" ")[0] };
        data.AddRange(node.InParams.Select(var => new IdentifierExpr(new Token(), var)));
        node.Blocks[0].cmds.Insert(0, GetAssumePrintCmd(data));
        if (Utils.DeclarationHasAttribute(node, TestGenerationOptions.TestInlineAttribute)) {
          // This method is inlined (and hence tested)
          // TODO: Should you test that the argument exists and is an integer?
          var depthExpression = Utils.GetAttributeValue(node, TestGenerationOptions.TestInlineAttribute).First();
          var attribute = new QKeyValue(new Token(), "inline",
            new List<object>() { depthExpression }, null);
          attribute.Next = node.Attributes;
          node.Attributes = attribute;
          VisitBlockList(node.Blocks);
        } else if (Utils.DeclarationHasAttribute(node, TestGenerationOptions.TestEntryAttribute)) {
          VisitBlockList(node.Blocks);
        }
        return node;
      }

      public override Program VisitProgram(Program node) {
        node = base.VisitProgram(node);
        return node;
      }
    }

    /// <summary>
    /// Replace assertions with assumptions and ensures with free ensures to
    /// alleviate the verification burden. Return a reresolved copy of the AST.
    /// </summary>
    public class RemoveChecks : StandardVisitor {
      private DafnyOptions options;

      public RemoveChecks(DafnyOptions options) {
        this.options = options;
      }

      public override Block VisitBlock(Block node) {
        var toRemove = node.cmds.OfType<AssertCmd>().ToList();
        foreach (var cmd in toRemove) {
          var newCmd = new AssumeCmd(new Token(), cmd.Expr, cmd.Attributes);
          node.cmds.Insert(node.cmds.IndexOf(cmd), newCmd);
          node.cmds.Remove(cmd);
        }
        return node;
      }

      public override Procedure VisitProcedure(Procedure node) {
        List<Ensures> newEnsures = new();
        foreach (var e in node.Ensures) {
          newEnsures.Add(new Ensures(
            new Token(),
            true,
            e.Condition,
            e.Comment,
            e.Attributes));
        }
        node.Ensures = newEnsures;
        return node;
      }

      public override Program VisitProgram(Program node) {
        VisitDeclarationList(node.TopLevelDeclarations.ToList());
        return Utils.DeepCloneResolvedProgram(node, options);
      }
    }
  }
}
