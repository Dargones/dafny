// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;
using Function = Microsoft.Dafny.Function;

namespace DafnyTestGeneration.Inlining;

/// <summary> Turns each function into a function-by-method and removes all opaque attributes. </summary>
public class AddByMethodRewriter : IRewriter {

  protected internal AddByMethodRewriter(ErrorReporter reporter) : base(reporter) { }

  internal void PreResolve(Program program) {
    AddByMethod(program.DefaultModule);
  }

  private void AddByMethod(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.TopLevelDecls.Iter(AddByMethod);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      withMembers.Members.OfType<Function>().Iter(AddByMethod);
    }
  }

  private static Attributes RemoveOpaqueAttr(Attributes attributes, Cloner cloner) {
    if (attributes == null) {
      return null;
    }

    if (attributes.Name == "opaque") {
      RemoveOpaqueAttr(attributes.Prev, cloner);
    }

    if (attributes is UserSuppliedAttributes) {
      var usa = (UserSuppliedAttributes)attributes;
      return new UserSuppliedAttributes(
        cloner.Tok(usa.tok),
        cloner.Tok(usa.OpenBrace),
        cloner.Tok(usa.CloseBrace),
        attributes.Args.ConvertAll(cloner.CloneExpr),
        RemoveOpaqueAttr(attributes.Prev, cloner));
    }

    return new Attributes(attributes.Name,
      attributes.Args.ConvertAll(cloner.CloneExpr),
      RemoveOpaqueAttr(attributes.Prev, cloner));
  }

  private void AddByMethod(Function func) {

    func.Attributes = RemoveOpaqueAttr(func.Attributes, new Cloner());
    if (func.IsGhost ||
        func.Body == null ||
        func.ByMethodBody != null ||
        (!Utils.MembersHasAttribute(func, TestGenerationOptions.TestInlineAttribute) && !Utils.MembersHasAttribute(func, TestGenerationOptions.TestEntryAttribute))) {
      return;
    }

    var returnStatement = new ReturnStmt(func.Body.RangeToken,
      new List<AssignmentRhs> { new ExprRhs(new Cloner().CloneExpr(func.Body)) });
    func.ByMethodBody = new BlockStmt(
      func.Body.RangeToken,
      new List<Statement> { returnStatement });
    func.ByMethodTok = func.Body.tok;
  }
}