#nullable disable

using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;
using Function = Microsoft.Dafny.Function;

namespace DafnyTestGeneration.Inlining;

/// <summary>
/// Separates the bodies of function-by-methods into separate methods so that translator will process them accordingly.
/// </summary>
public class SeparateByMethodRewriter : IRewriter {

  private readonly List<Method> methodsToAdd = new();

  public SeparateByMethodRewriter(ErrorReporter reporter) : base(reporter) { }

  public void PostResolve(Program program) {
    SeparateByMethod(program.DefaultModule);
  }

  private void SeparateByMethod(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.TopLevelDecls.Iter(SeparateByMethod);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      methodsToAdd.Clear();
      withMembers.Members.OfType<Function>().Iter(SeparateByMethod);
      withMembers.Members.AddRange(methodsToAdd);
    }
  }

  private void SeparateByMethod(Function func) {
    if (func.ByMethodBody == null || func.ByMethodDecl == null) {
      return;
    }
    methodsToAdd.Add(func.ByMethodDecl);
    func.ByMethodDecl = null;
    func.ByMethodBody = null;
    func.ByMethodTok = null;
  }
}