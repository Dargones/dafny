#nullable disable
using System.Collections.Generic;
using System.IO;
using System.Linq;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Errors = Microsoft.Dafny.Errors;
using Function = Microsoft.Dafny.Function;
using Parser = Microsoft.Dafny.Parser;
using Program = Microsoft.Dafny.Program;
using Token = Microsoft.Dafny.Token;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  public static class Utils {
    
    /// <summary>
    /// Take a resolved type and change all names to fully-qualified.
    /// </summary>
    public static Type UseFullName(Type type) {
      return DafnyModelTypeUtils
        .ReplaceType(type, _ => true, typ => new UserDefinedType(
          new Token(),
          typ?.ResolvedClass?.FullName ?? typ.Name,
          typ.TypeArgs));
    }

    /// <summary>
    /// Copy a <param name="type"></param> and recursively replace type
    /// arguments named as in <param name="from"></param> with types from
    /// <param name="to"></param>.
    /// </summary>
    public static Type CopyWithReplacements(Type type, List<string> from, List<Type> to) {
      if (from.Count != to.Count) {
        return type;
      }
      Dictionary<string, Type> replacements = new();
      for (int i = 0; i < from.Count; i++) {
        replacements[from[i]] = to[i];
      }
      replacements["_System.string"] =
        new UserDefinedType(new Token(), "string", new List<Type>());
      replacements["_System.nat"] =
        new UserDefinedType(new Token(), "nat", new List<Type>());
      replacements["_System.object"] =
        new UserDefinedType(new Token(), "object", new List<Type>());
      return DafnyModelTypeUtils.ReplaceType(type, _ => true,
        typ => replacements.ContainsKey(typ.Name) ?
          replacements[typ.Name] :
          new UserDefinedType(typ.tok, typ.Name, typ.TypeArgs));
    }

    /// <summary>
    /// Parse a string read (from a certain file) to a Dafny Program
    /// </summary>
    public static Program/*?*/ Parse(string source, string fileName = "") {
      ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      var builtIns = new BuiltIns();
      var reporter = new ConsoleErrorReporter();
      var success = Parser.Parse(source, fileName, fileName, null, module, builtIns,
        new Errors(reporter)) == 0 && Microsoft.Dafny.Main.ParseIncludesDepthFirstNotCompiledFirst(module, builtIns,
        new HashSet<string>(), new Errors(reporter)) == null;
      Program/*?*/ program = null;
      if (success) {
        program = new Program(fileName, module, builtIns, reporter);
      }
      if (program == null) {
        return null;
      }
      // Substitute function methods with function-by-methods
      new AddByMethodRewriter(new ConsoleErrorReporter()).PreResolve(program);
      program.Reporter = new ErrorReporterSink();
      new Resolver(program).ResolveProgram(program);
      return program;
    }

    /// <summary>
    /// Deep clone a Boogie program.
    /// </summary>
    public static Microsoft.Boogie.Program
      DeepCloneProgram(Microsoft.Boogie.Program program) {
      var textRepresentation = GetStringRepresentation(program);
      Microsoft.Boogie.Parser.Parse(textRepresentation, "", out var copy);
      return copy;
    }

    public static string GetStringRepresentation(Microsoft.Boogie.Program program) {
      var oldPrintInstrumented = DafnyOptions.O.PrintInstrumented;
      var oldPrintFile = DafnyOptions.O.PrintFile;
      DafnyOptions.O.PrintInstrumented = true;
      DafnyOptions.O.PrintFile = "-";
      var output = new StringWriter();
      program.Emit(new TokenTextWriter(output, DafnyOptions.O));
      DafnyOptions.O.PrintInstrumented = oldPrintInstrumented;
      DafnyOptions.O.PrintFile = oldPrintFile;
      return output.ToString();
    }

    /// <summary>
    /// Turns each function-method into a function-by-method.
    /// Copies body of the function into the body of the corresponding method.
    /// </summary>
    private class AddByMethodRewriter : IRewriter {

      protected internal AddByMethodRewriter(ErrorReporter reporter) : base(reporter) { }
      
      internal void PreResolve(Program program) {
        AddByMethod(program.DefaultModule);
      }

      private static void AddByMethod(TopLevelDecl d) {
        if (d is LiteralModuleDecl moduleDecl) {
          moduleDecl.ModuleDef.TopLevelDecls.ForEach(AddByMethod);
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
          var usa = (UserSuppliedAttributes) attributes;
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

      private static void AddByMethod(Function func) {
        func.Attributes = RemoveOpaqueAttr(func.Attributes, new Cloner());
        if (func.IsGhost || func.Body == null || func.ByMethodBody != null) {
          return;
        }
        var returnStatement = new ReturnStmt(new Token(), new Token(),
          new List<AssignmentRhs> { new ExprRhs(func.Body) });
        func.ByMethodBody = new BlockStmt(new Token(), new Token(),
          new List<Statement> { returnStatement });
      }
    }
  }
}
