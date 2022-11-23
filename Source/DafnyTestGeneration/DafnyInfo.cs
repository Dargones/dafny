#nullable disable
using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;
using Function = Microsoft.Dafny.Function;
using IdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using LetExpr = Microsoft.Dafny.LetExpr;
using OldExpr = Microsoft.Dafny.OldExpr;
using Program = Microsoft.Dafny.Program;
using Token = Microsoft.Dafny.Token;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  /// <summary> Extract essential info from a parsed Dafny program </summary>
  public class DafnyInfo {

    public readonly Dictionary<string, Method> methods;
    public readonly Dictionary<string, Function> functions;
    public readonly Dictionary<string, IndDatatypeDecl> Datatypes;
    private readonly Dictionary<string, ClassDecl> Classes;
    // import required to access the code contained in the program
    public readonly Dictionary<string, string> ToImportAs;
    private readonly Dictionary<string, (List<TypeParameter> args, Type superset)> subsetToSuperset;
    private readonly Dictionary<string, Expression> witnessForType;
    private readonly Dictionary<string, (IVariable variable, Expression expr)> conditionForType;
    // list of top level scopes accessible from the testing module
    private readonly List<VisibilityScope> scopes;

    public DafnyInfo(Program program) {
      methods = new Dictionary<string, Method>();
      functions = new Dictionary<string, Function>();
      ToImportAs = new Dictionary<string, string>();
      Datatypes = new Dictionary<string, IndDatatypeDecl>();
      Classes = new Dictionary<string, ClassDecl>();
      witnessForType = new Dictionary<string, Expression>();
      conditionForType =
        new Dictionary<string, (IVariable variable, Expression expr)>();
      subsetToSuperset =
        new Dictionary<string, (List<TypeParameter> args, Type superset)>();
      subsetToSuperset["_System.string"] = new(
        new List<TypeParameter>(),
        new SeqType(new CharType()));
      subsetToSuperset["string"] = new(
        new List<TypeParameter>(),
        new SeqType(new CharType()));
      subsetToSuperset["_System.nat"] = new(
        new List<TypeParameter>(),
        Type.Int);
      subsetToSuperset["nat"] = new(
        new List<TypeParameter>(),
        Type.Int);
      subsetToSuperset["_System.object"] = new(
        new List<TypeParameter>(),
        new UserDefinedType(new Token(), "object", new List<Type>()));
      scopes = program.DefaultModuleDef.TopLevelDecls?
        .OfType<LiteralModuleDecl>()
        .Select(declaration =>
          declaration.DefaultExport.VisibilityScope).ToList() ?? new List<VisibilityScope>();
      var visitor = new DafnyInfoExtractor(this);
      visitor.Visit(program);
    }

    public string GetCompiledName(string callable) {
      if (methods.ContainsKey(callable)) {
        return GetFullCompiledName(methods[callable]);
      }
      if (functions.ContainsKey(callable)) {
        return GetFullCompiledName(functions[callable]);
      }
      throw new Exception("Cannot identify callable " + callable);
    }

    private static string GetFullCompiledName(MemberDecl decl) {
      var fullCompiledName = decl.CompileName;
      var enclosingClass = decl.EnclosingClass;
      fullCompiledName = $"{enclosingClass.CompileName}.{fullCompiledName}";
      var m = enclosingClass.EnclosingModuleDefinition;
      while (!m.IsDefaultModule) {
        if (Attributes.Contains(m.Attributes, "extern") &&
            Attributes.FindExpressions(m.Attributes, "extern").Count > 0) {
          fullCompiledName = $"{Printer.ExprToString(m.Attributes.Args[0]).Trim('"')}.{fullCompiledName}";
          break;
        }
        fullCompiledName = $"{m.CompileName}_Compile.{fullCompiledName}";
        m = m.EnclosingModule;
      }
      return fullCompiledName;
    }

    public IList<Type> GetReturnTypes(string callable) {
      if (methods.ContainsKey(callable)) {
        return methods[callable].Outs.Select(arg =>
          Utils.UseFullName(arg.Type)).ToList(); ;
      }
      if (functions.ContainsKey(callable)) {
        return new List<Type>
          { Utils.UseFullName(functions[callable].ResultType) };
      }
      throw new Exception("Cannot identify callable " + callable);
    }

    public List<TypeParameter> GetTypeArgs(string callable) {
      if (methods.ContainsKey(callable)) {
        return methods[callable].TypeArgs;
      }
      if (functions.ContainsKey(callable)) {
        return functions[callable].TypeArgs;
      }
      throw new Exception("Cannot identify callable " + callable);
    }

    public List<TypeParameter> GetTypeArgsWithParents(string callable) {
      List<TypeParameter> result = new List<TypeParameter>();
      TopLevelDecl/*?*/ clazz;
      if (methods.ContainsKey(callable)) {
        result.AddRange(methods[callable].TypeArgs);
        clazz = methods[callable].EnclosingClass;
      } else if (functions.ContainsKey(callable)) {
        result.AddRange(functions[callable].TypeArgs);
        clazz = functions[callable].EnclosingClass;
      } else {
        throw new Exception("Cannot identify callable " + callable);
      }
      result.AddRange(clazz.TypeArgs);
      return result;
    }

    public IList<Type> GetFormalsTypes(string callable) {
      if (methods.ContainsKey(callable)) {
        return methods[callable].Ins.Select(arg =>
          Utils.UseFullName(arg.Type)).ToList(); ;
      }
      if (functions.ContainsKey(callable)) {
        return functions[callable].Formals.Select(arg =>
          Utils.UseFullName(arg.Type)).ToList(); ;
      }
      throw new Exception("Cannot identify callable " + callable);
    }

    public bool IsStatic(string callable) {
      if (methods.ContainsKey(callable)) {
        return methods[callable].IsStatic;
      }
      if (functions.ContainsKey(callable)) {
        return functions[callable].IsStatic;
      }
      throw new Exception("Cannot identify callable " + callable);
    }

    public bool IsGhost(string callable) {
      if (methods.ContainsKey(callable)) {
        return methods[callable].IsGhost || methods[callable].IsLemmaLike;
      }
      if (functions.ContainsKey(callable)) {
        return functions[callable].IsGhost;
      }
      return true;
    }

    public bool IsAccessible(string callable) {
      if (methods.ContainsKey(callable)) {
        return scopes.Any(scope => methods[callable].IsVisibleInScope(scope));
      }
      if (functions.ContainsKey(callable)) {
        return scopes.Any(scope => functions[callable].IsVisibleInScope(scope));
      }
      return false;
    }

    public string/*?*/ GetWitnessForType(Type type) {
      if (type is not UserDefinedType userDefinedType ||
          !witnessForType.ContainsKey(userDefinedType.Name)) {
        return null;
      }

      return Printer.ExprToString(
        new ClonerWithSubstitution(this, new Dictionary<IVariable, string>(),
          "").CloneExpr(witnessForType[userDefinedType.Name]));
    }

    public Type/*?*/ GetSupersetType(Type type) {
      if (type is not UserDefinedType userDefinedType ||
          !subsetToSuperset.ContainsKey(userDefinedType.Name)) {
        return null;
      }
      var superSetType = subsetToSuperset[userDefinedType.Name].superset;
      var typeArgs = subsetToSuperset[userDefinedType.Name].args;
      superSetType = Utils.CopyWithReplacements(superSetType,
        typeArgs.ConvertAll(arg => arg.Name), type.TypeArgs);
      if ((superSetType is UserDefinedType tmp) &&
          tmp.Name.StartsWith("_System") &&
           subsetToSuperset.ContainsKey(tmp.Name)) {
        return subsetToSuperset[tmp.Name].superset;
      }
      return superSetType;
    }

    public IEnumerable<Expression> GetEnsures(List<string> ins, List<string> outs, string callableName, string receiver) {
      Dictionary<IVariable, string> subst = new Dictionary<IVariable, string>();
      if (methods.ContainsKey(callableName)) {
        for (int i = 0; i < methods[callableName].Ins.Count; i++) {
          subst[methods[callableName].Ins[i]] = ins[i];
        }
        for (int i = 0; i < methods[callableName].Outs.Count; i++) {
          subst[methods[callableName].Outs[i]] = outs[i];
        }
        return methods[callableName].Ens.Select(e =>
            new ClonerWithSubstitution(this, subst, receiver).CloneValidOrNull(e.E))
          .Where(e => e != null);
      }
      if (functions.ContainsKey(callableName)) {
        for (int i = 0; i < functions[callableName].Formals.Count; i++) {
          subst[functions[callableName].Formals[i]] = ins[i];
        }

        if (functions[callableName].Result != null) {
          subst[functions[callableName].Result] = outs[0];
        }

        return functions[callableName].Ens.Select(e =>
            new ClonerWithSubstitution(this, subst, receiver).CloneValidOrNull(e.E))
          .Where(e => e != null);
      }
      throw new Exception("Cannot identify callable " + callableName);
    }

    public IEnumerable<Expression> GetRequires(List<string> ins, string callableName, string receiver) {
      Dictionary<IVariable, string> subst = new Dictionary<IVariable, string>();
      if (methods.ContainsKey(callableName)) {
        for (int i = 0; i < methods[callableName].Ins.Count; i++) {
          subst[methods[callableName].Ins[i]] = ins[i];
        }
        return methods[callableName].Req.Select(e =>
            new ClonerWithSubstitution(this, subst, receiver).CloneValidOrNull(e.E))
          .Where(e => e != null);
      }
      if (functions.ContainsKey(callableName)) {
        for (int i = 0; i < functions[callableName].Formals.Count; i++) {
          subst[functions[callableName].Formals[i]] = ins[i];
        }
        return functions[callableName].Req.Select(e =>
            new ClonerWithSubstitution(this, subst, receiver).CloneValidOrNull(e.E))
          .Where(e => e != null);
      }
      throw new Exception("Cannot identify callable " + callableName);
    }

    public Expression/*?*/ GetTypeCondition(Type type, string name) {
      if (type is not UserDefinedType userDefinedType ||
          !conditionForType.ContainsKey(userDefinedType.Name)) {
        return null;
      }
      Dictionary<IVariable, string> subst = new Dictionary<IVariable, string>();
      subst[conditionForType[userDefinedType.Name].variable] = name;
      var condition = conditionForType[userDefinedType.Name].expr;
      return new ClonerWithSubstitution(this, subst, name).CloneValidOrNull(condition);
    }

    public List<(string name, Type type, bool mutable, string/*?*/ defValue)> GetNonGhostFields(UserDefinedType/*?*/ type) {
      if (type == null || !Classes.ContainsKey(type.Name)) {
        throw new Exception("Cannot identify class " + type?.Name ??
                            " (null) ");
      }

      var relevantFields = Classes[type.Name].Members.OfType<Field>()
        .Where(field => !field.IsGhost);
      var result = new List<(string name, Type type, bool mutable, string defValue)>();
      foreach (var field in relevantFields) {
        string/*?*/ defValue = null;
        if (field is ConstantField constantField && constantField.Rhs != null) {
          var defExpression = new ClonerWithSubstitution(
            this,
            new Dictionary<IVariable, string>(),
            "").CloneExpr(constantField.Rhs);
          if (defExpression != null) {
            defValue = Printer.ExprToString(defExpression);
          }
        }
        var fieldType = Utils.CopyWithReplacements(
          Utils.UseFullName(field.Type),
          Classes[type.Name].TypeArgs.ConvertAll(arg => arg.ToString()),
          type.TypeArgs);
        result.Add(new(field.Name, fieldType, field.IsMutable, defValue));
      }
      return result;
    }

    public bool IsTrait(UserDefinedType/*?*/ type) {
      if (type == null || !Classes.ContainsKey(type.Name)) {
        throw new Exception("Cannot identify class " + type?.Name ??
                            " (null) ");
      }
      return Classes[type.Name] is TraitDecl;
    }

    public List<Type>/*?*/ GetTypesForTrait(UserDefinedType/*?*/ type) {
      if (!IsTrait(type) || Classes[type.Name] is not TraitDecl traitDecl) {
        return null;
      }
      var result = new List<Type>();
      foreach (var member in traitDecl.Members) {
        switch (member) {
          case Function function when !function.IsGhost:
            var resultType = Utils.CopyWithReplacements(
              Utils.UseFullName(function.ResultType),
              traitDecl.TypeArgs.ConvertAll(arg => arg.ToString()),
              type.TypeArgs); ;
            if (resultType.ToString() != type.ToString() && !result.Any(type =>
                  type.ToString() == resultType.ToString()) && !resultType.ToString().Contains("_tuple")) {
              result.Add(resultType);
            }
            break;
        }
      }
      return result;
    }

    public List<string> GetEnsuresForTrait(UserDefinedType/*?*/ type, string name, Dictionary<string, string> arguments) {
      var result = new List<string>();
      var traitDecl = (TraitDecl)Classes[type.Name];
      foreach (var member in traitDecl.Members) {
        switch (member) {
          case Function function when !function.IsGhost:
            var resultType = Utils.CopyWithReplacements(
              Utils.UseFullName(function.ResultType),
              traitDecl.TypeArgs.ConvertAll(arg => arg.ToString()),
              type.TypeArgs);
            if (resultType.ToString().Contains("_tuple")) {
              continue;
            }
            var inputTypes = function.Formals.ConvertAll(formal =>
              Utils.CopyWithReplacements(
                Utils.UseFullName(formal.Type),
                traitDecl.TypeArgs.ConvertAll(arg => arg.ToString()),
                type.TypeArgs));
            var id = 0;
            var inputIds = function.Formals.ConvertAll(_ => name + "_arg" + id++);
            var inputs = Enumerable.Zip(inputIds, inputTypes);
            result.Add($"ensures forall " +
                       $"{string.Join(",", inputs.Select(formal => formal.First + ":" + formal.Second))} ::" +
                       $"{name}.{function.Name}" +
                       $"({String.Join(",", inputIds)}) == " +
                       $"{arguments[resultType.ToString()]}");
            break;
        }
      }
      return result;
    }
    public bool IsExtern(UserDefinedType/*?*/ type) {
      if (type == null || !Classes.ContainsKey(type.Name)) {
        throw new Exception("Cannot identify class " + type?.Name ??
                            " (null) ");
      }
      string qualification, name;
      return Classes[type.Name].IsExtern(out qualification, out name);
    }

    public Constructor/*?*/ GetConstructor(UserDefinedType/*?*/ type) {
      if (type == null || !Classes.ContainsKey(type.Name)) {
        throw new Exception("Cannot identify class " + type?.Name ??
                            " (null) ");
      }
      return Classes[type.Name].Members.OfType<Constructor>()
        .OrderBy(constructor => constructor.Ins.Count())
        .FirstOrDefault((Constructor/*?*/)null);
    }

    /// <summary>
    /// Fills in the Dafny Info data by traversing the AST
    /// </summary>
    private class DafnyInfoExtractor : BottomUpVisitor {

      private readonly DafnyInfo info;

      internal DafnyInfoExtractor(DafnyInfo info) {
        this.info = info;
      }

      internal void Visit(Program p) {
        Visit(p.DefaultModule);
      }

      private void Visit(TopLevelDecl d) {
        if (d is LiteralModuleDecl moduleDecl) {
          Visit(moduleDecl);
        } else if (d is ClassDecl classDecl) {
          Visit(classDecl);
        } else if (d is IndDatatypeDecl datatypeDecl) {
          Visit(datatypeDecl);
        } else if (d is NewtypeDecl newTypeDecl) {
          Visit(newTypeDecl);
        } else if (d is SubsetTypeDecl subsetTypeDecl) {
          Visit(subsetTypeDecl);
        } else if (d is TypeSynonymDeclBase typeSynonymDecl) {
          Visit(typeSynonymDecl);
        }
      }

      private void VisitUserDefinedTypeDeclaration(string newTypeName,
        Type baseType, Expression/*?*/ witness, List<TypeParameter> typeArgs) {
        if (witness != null) {
          info.witnessForType[newTypeName] = witness;
          if (DafnyOptions.O.TestGenOptions.Verbose) {
            Console.Out.WriteLine($"// Values of type {newTypeName} will be " +
                                  $"assigned the default value of " +
                                  $"{Printer.ExprToString(info.witnessForType[newTypeName])}");
          }
        } else if (DafnyOptions.O.TestGenOptions.Verbose) {
          Console.Out.WriteLine($"// Warning: Values of type {newTypeName} " +
                                $"will be assigned a default value of type " +
                                $"{baseType}, which may or may not match the " +
                                $"associated condition");
        }
        info.subsetToSuperset[newTypeName] = (typeArgs,
          Utils.UseFullName(baseType));
      }

      private new void Visit(SubsetTypeDecl newType) {
        var name = newType.FullDafnyName;
        var type = newType.Rhs;
        while (type is InferredTypeProxy inferred) {
          type = inferred.T;
        }
        info.conditionForType[name] = new(newType.Var, newType.Constraint);
        VisitUserDefinedTypeDeclaration(name, type, newType.Witness,
          newType.TypeArgs);
      }

      private new void Visit(NewtypeDecl newType) {
        var name = newType.FullDafnyName;
        var type = newType.BaseType;
        while (type is InferredTypeProxy inferred) {
          type = inferred.T;
        }
        info.conditionForType[name] = new(newType.Var, newType.Constraint);
        VisitUserDefinedTypeDeclaration(name, type, newType.Witness,
          newType.TypeArgs);
      }

      private void Visit(TypeSynonymDeclBase newType) {
        var name = newType.FullDafnyName;
        var type = newType.Rhs;
        while (type is InferredTypeProxy inferred) {
          type = inferred.T;
        }
        VisitUserDefinedTypeDeclaration(name, type, null, newType.TypeArgs);
      }

      private void Visit(LiteralModuleDecl d) {
        if (d.ModuleDef.IsAbstract) {
          return;
        }
        if (info.ToImportAs.ContainsValue(d.Name)) {
          var id = info.ToImportAs.Values.Count(v => v.StartsWith(d.Name));
          info.ToImportAs[d.FullDafnyName] = d.Name + id;
        } else if (d.FullDafnyName != "") {
          info.ToImportAs[d.FullDafnyName] = d.Name;
        }
        d.ModuleDef.TopLevelDecls.ForEach(Visit);
      }

      private void Visit(IndDatatypeDecl d) {
        info.Datatypes[d.FullDafnyName] = d;
        info.Datatypes[d.FullSanitizedName] = d;
        d.Members.ForEach(Visit);
      }

      private void Visit(ClassDecl d) {
        info.Classes[d.FullDafnyName] = d;
        info.Classes[d.FullSanitizedName] = d;
        d.Members.ForEach(Visit);
      }

      private void Visit(MemberDecl d) {
        if (d is Method method) {
          Visit(method);
        } else if (d is Function function) {
          Visit(function);
        }
      }

      private new void Visit(Method m) {
        info.methods[m.FullDafnyName] = m;
      }

      private new void Visit(Function f) {
        info.functions[f.FullDafnyName] = f;
      }
    }

    private class ClonerWithSubstitution : Cloner {

      private Dictionary<IVariable, string> subst;
      private bool isValidExpression;
      private string receiver;
      private DafnyInfo dafnyInfo;
      public ClonerWithSubstitution(DafnyInfo dafnyInfo, Dictionary<IVariable, string> subst, string receiver) {
        this.subst = subst;
        this.receiver = receiver;
        this.dafnyInfo = dafnyInfo;
        isValidExpression = true;
      }

      public override Type CloneType(Type type) {
        // TODO: type arguments
        if (type is UserDefinedType userDefinedType) {
          var name = userDefinedType?.ResolvedClass?.FullName ??
                     userDefinedType.Name;
          if (name.StartsWith("_System.")) {
            name = name[8..];
          }
          return new UserDefinedType(new Token(), name,
            type.TypeArgs.ConvertAll(CloneType));
        }
        return base.CloneType(type);
      }

      public override Expression CloneExpr(Expression expr) {
        if (expr == null) {
          return null;
        }
        switch (expr) {
          case ImplicitThisExpr_ConstructorCall:
            isValidExpression = false;
            return base.CloneExpr(expr);
          case ThisExpr:
            return new IdentifierExpr(expr.tok, receiver);
          case AutoGhostIdentifierExpr:
            isValidExpression = false;
            return base.CloneExpr(expr);
          case ExprDotName or NameSegment or ApplySuffix: {
              if (!expr.WasResolved()) {
                isValidExpression = false;
                return base.CloneExpr(expr);
              }
              if (expr.Resolved is IdentifierExpr or MemberSelectExpr or DatatypeValue) {
                return CloneExpr(expr.Resolved);
              }
              return base.CloneExpr(expr);
            }
          case DatatypeValue datatypeValue:
            if (datatypeValue.Type is UserDefinedType udt &&
                udt.ResolvedClass != null) {
              var actualBindings = datatypeValue.Bindings.ArgumentBindings.ConvertAll(
                  base.CloneActualBinding);
              var newValue = new DatatypeValue(new Token(),
                udt.ResolvedClass.FullDafnyName, datatypeValue.MemberName,
                actualBindings);
              newValue.Type = Utils.UseFullName(datatypeValue.Type);
              newValue.InferredTypeArgs = datatypeValue.InferredTypeArgs.ConvertAll(typ => Utils.UseFullName(typ));
              newValue.Bindings.arguments =
                actualBindings.ConvertAll(binding => binding.Actual);
              return newValue;
            }
            isValidExpression = false;
            return base.CloneExpr(expr);
          case IdentifierExpr identifierExpr: {
              if ((identifierExpr.Var != null) && identifierExpr.Var.IsGhost) {
                isValidExpression = false;
                return base.CloneExpr(expr);
              }
              if ((identifierExpr.Var != null) &&
                  subst.ContainsKey(identifierExpr.Var)) {
                return new IdentifierExpr(expr.tok, subst[identifierExpr.Var]);
              }
              return base.CloneExpr(expr);
            }
          case MemberSelectExpr memberSelectExpr: {
              if (memberSelectExpr.Member.IsGhost ||
                  dafnyInfo.scopes.All(scope => !memberSelectExpr.Member.IsVisibleInScope(scope))) {
                isValidExpression = false;
                return base.CloneExpr(expr);
              }
              if (memberSelectExpr.Obj is StaticReceiverExpr staticReceiverExpr) {
                return new IdentifierExpr(expr.tok,
                  ((staticReceiverExpr.Type) as UserDefinedType).ResolvedClass
                  .FullDafnyName + "." + memberSelectExpr.MemberName);
              }
              return base.CloneExpr(expr);
            }
          case OldExpr or UnchangedExpr or FreshExpr or LetExpr or
            LetOrFailExpr or ComprehensionExpr or WildcardExpr or StmtExpr:
            isValidExpression = false;
            return base.CloneExpr(expr);
          default:
            return base.CloneExpr(expr);
        }
      }
      public Expression/*?*/ CloneValidOrNull(Expression expr) {
        var result = CloneExpr(expr);
        return isValidExpression ? result : null;
      }
    }
  }
}