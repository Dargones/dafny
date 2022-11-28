#nullable disable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text.RegularExpressions;
using DafnyServer.CounterexampleGeneration;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.CounterExampleGeneration;
using Formal = Microsoft.Dafny.Formal;
using LambdaExpr = Microsoft.Dafny.LambdaExpr;
using LiteralExpr = Microsoft.Dafny.LiteralExpr;
using IdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using MapType = Microsoft.Dafny.MapType;
using Token = Microsoft.Dafny.Token;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  /// <summary> Allows converting a counterexample to a test method </summary>
  public class TestMethod {
    
    private static int nextId; // next unique id to be assigned
    private Method method; // AST of the test method
    // list of values to mock together with their types
    // maps a variable that is mocked to its unique id
    private readonly Dictionary<DafnyModelVariable, Expression> mockedVarId = new();
    private int nextValueId = 0;
    private readonly int id = nextId++;
    public readonly DafnyInfo DafnyInfo;
    // name of the method for which the counterexample is generated
    public readonly string MethodName;
    // default type to replace any type variable with
    private readonly Type defaultType = Type.Int;
    // the DafnyModel that describes the inputs to this test method
    private readonly DafnyModel dafnyModel;
    // Set of all types for which a {:synthesize} - annotated method is needed
    // These methods are used to get fresh instances of the corresponding types
    private static readonly Dictionary<string, UserDefinedType> TypesToSynthesize = new();
    // is set to true whenever the tool encounters something it does not support
    private readonly List<string> errorMessages = new();
    // records parameters for GetDefaultValue call - this is used to to
    // terminate potential infinite recursion
    private List<string> getDefaultValueParams = new();
    // similar to above but for objects
    private readonly HashSet<string> getClassTypeInstanceParams = new();
    private Dictionary<string, Expression> defaultValueForType = new();

    public TestMethod(DafnyInfo dafnyInfo, string log) {
      DafnyInfo = dafnyInfo;
      var typeNames = ExtractPrintedInfo(log, "Types | ");
      var argumentNames = ExtractPrintedInfo(log, "Impl | ");
      dafnyModel = DafnyModel.ExtractModel(log);
      MethodName = argumentNames.First();
      argumentNames.RemoveAt(0);
      method = new Method(new Token(), "test" + id, true, false,
        new List<TypeParameter>(), new List<Formal>(), new List<Formal>(),
        new List<AttributedExpression>(), new Specification<FrameExpression>(new List<FrameExpression>(), null),
        new List<AttributedExpression>(), new Specification<Expression>(new List<Expression>(), null),
        new BlockStmt(new Token(), new Token(), new List<Statement>()),
        new Attributes("test", new List<Expression>(), null), new Token(),
        false);
      var NOfTypeArgs = dafnyInfo.GetTypeArgs(MethodName).Count;
      ArgValues = ExtractInputs(dafnyModel.States.First(), argumentNames, typeNames);
      // TODO: populate method call and preconditions here
    }

    public bool IsValid => errorMessages.Count == 0;

    public static void ClearTypesToSynthesize() {
      TypesToSynthesize.Clear();
    }

    /// <summary>
    /// Returns the name given to a {:synthesize} - annotated method that
    /// returns a value of certain type
    /// </summary>
    private static string GetSynthesizeMethodName(string typ) {
      return "getFresh" + Regex.Replace(typ, "[^a-zA-Z]", "");
    }

    /// <summary>
    /// Returns a string that contains all the {:synthesize} annotated methods
    /// necessary to compile the tests
    /// </summary>
    public static string EmitSynthesizeMethods(DafnyInfo dafnyInfo) {
      var result = "";
      foreach (var typ in TypesToSynthesize.Keys) {
        var methodName = GetSynthesizeMethodName(typ);
        var returnName = "o";
        if (dafnyInfo.IsTrait(TypesToSynthesize[typ])) {
          var types = dafnyInfo.GetTypesForTrait(TypesToSynthesize[typ]);
          int id = 0;
          var typeToNameDict = new Dictionary<string, string>();
          foreach (var resultTyp in types) {
            typeToNameDict[resultTyp.ToString()] = "o_res_" + id++;
          }
          typeToNameDict[typ] = "o";
          result += $"\nmethod {{:synthesize}} {methodName}(" +
                    $"{string.Join(",", types.ConvertAll(t => $"{typeToNameDict[t.ToString()]}:{t}"))})" +
                    $"returns ({returnName}:{typ}) ensures fresh({returnName}) " +
                    $"{string.Join(" ", dafnyInfo.GetEnsuresForTrait(TypesToSynthesize[typ], returnName, typeToNameDict))}";
        } else {
          var constFields = dafnyInfo.GetNonGhostFields(TypesToSynthesize[typ])
            .Where(field => !field.mutable).ToList();
          while (constFields.Any(field => field.name == returnName)) {
            returnName += "o";
          }

          var parameters = string.Join(", ",
            constFields.Select(field => $"{field.name}:{field.type}"));
          var ensures = string.Join(" ",
            constFields.Select(field =>
              $"ensures {returnName}.{field.name}=={field.name}"));
          result += $"\nmethod {{:synthesize}} {methodName}({parameters}) " +
                    $"returns ({returnName}:{typ}) ensures fresh({returnName}) " +
                    $"{ensures}";
        }
      }
      return result;
    }

    /// <summary>
    /// Extract values that certain elements have at a certain state in the
    /// model.
    /// </summary>
    /// <param name="state"> DafnyModelState to work with</param>
    /// <param name="printOutput"> Output of print command for each element.
    /// This can either be a value of a basic type ("1.0", "false", etc.),
    /// a reference to an element ("T@U!val!25", etc.) or an empty string,
    /// which means that one has to come up with a value based on its
    /// type alone </param>
    /// <param name="types">the types of the elements</param>
    /// <returns></returns>
    private List<Expression> ExtractInputs(DafnyModelState state, IReadOnlyList<string> printOutput, IReadOnlyList<string> types) {
      var result = new List<string>();
      var vars = state.ExpandedVariableSet(-1);
      var parameterIndex = DafnyInfo.IsStatic(MethodName) ? -1 : -2;
      for (var i = 0; i < printOutput.Count; i++) {
        if (types[i] == "Ty") {
          continue; // this means that this parameter is a type variable
        }
        parameterIndex++;
        Type type;
        if (parameterIndex >= 0) {
          type = Utils.UseFullName(
            DafnyInfo.GetFormalsTypes(MethodName)[parameterIndex]);
          type = Utils.CopyWithReplacements(type,
            DafnyInfo.GetTypeArgsWithParents(MethodName).ConvertAll(arg => arg.ToString()),
            Enumerable.Repeat(defaultType, DafnyInfo.GetTypeArgsWithParents(MethodName).Count).ToList());
          type = DafnyModelTypeUtils.ReplaceType(type,
            _ => true,
            type => DafnyInfo.GetSupersetType(type) != null && type.Name.StartsWith("_System") ?
              new UserDefinedType(type.tok, type.Name[8..], type.TypeArgs) :
              new UserDefinedType(type.tok, type.Name, type.TypeArgs));
        } else {
          type = null;
        }
        if (printOutput[i] == "") {
          getDefaultValueParams = new();
          var value = GetDefaultValue(type, type);
          if (value == null) {
            return null;
          }
          result.Add(value);
          continue;
        }
        if (!printOutput[i].StartsWith("T@")) {
          string baseValue;
          if (Regex.IsMatch(printOutput[i], "^[0-9]+bv[0-9]+$")) {
            var baseIndex = printOutput[i].IndexOf('b');
            baseValue = $"({printOutput[i][..baseIndex]} as {printOutput[i][baseIndex..]})";
          } else {
            baseValue = printOutput[i];
          }
          result.Add(GetPrimitiveAsType(baseValue, type));
          continue;
        }
        foreach (var variable in vars) {
          if ((variable.Element as Model.Uninterpreted)?.Name != printOutput[i]) {
            continue;
          }
          result.Add(ExtractVariable(variable, type));
          break;
        }
      }
      return result;
    }

    // Returns a new value of the defaultType type (set to int by default)
    private Expression GetADefaultTypeValue(DafnyModelVariable variable) {
      return dafnyModel.GetUnreservedNumericValue(variable.Element, Type.Int);
    }

    private LambdaExpr GetFunctionOfType(ArrowType type) {
      type = (ArrowType)DafnyModelTypeUtils.ReplaceTypeVariables(type, defaultType);
      getDefaultValueParams = new();
      var returnValue = GetDefaultValue(type.TypeArgs.Last());
      if (returnValue == null) {
        return null;
      }
      return new LambdaExpr(new Token(), new Token(), 
        type.TypeArgs.SkipLast(1).Select((t, i) => new BoundVar(new Token(), "a" + i, t)).ToList(), 
        null, null, returnValue);
    }

    /// <summary>
    /// Try to reduce the type from a synonym down to superset type until
    /// a certain condition is met
    /// </summary>
    private Type GetBasicType(Type start, Func<Type, bool> stopCondition) {
      if (!stopCondition(start) &&
             DafnyInfo.GetSupersetType(start) != null) {
        return GetBasicType(
          DafnyInfo.GetSupersetType(start),
          stopCondition);
      }
      return start;
    }

    /// <summary>
    /// Extract the value of a variable. This can have side-effects on
    /// assignments, reservedValues, reservedValuesMap, and objectsToMock.
    /// </summary>
    private Expression ExtractVariable(DafnyModelVariable variable, Type/*?*/ asType) {
      if (variable == null) {
        if (asType != null) {
          return GetDefaultValue(asType);
        } else {
          errorMessages.Add("// Failed: variable and type are null");
          return null;
        }
      }
      if (asType != null) {
        asType = DafnyModelTypeUtils.ReplaceType(asType,
          type => DafnyInfo.GetSupersetType(type) != null &&
                  type.Name.StartsWith("_System"),
          type => new UserDefinedType(type.tok, type.Name[8..], type.TypeArgs));
      }
      if (mockedVarId.ContainsKey(variable)) {
        return mockedVarId[variable];
      }

      if (variable is DuplicateVariable duplicateVariable) {
        return ExtractVariable(duplicateVariable.Original, asType);
      }

      if (variable.Type.ToString().Contains("_System.Tuple") ||
          (asType?.ToString() ?? "").Contains("_System.Tuple")) {
        errorMessages.Add("// Failed - temporary disable tuple support");
        return null;
      }

      List<Expression> elements = new();
      var variableType = DafnyModelTypeUtils.GetInDafnyFormat(
        DafnyModelTypeUtils.ReplaceTypeVariables(variable.Type, defaultType));
      variableType = DafnyModelTypeUtils.ReplaceType(variableType,
        type => DafnyInfo.GetSupersetType(type) != null &&
                type.Name.StartsWith("_System"),
        type => new UserDefinedType(type.tok, type.Name[8..], type.TypeArgs));
      if (variableType.ToString() == defaultType.ToString() &&
          variableType.ToString() != variable.Type.ToString()) {
        return GetADefaultTypeValue(variable);
      }
      switch (variableType) {
        case IntType:
        case RealType:
        case BoolType:
        case CharType:
        case BitvectorType:
          return new ConversionExpr(new Token(), new LiteralExpr(new Token(), BigInteger.Parse(variable.Value)), variableType);
        case SeqType seqType:
          var asBasicSeqType = GetBasicType(asType, type => type is SeqType) as SeqType;
          string seqName;
          var seqVar = variable as SeqVariable;
          if (seqVar?.GetLength() == -1) {
            return GetDefaultValue(seqType, seqType);
          }
          for (var i = 0; i < seqVar?.GetLength(); i++) {
            var elementVar = seqVar?[i];
            Expression element;
            if (elementVar == null) {
              getDefaultValueParams = new();
              element = GetDefaultValue(seqType.Arg,
                asBasicSeqType?.TypeArgs?.FirstOrDefault((Type /*?*/)null));
            } else {
              element = ExtractVariable(elementVar,
                asBasicSeqType?.TypeArgs?.FirstOrDefault((Type /*?*/)null));
            }
            if (element == null) {
              return null;
            }
            elements.Add(element);
          }
          seqName = "d" + nextValueId++;

          //
          // Work around stack overflow issue that can occur in Dafny when trying to construct large strings.
          // Only apply this for strings i.e. sequences of characters.
          //
          const int chunksize = 100;
          if (seqType.Arg is CharType && elements.Count > chunksize) {
            int i = 0;
            var chunkStrs = new List<string>();
            while (i < elements.Count) {
              int count = Math.Min(chunksize, elements.Count - i);
              string chunk = "\"" + string.Join("", elements.GetRange(i, count)).Replace("'", "") + "\"";
              chunkStrs.Add(chunk);
              i += chunksize;
            }
            return string.Join("+", chunkStrs);
          }


          ValueCreation.Add(seqType.Arg is CharType
            ? (seqName, asType ?? variableType, $"\"{string.Join("", elements.SelectMany(c => c[1..^1]))}\"")
            : (seqName, asType ?? variableType, $"[{string.Join(", ", elements)}]"));
          return seqName;
        case SetType setType:
          var asBasicSetType = GetBasicType(asType, type => type is SetType) as SetType;
          string setName;
          foreach (var element in variable.Children["true"]) {
            elements.Add(ExtractVariable(element, asBasicSetType?.TypeArgs?.FirstOrDefault((Type/*?*/)null)));
          }
          setName = "d" + nextValueId++;
          // TODO: case as type?
          method.Body.AppendStmt(Statement.CreateLocalVariable(new Token(),
            setName, 
            new SetDisplayExpr(new Token(), setType.Finite, elements)));
          return new IdentifierExpr(new Token(), setName);
        case MapType:
          var asBasicMapType = GetBasicType(asType, type => type is MapType) as MapType;
          var mapVar = variable as MapVariable;
          List<string> mappingStrings = new();
          foreach (var mapping in mapVar?.Mappings ?? new()) {
            var asTypeTypeArgs =
              asBasicMapType?.TypeArgs?.Count == 2 ? asBasicMapType.TypeArgs : null;
            mappingStrings.Add($"{ExtractVariable(mapping.Key, asTypeTypeArgs?[0])} := {ExtractVariable(mapping.Value, asTypeTypeArgs?[1])}");
          }
          var mapName = "d" + nextValueId++;
          ValueCreation.Add((mapName, asType ?? variableType, $"map[{string.Join(", ", mappingStrings)}]"));
          return mapName;
        case UserDefinedType tupleType when tupleType.Name.StartsWith("_System.Tuple") || tupleType.Name.StartsWith("_System._tuple"):
          errorMessages.Add("// Failed - temporary disable datatype support");
          var tupleName = "d" + nextValueId++;
          ValueCreation.Add((tupleName, DafnyModel.UnknownType, "(" +
            string.Join(",", variable.Children.Values
            .Select(v => ExtractVariable(v.First(), null))) + ")"));
          return tupleName;
        case DafnyModelTypeUtils.DatatypeType dataType:
          if (variable.CanonicalName() == "") {
            getDefaultValueParams = new();
            return GetDefaultValue(dataType, asType);
          }

          var basicType = GetBasicType(asType ?? dataType,
            type => type == null || type is not UserDefinedType definedType ||
                    DafnyInfo.Datatypes.ContainsKey(definedType
                      .Name)) as UserDefinedType;
          if (basicType == null ||
              !DafnyInfo.Datatypes.ContainsKey(basicType.Name)) {
            errorMessages.Add($"// Failed: Cannot find datatype {dataType} in DafnyInfo");
            return dataType.ToString();
          }
          var ctor = DafnyInfo.Datatypes[basicType.Name].Ctors.FirstOrDefault(ctor => ctor.Name == variable.CanonicalName(), null);
          if (ctor == null) {
            errorMessages.Add($"// Failed: Cannot find constructor {variable.CanonicalName()} for datatype {basicType}");
            return basicType.ToString();
          }
          List<string> fields = new();
          for (int i = 0; i < ctor.Destructors.Count; i++) {
            var fieldName = ctor.Destructors[i].Name;
            if (!variable.Children.ContainsKey(fieldName)) {
              fieldName = $"[{i}]";
            }

            if (!variable.Children.ContainsKey(fieldName)) {
              errorMessages.Add($"// Failed: Cannot find destructor " +
                                $"{ctor.Destructors[i].Name} of constructor " +
                                $"{variable.CanonicalName()} for datatype " +
                                $"{basicType}");
              return basicType.ToString();
            }

            var destructorType = Utils.CopyWithReplacements(
              Utils.UseFullName(ctor.Destructors[i].Type),
              ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), basicType.TypeArgs);
            destructorType = DafnyModelTypeUtils.ReplaceType(destructorType,
              _ => true,
              t => DafnyInfo.Datatypes.ContainsKey(t.Name)
                ? new DafnyModelTypeUtils.DatatypeType(t)
                : new UserDefinedType(t.tok, t.Name, t.TypeArgs));
            fields.Add(ctor.Destructors[i].Name + ":=" +
                       ExtractVariable(variable.Children[fieldName].First(), destructorType));
          }

          var value = basicType.ToString();
          if (fields.Count == 0) {
            value += "." + variable.CanonicalName();
          } else {
            value += "." + variable.CanonicalName() + "(" +
                     string.Join(",", fields) + ")";
          }
          var name = "d" + nextValueId++;
          ValueCreation.Add((name, asType ?? dataType, value));
          return name;
        case ArrowType arrowType:
          var asBasicArrowType = GetBasicType(asType, type => type is ArrowType) as ArrowType;
          return GetFunctionOfType(asBasicArrowType ?? arrowType);
        case UserDefinedType unknown when unknown.Name == DafnyModel.UnknownType.Name:
          if (asType != null) {
            return GetDefaultValue(asType, asType);
          }
          errorMessages.Add($"// Failed to determine a variable type (element {variable.Element}).");
          return null;
        case UserDefinedType arrType when new Regex("^_System.array[0-9]*\\?$").IsMatch(arrType.Name):
          errorMessages.Add($"// Failed because arrays are not yet supported (type {arrType} element {variable.Element})");
          break;
        case UserDefinedType _ when variable.CanonicalName() == "null":
          return new LiteralExpr(new Token());
        case UserDefinedType userDefinedType:
          return GetClassTypeInstance(userDefinedType, asType, variable);
      }
      errorMessages.Add($"// Failed because variable has unknown type {variableType} (element {variable.Element})");
      return null;
    }

    private Expression GetTraitTypeInstance(UserDefinedType type) {
      var typesToInitialize = DafnyInfo.GetTypesForTrait(type);
      foreach (var typ in typesToInitialize) {
        var value = GetDefaultValue(typ, typ);
        if (value == null) {
          return null;
        }
        defaultValueForType[typ.ToString()] = value;
      }
      var varId = new IdentifierExpr(new Token(), $"v{nextValueId++}");
      method.Body.AppendStmt(new AssignStmt(new Token(), new Token(), varId,
        new ExprRhs(new FunctionCallExpr(new Token(), 
          GetSynthesizeMethodName(type.ToString()), 
          new ImplicitThisExpr(new Token()), 
          new Token(), new Token(), 
          typesToInitialize.ConvertAll(typ => defaultValueForType[typ.ToString()])))));
      TypesToSynthesize[type.ToString()] = type;
      return varId;
    }

    private Expression GetClassTypeInstance(UserDefinedType type, Type/*?*/ asType, DafnyModelVariable/*?*/ variable) {
      var asBasicType = GetBasicType(asType, _ => false);
      if ((asBasicType != null) && (asBasicType is not UserDefinedType)) {
        return GetDefaultValue(asType, asType);
      }
      var dafnyType = DafnyModelTypeUtils.GetNonNullable(asBasicType ?? type) as UserDefinedType;
      if (getClassTypeInstanceParams.Contains(dafnyType.ToString())) {
        errorMessages.Add(
          $"// Failed to find a non-recursive way of constructing value (type {dafnyType})");
        return null;
      }
      getClassTypeInstanceParams.Add(dafnyType.ToString());
      if (DafnyInfo.IsTrait(dafnyType)) {
        var tmp = GetTraitTypeInstance(dafnyType);
        if (tmp == null) {
          return null;
        }
        getClassTypeInstanceParams.Remove(dafnyType.ToString());
        if (variable != null) {
          mockedVarId[variable] = tmp;
        }
        return tmp;
      }
      var varId = new IdentifierExpr(new Token(), $"v{nextValueId++}");
      method.Body.AppendStmt(Statement.CreateLocalVariable(new Token(), varId.Name, dafnyType));
      if (DafnyInfo.IsExtern(dafnyType)) {
        var ctor = DafnyInfo.GetConstructor(dafnyType);
        if (ctor == null) {
          errorMessages.Add($"// Failed to find constructor for extern class {dafnyType}");
          return null;
        }
        var constructorArgs = new List<ActualBinding>();
        foreach (var argType in ctor.Ins.Select(formal => formal.Type)) {
          var processedType = Utils.CopyWithReplacements(
            Utils.UseFullName(argType),
            ctor.EnclosingClass.TypeArgs.ConvertAll(arg => arg.Name), dafnyType.TypeArgs);
          var argValue = GetDefaultValue(processedType);
          if (argValue == null) {
            return null;
          }
          constructorArgs.Add(new ActualBinding(new Token(), argValue));
        }
        var ctorName = ctor.EnclosingClass.FullDafnyName + (ctor.HasName ? ctor.Name : "");
        method.Body.AppendStmt(new AssignStmt(new Token(), new Token(), varId,
          new TypeRhs(new Token(), 
            new UserDefinedType(new Token(), ctorName, new List<Type>()), constructorArgs)));
      } else {
        var constFieldValues = new List<ActualBinding>();
        var immutableFields = DafnyInfo.GetNonGhostFields(dafnyType)
          .Where(field => !field.mutable);
        foreach (var field in
                 immutableFields) {
          var constFieldValue = GetFieldValue(field, variable);
          if (constFieldValue == null) {
            return null;
          }
          constFieldValues.Add(new ActualBinding(new Token(), constFieldValue));
        }
        method.Body.AppendStmt(new AssignStmt(new Token(), new Token(), varId,
          new ExprRhs(new FunctionCallExpr(new Token(), GetSynthesizeMethodName(dafnyType.ToString()), new ImplicitThisExpr(new Token()), new Token(), new Token(), constFieldValues))));
        TypesToSynthesize[dafnyType.ToString()] = dafnyType;
      }
      getClassTypeInstanceParams.Remove(dafnyType.ToString());
      if (variable != null) {
        mockedVarId[variable] = varId;
      }
      var mutableFields = DafnyInfo.GetNonGhostFields(dafnyType)
        .Where(field => field.mutable);
      foreach (var field in mutableFields) {
        var fieldValue = GetFieldValue(field, variable);
        if (fieldValue == null) {
          return null;
        }
        method.Body.AppendStmt(new AssignStmt(
          new Token(), 
          new Token(), 
          new ExprDotName(new Token(), varId, field.name, new List<Type>()),
          new ExprRhs(fieldValue)));
      }
      return varId;
    }

    private Expression GetFieldValue((string name, Type type, bool mutable, Expression/*?*/ defValue) field, DafnyModelVariable/*?*/ variable) {
      if (field.defValue != null) {
        return field.defValue;
      }
      if (variable != null && variable.Children.ContainsKey(field.name) &&
          variable.Children[field.name].Count == 1) {
        return ExtractVariable(variable.Children[field.name].First(), null);
      }

      var previouslyCreated = method.Body.Body.OfType<VarDeclStmt>()
        .Select(varDecl => varDecl.Locals[0])
        .FirstOrDefault(v => v.Type == field.type, null);
      if (previouslyCreated != null) {
        return new IdentifierExpr(new Token(), previouslyCreated);
      }
      return GetDefaultValue(field.type, field.type);
    }

    private static Expression GetPrimitiveAsType(Expression expression, Type/*?*/ asType) {
      if ((asType is null or IntType or RealType or BoolType or CharType
          or BitvectorType) || 
          (expression is SeqDisplayExpr seqDisplayExpr && seqDisplayExpr.Elements.Count == 0) ||
          (expression is SetDisplayExpr setDisplayExpr && setDisplayExpr.Elements.Count == 0) || 
          (expression is MapDisplayExpr mapDisplayExpr && mapDisplayExpr.Elements.Count == 0)) {
        return expression;
      }
      var typeString = asType.ToString();
      if (typeString.StartsWith("_System.")) {
        typeString = typeString[8..];
        return new ConversionExpr(new Token(), expression, new UserDefinedType(new Token(), typeString, asType.TypeArgs));
      }
      return new ConversionExpr(new Token(), expression, asType);
    }

    /// <summary>
    /// Return the default value for a variable of a particular type.
    /// Note that default value is different from unspecified value.
    /// An unspecified value is such a value for which a model does reserve
    /// an element (e.g. T@U!val!25).
    /// </summary>
    private Expression GetDefaultValue(Type type, Type/*?*/ asType = null) {
      if (type == null) {
        errorMessages.Add("// Failed - cannot determine type");
        return null;
      }
      if (type.ToString().Contains("_System.Tuple") ||
          (asType?.ToString() ?? "").Contains("_System.Tuple")) {
        errorMessages.Add("// Failed - temporary disable tuple support");
        return null;
      }
      type = GetBasicType(type, type => DafnyInfo.GetSupersetType(type) == null);
      type = DafnyModelTypeUtils.ReplaceType(type,
        _ => true,
        t => DafnyInfo.Datatypes.ContainsKey(t.Name) ?
          new DafnyModelTypeUtils.DatatypeType(t) :
          new UserDefinedType(t.tok, t.Name, t.TypeArgs));
      type = DafnyModelTypeUtils.ReplaceTypeVariables(type, defaultType);
      if ((asType != null) && (DafnyInfo.GetWitnessForType(asType) != null)) {
        return DafnyInfo.GetWitnessForType(asType);
      }
      switch (type) {
        case IntType:
          return GetPrimitiveAsType(new LiteralExpr(new Token(), 0), asType);
        case RealType:
          return GetPrimitiveAsType(new LiteralExpr(new Token(), BigDec.ZERO), asType);
        case BoolType:
          return GetPrimitiveAsType(new LiteralExpr(new Token(), false), asType);
        case CharType:
          return GetPrimitiveAsType(new CharLiteralExpr(new Token(), "a"), asType);
        case BitvectorType bitvectorType:
          return GetPrimitiveAsType(new ConversionExpr(new Token(), new LiteralExpr(new Token(), 0), bitvectorType), asType);
        case SeqType seqType:
          var seqName = "d" + nextValueId++;
          Expression seqValue = seqType.Arg is CharType
            ? new StringLiteralExpr(new Token(), "", true)
            : new SeqDisplayExpr(new Token(), new List<Expression>());
          method.Body.AppendStmt(Statement.CreateLocalVariable(new Token(), seqName, seqValue));
          return new IdentifierExpr(new Token(), seqName);
        case SetType setType:
          var setName = "d" + nextValueId++;
          method.Body.AppendStmt(Statement.CreateLocalVariable(new Token(),
            setName, 
            new SetDisplayExpr(new Token(), setType.Finite, new List<Expression>())));
          return new IdentifierExpr(new Token(), setName);
        case MapType mapType:
          var mapName = "d" + nextValueId++;
          method.Body.AppendStmt(Statement.CreateLocalVariable(new Token(),
            mapName, 
            new MapDisplayExpr(new Token(), mapType.Finite, new List<ExpressionPair>())));
          return new IdentifierExpr(new Token(), mapName);
        case UserDefinedType tupleType when tupleType.Name.StartsWith("_System.Tuple") || tupleType.Name.StartsWith("_System._tuple"):
          errorMessages.Add("// Failed - temporary disable tuple support");
          return null;
        case DafnyModelTypeUtils.DatatypeType datatypeType:
          Expression value;
          if (getDefaultValueParams.Contains(datatypeType.Name)) {
            errorMessages.Add($"// Failed to non-recursively construct a default value for type {datatypeType}");
            return null;
          }
          if (!DafnyInfo.Datatypes.ContainsKey(datatypeType.Name)) {
            errorMessages.Add($"// Failed to determine default constructors for datatype (type {datatypeType})");
            return null;
          }
          getDefaultValueParams.Add(datatypeType.ToString());
          var ctor = DafnyInfo.Datatypes[datatypeType.Name].Ctors.MinBy(ctor => ctor.Destructors.Count);
          List<ActualBinding> assignments = new();
          foreach (var destructor in ctor.Destructors) {
            var token = new Token();
            token.val = destructor.Name;
            var arg = GetDefaultValue(
              Utils.CopyWithReplacements(Utils.UseFullName(destructor.Type),
                ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name),
                datatypeType.TypeArgs));
            if (arg == null) {
              return null;
            }
            assignments.Add(new ActualBinding(token, arg));
          }
          value = new DatatypeValue(new Token(), datatypeType.Name, ctor.Name,
            assignments);
          var name = "d" + nextValueId++;
          method.Body.AppendStmt(Statement.CreateLocalVariable(new Token(),
            name, GetPrimitiveAsType(value, asType ?? datatypeType)));
          getDefaultValueParams.RemoveAt(getDefaultValueParams.Count - 1);
          return new IdentifierExpr(new Token(), name);

        case ArrowType arrowType:
          return GetFunctionOfType(arrowType);
        case UserDefinedType unknown when unknown.Name == DafnyModel.UnknownType.Name:
          errorMessages.Add($"// Failed to determine type of a default value");
          return null;
        case UserDefinedType userDefinedType when userDefinedType.Name.EndsWith("?"):
          return new LiteralExpr(new Token());
        case UserDefinedType userDefinedType:
          return GetClassTypeInstance(userDefinedType, asType, null);
      }
      errorMessages.Add(
        $"// Failed to extract default value for type " + type ?? "(null)");
      return null;
    }

    /// <summary>
    /// Extract output of an "assume {:print ...} true;"  statement.
    /// </summary>
    /// <param name="log">the counterexample log as a string</param>
    /// <param name="prefix">the prefix of the print statement such as
    /// "Types" or "Impl" - these come from ProgramModifier</param>
    private static List<string> ExtractPrintedInfo(string log, string prefix) {
      var lines = log.Split("\n");
      foreach (var line in lines) {
        if (!line.StartsWith(prefix)) {
          continue;
        }

        var result = line.Split("|").ToList();
        result.RemoveAt(0);
        for (var i = 0; i < result.Count; i++) {
          result[i] = Regex.Replace(result[i],
            "/ *([0-9]+\\.[0-9]+) +([0-9]+\\.[0-9]+)", "$1/$2");
          result[i] = Regex.Replace(result[i], "[)( \\\\]", "");
        }

        return result;
      }

      return new List<string>();
    }

    /// <summary>  Return the test method as a list of lines of code </summary>
    private List<string> TestMethodLines() {

      List<string> lines = new();

      var returnParNames = new List<string>();
      for (var i = 0; i < DafnyInfo.GetReturnTypes(MethodName).Count; i++) {
        returnParNames.Add("r" + i);
      }

      string receiver = "";
      if (!DafnyInfo.IsStatic(MethodName)) {
        receiver = ArgValues[0];
        ArgValues.RemoveAt(0);
      }

      lines.AddRange(DafnyInfo.GetRequires(ArgValues,
        MethodName,
        receiver).Select(e =>
        "expect " + Printer.ExprToString(e) +
        ", \"Test does not meet preconditions and should be removed\";"));
      if (!DafnyInfo.IsStatic(MethodName)) {
        ArgValues.Insert(0, receiver);
      }

      // the method call itself:
      var typeArguments = "";
      if (NOfTypeArgs > 0) {
        typeArguments = "<" + string.Join(",", Enumerable.Repeat(defaultType.ToString(), NOfTypeArgs)) + ">";
      }
      string methodCall;
      if (DafnyInfo.IsStatic(MethodName)) {
        methodCall = $"{MethodName}{typeArguments}({string.Join(", ", ArgValues)});";
      } else {
        ArgValues.RemoveAt(0);
        methodCall = $"{receiver}.{MethodName.Split(".").Last()}" +
                     $"{typeArguments}({string.Join(", ", ArgValues)});";
        ArgValues.Insert(0, receiver);
      }

      var returnValues = "";
      if (returnParNames.Count != 0) {
        returnValues = "var " + string.Join(", ", returnParNames) + " := ";
      }

      lines.Add(returnValues + methodCall);
      if (!DafnyInfo.IsStatic(MethodName)) {
        ArgValues.RemoveAt(0);
      }

      
      lines.AddRange(DafnyInfo.GetEnsures(ArgValues,
        returnParNames,
        MethodName,
        receiver).Select(e => "expect " + Printer.ExprToString(e) + ";"));

      if (!DafnyInfo.IsStatic(MethodName)) {
        ArgValues.Insert(0, receiver);
      }
      lines.Add("}");

      return lines;
    }

    public override string ToString() {
      return string.Join("\n", TestMethodLines());
    }

    public override int GetHashCode() {
      var lines = TestMethodLines();
      if (lines.Count == 0) {
        return "".GetHashCode();
      }
      lines.RemoveAt(0);
      var hashCode = string.Join("", lines).GetHashCode();
      return hashCode;
    }

    public override bool Equals(object/*?*/ obj) {
      if (obj is not TestMethod other) {
        return false;
      }
      var otherLines = other.TestMethodLines();
      var lines = TestMethodLines();
      if (lines.Count != otherLines.Count) {
        return false;
      }
      if (lines.Count == 0) {
        return true;
      }
      lines.RemoveAt(0);
      otherLines.RemoveAt(0);
      return string.Join("", lines) == string.Join("", otherLines);
    }
  }
}