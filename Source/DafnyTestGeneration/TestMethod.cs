// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.CounterExampleGeneration;
using IdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using MapType = Microsoft.Dafny.MapType;
using Token = Microsoft.Dafny.Token;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  /// <summary> Allows converting a counterexample to a test method </summary>
  public class TestMethod {

    private static int nextId; // next unique id to be assigned

    // list of values to mock together with their types
    // maps a variable that is mocked to its unique id
    private readonly Dictionary<PartialValue, string> mockedVarId = new();
    public readonly List<(string parentId, string fieldName, string childId)> Assignments = new();
    public readonly List<(string id, Type type, string value)> ValueCreation = new();
    // next id to assign to a variable with given name:
    private Dictionary<string, int> nameToNextId = new();
    private readonly int id = nextId++;
    public readonly DafnyInfo DafnyInfo;
    // name of the method for which the counterexample is generated
    public readonly string MethodName;
    // values of the arguments to be passed to the method call
    public readonly List<string> ArgValues;
    // number of type arguments for the method (all will be set to defaultType)
    public readonly int NOfTypeArgs;
    // default type to replace any type variable with
    private readonly Type defaultType = Type.Int;
    // the DafnyModel that describes the inputs to this test method
    private readonly DafnyModel dafnyModel;
    // is set to true whenever the tool encounters something it does not support
    private readonly List<string> errorMessages = new();
    // records parameters for GetDefaultValue call - this is used to to
    // terminate potential infinite recursion
    private List<string> getDefaultValueParams = new();
    // similar to above but for objects
    private readonly HashSet<string> getClassTypeInstanceParams = new();
    private readonly Modifications cache;

    private readonly Dictionary<PartialValue, Expression> constraintContext;

    // Added for predicate generation
    private static int classTypePredicateCounter = 0;
    private static readonly Dictionary<PartialValue, string> classTypePredicates = new();
    public readonly List<string> PredicateMethods = new();
    public readonly List<string> ExpectStatements = new();

    public TestMethod(DafnyInfo dafnyInfo, string log, Modifications cache) {
      DafnyInfo = dafnyInfo;
      this.cache = cache;
      var typeNames = ExtractPrintedInfo(log, "Types | ");
      var argumentNames = ExtractPrintedInfo(log, "Impl | ");
      dafnyModel = DafnyModel.ExtractModel(dafnyInfo.Options, log);
      dafnyModel.AssignConcretePrimitiveValues();
      MethodName = argumentNames.First();
      argumentNames.RemoveAt(0);
      NOfTypeArgs = dafnyInfo.GetTypeArgs(MethodName).Count;
      constraintContext = new Dictionary<PartialValue, Expression>();
      foreach (var partialValue in dafnyModel.States.First().KnownVariableNames.Keys) {
        constraintContext[partialValue] = new Microsoft.Dafny.IdentifierExpr(Token.NoToken, dafnyModel.States.First().KnownVariableNames[partialValue].First());
        constraintContext[partialValue].Type = partialValue.Type;
      }
      ArgValues = ExtractInputs(dafnyModel.States.First(), argumentNames, typeNames);
    }

    public bool IsValid => errorMessages.Count == 0;

    /// <summary>
    /// Add a tuple to the ValueCreation list with a given type and value.
    /// The name of the variable assigned to the value is chosen so that it is
    /// unique and begins with the name of the type. Return that name.
    /// </summary>
    private string AddValue(Type type, string value) {
      var name = Regex.Replace(type.ToString().Split(".").Last().Split(" ")[0], "[^a-zA-Z]", "");
      if (name == "") {
        name = "v";
      }
      name = name[0].ToString().ToLower() + name[1..];
      if (!nameToNextId.ContainsKey(name)) {
        nameToNextId[name] = 0;
      }
      name += nameToNextId[name]++;
      ValueCreation.Add((name, type, value));
      return name;
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
    public static string EmitSynthesizeMethods(DafnyInfo dafnyInfo, Modifications cache) {
      var result = "";
      // ensures that duplicate types in TypesToSynthesize are skipped:
      HashSet<string> emittedTypes = new();
      foreach (var typ in cache.TypesToSynthesize) {
        var typeString = typ.ToString();
        if (emittedTypes.Contains(typeString)) {
          continue;
        }
        emittedTypes.Add(typeString);
        var methodName = GetSynthesizeMethodName(typeString);
        var returnName = "o";
        if (!dafnyInfo.IsTrait(typ)) {
          var constFields = dafnyInfo.GetNonGhostFields(typ)
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
                    $"returns ({returnName}:{typeString}) ensures fresh({returnName}) " +
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
    private List<string> ExtractInputs(PartialState state, IReadOnlyList<string> printOutput, IReadOnlyList<string> types) {
      var result = new List<string>();
      var vars = state.ExpandedVariableSet(-1);
      var constraintSet = new List<Constraint>();
      foreach (var variable in vars) {
        foreach (var constraint in variable.Constraints) {
          constraintSet.Add(constraint);
        }
      }
      var constraints = constraintSet.ToList();
      constraints = Constraint.ResolveAndOrder(constraintContext, constraints, false);
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
          result.Add(GetDefaultValue(type, type));
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
    private string GetADefaultTypeValue(PartialValue variable) {
      return "0";
    }

    private string GetFunctionOfType(ArrowType type) {
      type = (ArrowType)DafnyModelTypeUtils.ReplaceTypeVariables(type, defaultType);
      var lambda =
        $"({string.Join(",", type.TypeArgs.SkipLast(1).Select((t, i) => "a" + i + ":" + t))})" + // parameter types
        "=>" + // return type
        $"{GetDefaultValue(type.TypeArgs.Last())}"; // body
      return lambda;
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
    private string ExtractVariable(PartialValue variable, Type/*?*/ asType) {
      if (variable == null) {
        if (asType != null) {
          return GetDefaultValue(asType, asType);
        } else {
          errorMessages.Add("// Failed: variable and type are null");
          return "";
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

      List<string> elements = new();
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
          return GetPrimitiveAsType(variable.PrimitiveLiteral, asType);
        case SeqType seqType:
          var asBasicSeqType = GetBasicType(asType, type => type is SeqType) as SeqType;
          if (variable?.Cardinality() == -1) {
            if (seqType.Arg is CharType) {
              return "\"\"";
            }
            return AddValue(asType ?? variableType, "[]");
          }
          for (var i = 0; i < variable?.Cardinality(); i++) {
            var element = variable?[i];
            if (element == null) {
              getDefaultValueParams = new();
              elements.Add(GetDefaultValue(seqType.Arg, asBasicSeqType?.TypeArgs?.FirstOrDefault((Type/*?*/)null)));
              continue;
            }
            elements.Add(ExtractVariable(element, asBasicSeqType?.TypeArgs?.FirstOrDefault((Type/*?*/)null)));
          }

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

          if (seqType.Arg is CharType || asBasicSeqType?.TypeArgs?.FirstOrDefault((Type/*?*/)null) is CharType) {
            return $"\"{string.Join("", elements.SelectMany(c => c[1..^1]))}\"";
          }
          return AddValue(asType ?? variableType, $"[{string.Join(", ", elements)}]");
        case SetType:
          var asBasicSetType = GetBasicType(asType, type => type is SetType) as SetType;
          foreach (var element in variable.SetElements()) {
            elements.Add(ExtractVariable(element, asBasicSetType?.TypeArgs?.FirstOrDefault((Type/*?*/)null)));
          }
          return AddValue(asType ?? variableType, $"{{{string.Join(", ", elements)}}}");
        case MapType:
          var asBasicMapType = GetBasicType(asType, type => type is MapType) as MapType;
          List<string> mappingStrings = new();
          foreach (var mapping in variable?.Mappings()) {
            var asTypeTypeArgs =
              asBasicMapType?.TypeArgs?.Count == 2 ? asBasicMapType.TypeArgs : null;
            mappingStrings.Add($"{ExtractVariable(mapping.Key, asTypeTypeArgs?[0])} := {ExtractVariable(mapping.Value, asTypeTypeArgs?[1])}");
          }
          return AddValue(asType ?? variableType, $"map[{string.Join(", ", mappingStrings)}]");
        case UserDefinedType tupleType when tupleType.Name.StartsWith("_tuple#"):
          return AddValue(asType ?? variableType, "(" +
            string.Join(",", variable.UnnamedDestructors()
              .Select(v => ExtractVariable(v, null))) + ")");
        case ArrowType arrowType:
          var asBasicArrowType = GetBasicType(asType, type => type is ArrowType) as ArrowType;
          return GetFunctionOfType(asBasicArrowType ?? arrowType);
        case UserDefinedType unknown when unknown.Name == DafnyModel.UnknownType.Name:
          if (asType != null) {
            return GetDefaultValue(asType, asType);
          }
          errorMessages.Add($"// Failed to determine a variable type (element {variable.Element}).");
          return "null";
        case UserDefinedType arrType when new Regex("^_System.array[0-9]*\\?$").IsMatch(arrType.Name):
          errorMessages.Add($"// Failed because arrays are not yet supported (type {arrType} element {variable.Element})");
          break;
        case UserDefinedType _ when variable.PrimitiveLiteral != "":
          return "null";
        case UserDefinedType userDefinedType:
          var basicType = GetBasicType(asType ?? userDefinedType,
            type => type == null || type is not UserDefinedType definedType ||
                    DafnyInfo.Datatypes.ContainsKey(definedType
                      .Name)) as UserDefinedType;
          if (basicType == null || !DafnyInfo.Datatypes.ContainsKey(basicType.Name)) {
            if (DafnyInfo.IsClassType(userDefinedType)) {
              if (mockedVarId.ContainsKey(variable)) {
                return mockedVarId[variable];
              }

              string predicateName;
              if (!classTypePredicates.ContainsKey(variable)) {
                predicateName = $"ClassTypePredicate{classTypePredicateCounter++}";
                classTypePredicates[variable] = predicateName;
                GeneratePredicateMethod(predicateName, userDefinedType, variable);
              } else {
                predicateName = classTypePredicates[variable];
              }

              var varName = AddValue(asType ?? userDefinedType, $"Generate{predicateName}()");
              mockedVarId[variable] = varName;
              // ExpectStatements.Add($"expect {classTypePredicates[variable]}({varName}), \"If this check fails, the test does not satisfy the constraints\";");
              return varName;
            }
            return "null";
          } else {
            if (variable.DatatypeConstructorName() == "") {
              getDefaultValueParams = new();
              return GetDefaultValue(userDefinedType, asType);
            }

            var ctor = DafnyInfo.Datatypes[basicType.Name].Ctors
              .FirstOrDefault(ctor => ctor.Name == variable.DatatypeConstructorName(), null);
            if (ctor == null) {
              errorMessages.Add(
                $"// Failed: Cannot find constructor {variable.DatatypeConstructorName()} for datatype {basicType}");
              return basicType.ToString();
            }

            List<string> fields = new();
            for (int i = 0; i < ctor.Destructors.Count; i++) {
              var fieldName = ctor.Destructors[i].Name;
              if (!variable.Fields().ContainsKey(fieldName)) {
                fieldName = $"[{i}]";
              }

              if (!variable.Fields().ContainsKey(fieldName)) {
                errorMessages.Add($"// Failed: Cannot find destructor " +
                                  $"{ctor.Destructors[i].Name} of constructor " +
                                  $"{variable.DatatypeConstructorName()} for datatype " +
                                  $"{basicType}. Available destructors are: " +
                                  string.Join(",", variable.Fields().Keys.ToList()));
                return basicType.ToString();
              }

              var destructorType = Utils.CopyWithReplacements(
                Utils.UseFullName(ctor.Destructors[i].Type),
                ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), basicType.TypeArgs);
              if (ctor.Destructors[i].Name.StartsWith("#")) {
                fields.Add(ExtractVariable(variable.Fields()[fieldName], destructorType));
              } else {
                fields.Add(ctor.Destructors[i].Name + ":=" +
                           ExtractVariable(variable.Fields()[fieldName], destructorType));
              }
            }

            var value = basicType.ToString();
            if (fields.Count == 0) {
              value += "." + variable.DatatypeConstructorName();
            } else {
              value += "." + variable.DatatypeConstructorName() + "(" +
                       string.Join(",", fields) + ")";
            }

            return AddValue(asType ?? userDefinedType, value);
          }
      }
      errorMessages.Add(
        $"// Failed to extract default value for type " + variableType ?? "(null)");
      return "null";
    }
    
    
    private void GeneratePredicateMethod(string predicateName, UserDefinedType userDefinedType, PartialValue variable) {
      // Map from PartialValue to expressions
      Dictionary<PartialValue, Expression> definitions = new();

      // Map the partialValue to the parameter name
      var paramName = "o";
      var paramExpr = new IdentifierExpr(Token.NoToken, paramName);
      paramExpr.Type = userDefinedType;
      definitions[variable] = paramExpr;

      // Collect variables reachable from variable
      var varsToProcess = new Queue<PartialValue>();
      varsToProcess.Enqueue(variable);
      var processedVars = new HashSet<PartialValue> { variable };

      while (varsToProcess.Count > 0) {
        var v = varsToProcess.Dequeue();
        foreach (var relatedVar in v.GetRelatedValues()) {
          if (!processedVars.Contains(relatedVar)) {
            varsToProcess.Enqueue(relatedVar);
            processedVars.Add(relatedVar);
          }
        }
      }

      // Apply preprocessing to constraints for sets and maps
      foreach (var partialValue in processedVars.Where(pv =>
                 pv.Type is SetType || pv.Type is MapType)) {
        var elements = partialValue.Constraints
          .OfType<ContainmentConstraint>()
          .Where(c => c.IsIn && Equals(c.Set, partialValue))
          .Select(c => c.Element).ToList();
        if (elements.Count == 0 && partialValue.Constraints.OfType<LiteralExprConstraint>()
              .Any(c => c.LiteralExpr is SetDisplayExpr or MapDisplayExpr)) {
          continue;
        }

        if (partialValue.Type is SetType) {
          _ = new SetDisplayConstraint(partialValue, elements);
        } else {
          _ = new MapKeysDisplayConstraint(partialValue, elements);
        }
      }

      // Collect and filter constraints
      var allConstraints = processedVars.SelectMany(var => var.Constraints).ToHashSet()
        .Where(constraint => constraint is not IdentifierExprConstraint)
        .Where(constraint =>
          constraint is not ContainmentConstraint containmentConstraint || containmentConstraint.IsIn)
        .Where(constraint => constraint is not FunctionCallConstraint functionCallConstraint ||
                             (functionCallConstraint.DefinedValue.Type == Type.Bool &&
                              functionCallConstraint.ReferencedValues.Count() == 1))
        .ToList();

      // Resolve and order constraints without introducing new variables
      var constraints = Constraint.ResolveAndOrder(definitions, allConstraints, false);

      // Convert constraints to expressions
      var constraintExprs = new List<Expression>();
      var constraintsAsStrings = new HashSet<string>();
      foreach (var constraint in constraints) {
        var expr = constraint.AsExpression(definitions);
        if (expr == null || constraint is TypeTestConstraint || constraint is DatatypeConstructorCheckConstraint) {
          continue;
        }

        var exprString = expr.ToString();
        if (constraintsAsStrings.Contains(exprString)) {
          continue;
        }
        constraintsAsStrings.Add(exprString);

        // Optimization: Convert 'A !in users' to '!(A in users)' and 'A != B' to '!(A == B)'
        /*if (expr is BinaryExpr binaryExpr) {
          if (binaryExpr.Op == BinaryExpr.Opcode.NotIn) {
            expr = new BinaryExpr(binaryExpr.tok, BinaryExpr.Opcode.In, binaryExpr.E0, binaryExpr.E1);
            expr.Type = Type.Bool;
            expr = new UnaryOpExpr(binaryExpr.tok, UnaryOpExpr.Opcode.Not, expr) { Type = Type.Bool };
            constraintExprs.Add(expr);
            continue;
          }
          if (binaryExpr.Op == BinaryExpr.Opcode.Neq) {
            expr = new BinaryExpr(binaryExpr.tok, BinaryExpr.Opcode.Eq, binaryExpr.E0, binaryExpr.E1);
            expr.Type = Type.Bool;
            expr = new UnaryOpExpr(binaryExpr.tok, UnaryOpExpr.Opcode.Not, expr) { Type = Type.Bool };
            constraintExprs.Add(expr);
            continue;
          }
        }*/

        constraintExprs.Add(expr);
      }

      // Build the conjunction of constraints
      Expression body = PartialState.GetCompactConjunction(constraintExprs);

      // Generate the predicate code
      var functionCode = $"ghost predicate {{:synthesize \"Generate{predicateName}\"}} {predicateName}(o: {userDefinedType}) reads o {{\n";
      functionCode += $"  {Printer.ExprToString(DafnyInfo.Options, body)}\n";
      functionCode += "}";
      PredicateMethods.Add(functionCode);
      var implementingMethod =
        $"static method Generate{predicateName} () returns (o: {userDefinedType}) ensures {predicateName}(o)";
      PredicateMethods.Add(implementingMethod);
    }

    private static string GetPrimitiveAsType(string value, Type/*?*/ asType) {
      if ((asType is null or IntType or RealType or BoolType or CharType
          or BitvectorType) || value is "[]" or "{}" or "map[]") {
        return value;
      }
      var typeString = asType.ToString();
      if (typeString.StartsWith("_System.")) {
        typeString = typeString[8..];
      }
      return $"({value} as {typeString})";
    }

    /// <summary>
    /// Return the default value for a variable of a particular type.
    /// Note that default value is different from unspecified value.
    /// An unspecified value is such a value for which a model does reserve
    /// an element (e.g. T@U!val!25).
    /// </summary>
    private string GetDefaultValue(Type type, Type/*?*/ asType = null) {
      if (type == null) {
        errorMessages.Add("// Failed - cannot determine type");
        return "";
      }
      type = GetBasicType(type, type => DafnyInfo.GetSupersetType(type) == null);
      type = DafnyModelTypeUtils.ReplaceTypeVariables(type, defaultType);
      if ((asType != null) && (DafnyInfo.GetWitnessForType(asType) != null)) {
        return DafnyInfo.GetWitnessForType(asType);
      }
      switch (type) {
        case IntType:
          return GetPrimitiveAsType("0", asType);
        case RealType:
          return GetPrimitiveAsType("0.0", asType);
        case BoolType:
          return GetPrimitiveAsType("false", asType);
        case CharType:
          return GetPrimitiveAsType("\'a\'", asType);
        case BitvectorType bitvectorType:
          return GetPrimitiveAsType($"(0 as bv{bitvectorType.Width})", asType);
        case SeqType seqType:
          return seqType.Arg is CharType ? "\"\"" : AddValue(asType ?? type, "[]");
        case SetType:
          return AddValue(asType ?? type, "{}");
        case MapType mapType:
          return AddValue(asType ?? type, mapType.Finite ? "map[]" : "imap[]");
        case UserDefinedType tupleType when tupleType.Name.StartsWith("_tuple#"):
          var destructors = new List<string>();
          foreach (var arg in tupleType.TypeArgs) {
            destructors.Add(GetDefaultValue(arg));
          }
          return AddValue(tupleType, "(" + string.Join(",", destructors) + ")");
        case ArrowType arrowType:
          return GetFunctionOfType(arrowType);
        case UserDefinedType unknown when unknown.Name == DafnyModel.UnknownType.Name:
          errorMessages.Add($"// Failed to determine type of a default value");
          return "null";
        case UserDefinedType userDefinedType when userDefinedType.Name.EndsWith("?"):
          return "null";
        case UserDefinedType datatypeType when DafnyInfo.Datatypes.ContainsKey(datatypeType.Name):
          string value;
          if (getDefaultValueParams.Contains(datatypeType.Name)) {
            errorMessages.Add($"// Failed to non-recursively construct a default value for type {datatypeType}");
            return datatypeType.Name + ".UNKNOWN";
          }
          getDefaultValueParams.Add(datatypeType.ToString());
          var ctor = DafnyInfo.Datatypes[datatypeType.Name].Ctors.MinBy(ctor => ctor.Destructors.Count);
          if (ctor.Destructors.Count == 0) {
            value = datatypeType + "." + ctor.Name;
          } else {
            var assignments = ctor.Destructors.Select(destructor =>
              (destructor.Name.StartsWith("#") ? "" : destructor.Name + ":=") + GetDefaultValue(
                Utils.CopyWithReplacements(Utils.UseFullName(destructor.Type),
                    ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), datatypeType.TypeArgs),
                Utils.CopyWithReplacements(Utils.UseFullName(destructor.Type),
                  ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), datatypeType.TypeArgs)));
            value = datatypeType + "." + ctor.Name + "(" +
                   string.Join(",", assignments) + ")";
          }
          var name = AddValue(asType ?? datatypeType, value);
          getDefaultValueParams.RemoveAt(getDefaultValueParams.Count - 1);
          return name;
        case UserDefinedType userDefinedType:
          return "null";
      }
      errorMessages.Add(
        $"// Failed to extract default value for type " + type ?? "(null)");
      return "null";
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

    /// <summary>  Return the test input as a list of lines of code </summary>
    public List<string> TestInputConstructionLines() {
      List<string> lines = new();

      foreach (var line in ValueCreation) {
        lines.Add($"var {line.id} : {line.type} := {line.value};");
        var subsetTypeCondition = DafnyInfo.GetTypeCondition(line.type, line.id);
        if (subsetTypeCondition != null) {
          lines.Add("expect " + Printer.ExprToString(DafnyInfo.Options, subsetTypeCondition) +
                    ", \"If this check fails at runtime, the test does not meet the type constraints\";");
        }
      }

      // assignments necessary to set up the test case:
      foreach (var assignment in Assignments) {
        lines.Add($"{assignment.parentId}.{assignment.fieldName} := " +
                  $"{assignment.childId};");
      }

      // Add expect statements for class type predicates
      lines.AddRange(ExpectStatements);

      return lines;
    }

    /// <summary>  Return the test method as a list of lines of code </summary>
    private List<string> TestMethodLines() {

      List<string> lines = new();

      if (errorMessages.Count != 0) {
        if (DafnyInfo.Options.Verbose) {
          lines.AddRange(errorMessages);
        }
        return lines;
      }

      var returnParNames = new List<string>();
      for (var i = 0; i < DafnyInfo.GetReturnTypes(MethodName).Count; i++) {
        returnParNames.Add("r" + i);
      }

      lines.Add($"method {{:test}} Test{id}() {{");

      lines.AddRange(TestInputConstructionLines());

      string receiver = "";
      if (!DafnyInfo.IsStatic(MethodName)) {
        receiver = ArgValues[0];
        ArgValues.RemoveAt(0);
      }

      lines.AddRange(DafnyInfo.GetRequires(ArgValues,
        MethodName,
        receiver).Select(e =>
        "expect " + Printer.ExprToString(DafnyInfo.Options, e) +
        ", \"If this check fails at runtime, the test does not meet the preconditions\";"));
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
        receiver).Select(e => "expect " + Printer.ExprToString(DafnyInfo.Options, e) + ";"));

      if (!DafnyInfo.IsStatic(MethodName)) {
        ArgValues.Insert(0, receiver);
      }
      lines.Add("}");

      // Add the predicate methods to the output
      lines.AddRange(PredicateMethods);

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