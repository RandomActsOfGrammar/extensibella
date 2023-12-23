grammar extensibella:toAbella:abstractSyntax;

--things you can do outside of proofs

nonterminal TopCommand with
   --pp should always end with a newline
   pp, abella_pp,
   toAbella<[AnyCommand]>, toAbellaMsgs,
   interactive,
   newProofState,
   newTheorems,
   provingTheorems, provingExtInds, duringCommands, afterCommands,
   currentModule, typeEnv, constructorEnv, relationEnv, proverState;
propagate constructorEnv, relationEnv, currentModule, proverState,
          toAbellaMsgs, interactive on TopCommand
   excluding definitionDeclaration;
propagate typeEnv on TopCommand excluding definitionDeclaration,
                                          theoremDeclaration;

aspect default production
top::TopCommand ::=
{
  top.duringCommands = [];
  top.afterCommands = [];
  top.newTheorems = [];
  top.provingExtInds = [];
}


abstract production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  local buildParams::(String ::= [String]) =
     \ p::[String] ->
       case p of
       | [] ->
         error("Should not reach here; theoremDeclaration production")
       | [a] -> a
       | a::rest ->
         a ++ ", " ++ buildParams(rest)
       end;
  local paramsString::String =
     if null(params)
     then ""
     else " [" ++ buildParams(params) ++ "] ";
  top.pp = text("Theorem ") ++ name.pp ++ text(" ") ++
           text(paramsString) ++ text(":") ++
           nest(2, line() ++ docGroup(body.pp)) ++
           text(".") ++ realLine();
  top.abella_pp = "Theorem " ++ name.abella_pp ++ " " ++
                  paramsString ++ " : " ++ body.abella_pp ++ ".\n";

  production fullName::QName =
      if name.isQualified
      then name
      else addQNameBase(top.currentModule, name.shortName);
  top.toAbella =
      [anyTopCommand(
          theoremDeclaration(fullName, params, body.toAbella))];

  body.typeEnv = addEnv(top.typeEnv, map(typeVarEnvItem, params));

  body.boundNames = [];

  --check if name is qualified and has the appropriate module
  top.toAbellaMsgs <-
      if name.isQualified
      then if name.moduleName == top.currentModule
           then []
           else [errorMsg("Theorem name " ++ justShow(name.pp) ++
                    " does not have correct module (expected " ++
                    justShow(top.currentModule.pp))]
      else [];
  --check there are no existing theorems with this full name
  top.toAbellaMsgs <-
      if null(findTheorem(fullName, top.proverState))
      then []
      else [errorMsg("Theorem named " ++ justShow(fullName.pp) ++
                     " already exists")];

  top.provingTheorems = [(fullName, body)];
}


abstract production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.pp = text("Define ") ++
           nest(7,
              docGroup(ppImplode(cat(text(","), line()),
                          map(\ p::(QName, Type) ->
                                docGroup(p.1.pp ++ text(" :") ++
                                         nest(3, line() ++ p.2.pp)),
                              preds)))) ++
           text(" by") ++ realLine() ++
           ppImplode(text(";") ++ realLine(), defs.pps) ++
           text(".") ++ realLine();
  local predsString_abella::String =
     if null(preds)
     then error("Definition should not be empty; definitionDeclaration")
     else implode(",\n       ",
             map(\ p::(QName, Type) ->
                   p.1.abella_pp ++ " : " ++ p.2.abella_pp, preds));
  top.abella_pp = "Define " ++ predsString_abella ++ " by " ++
                  defs.abella_pp ++ ".\n";

  production fullNames::[(QName, Type)] =
      map(\ p::(QName, Type) ->
            if p.1.isQualified
            then p
            else (addQNameBase(top.currentModule, p.1.shortName),
                  decorate p.2 with {typeEnv = top.typeEnv;}.toAbella),
          preds);

  defs.beingDefined = fullNames;
  defs.relationEnv =
       map(\ p::(QName, Type) ->
             fixedRelationEnvItem(p.1,
                foldrLastElem(addTypeList,
                   \ x::Type -> emptyTypeList(), p.2.toList)),
           fullNames) ++ top.relationEnv;
  propagate typeEnv, constructorEnv, toAbellaMsgs;

  top.toAbella =
      [anyTopCommand(definitionDeclaration(fullNames,
                                           defs.toAbella))];

  --check names are qualified with appropriate module
  top.toAbellaMsgs <-
      flatMap(\ p::(QName, Type) ->
                if p.1.isQualified
                then if p.1.moduleName == top.currentModule
                     then []
                     else [errorMsg("Declared predicate name " ++
                              justShow(p.1.pp) ++ " does not have " ++
                              "correct module (expected " ++
                              justShow(top.currentModule.pp) ++ ")")]
                else [], preds);

  top.provingTheorems = [];
}


abstract production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.pp = ppConcat([text("Codefine"),
              nest(9,
                 docGroup(ppImplode(cat(text(","), line()),
                             map(\ p::(QName, Type) ->
                                   docGroup(
                                      ppConcat([p.1.pp, text(" : "),
                                                p.2.pp])),
                                 preds)))),
              text("by"), realLine(),
              ppImplode(cat(text(";"), realLine()), defs.pps),
              text("."), realLine()]);
  local predsString_abella::String =
     if null(preds)
     then error("CoDefinition should not be empty; codefinitionDeclaration")
     else implode(",\n       ",
             map(\ p::(QName, Type) ->
                   p.1.abella_pp ++ " : " ++ p.2.abella_pp, preds));
  top.abella_pp = "CoDefine " ++ predsString_abella ++ " by " ++
                  defs.abella_pp ++ ".\n";

  production fullNames::[(QName, Type)] =
      map(\ p::(QName, Type) ->
            if p.1.isQualified
            then p
            else (addQNameBase(top.currentModule, p.1.shortName),
                  p.2),
          preds);

  defs.beingDefined = fullNames;

  top.toAbella = error("codefinitionDeclaration.toAbella");

  --check names are qualified with appropriate module
  top.toAbellaMsgs <-
      flatMap(\ p::(QName, Type) ->
                if p.1.isQualified
                then if p.1.moduleName == top.currentModule
                     then []
                     else [errorMsg("Declared predicate name " ++
                              justShow(p.1.pp) ++ " does not have " ++
                              "correct module (expected " ++
                              justShow(top.currentModule.pp) ++ ")")]
                else [], preds);

  top.provingTheorems = [];
}


abstract production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.pp = ppConcat([text("Query "), m.pp, text("."), realLine()]);
  top.abella_pp = "Query " ++ m.abella_pp ++ ".\n";

  m.boundNames = [];

  top.toAbella = [anyTopCommand(queryCommand(m.toAbella))];

  top.toAbellaMsgs <-
      if !top.interactive
      then [errorMsg("Query command should not be used in " ++
                     "non-interactive settings")]
      else [];

  top.provingTheorems = [];
}


abstract production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  top.pp = ppConcat([text("Split"), theoremName.pp, text(" as"),
              line(), ppImplode(cat(text(","), line()),
                         map((.pp), newTheoremNames)),
              text("."), realLine()]);
  local namesString_abella::String =
      if null(newTheoremNames)
      then ""
      else " as " ++
           implode(", ", map((.abella_pp), newTheoremNames));
  top.abella_pp = "Split " ++ theoremName.abella_pp ++
                  namesString_abella ++ ".\n";

  top.toAbella =
      [anyTopCommand(splitTheorem(head(thm).1, expandedNames))];
  --
  production thm::[(QName, Metaterm)] =
     findTheorem(theoremName, top.proverState);
  production splitThm::[Metaterm] = splitMetaterm(head(thm).2);
  --Need to add module to given names and make up names for rest
  local qedNewNames::[QName] =
     map(\ q::QName ->
           if q.isQualified
           then q
           else addQNameBase(top.currentModule, q.shortName),
         newTheoremNames);
  local moreNames::[QName] =
      foldr(\ m::Metaterm rest::[QName] ->
              addQNameBase(top.currentModule,
                           theoremName.shortName ++ "_" ++
                           toString(genInt()))::rest,
            [], drop(length(newTheoremNames), splitThm));
  production expandedNames::[QName] = qedNewNames ++ moreNames;

  top.provingTheorems = [];
}


abstract production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.pp = ppConcat([text("Close "), ppImplode(text(", "), tys.pps),
                     text("."), realLine()]);
  top.abella_pp = "Close " ++ tys.abella_pp ++ ".\n";

  top.toAbella = error("closeCommand.toAbella");

  top.provingTheorems = [];
}


abstract production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.pp = ppConcat([text("Kind "), ppImplode(cat(text(","), line()),
                                       map((.pp), names)),
                     line(), k.pp, text("."), realLine()]);
  local namesString_abella::String =
     if null(names)
     then ""
     else " " ++ implode(", ", map((.abella_pp), names));
  top.abella_pp = "Kind" ++ namesString_abella ++ "   " ++
                  k.abella_pp ++ ".\n";

  top.toAbella = [anyTopCommand(kindDeclaration(newNames, k))];
  production newNames::[QName] =
      map(\ q::QName ->
            if q.isQualified
            then q
            else addQNameBase(top.currentModule, q.shortName),
          names);

  --redifining a previously-defined type from this module
  top.toAbellaMsgs <-
      foldr(\ q::QName rest::[Message] ->
              case lookupEnv(q, top.typeEnv) of
              | [] -> rest
              | _ ->
                errorMsg("Type " ++ justShow(q.pp) ++ " already " ++
                   "exists and cannot be defined again")::rest
              end,
            [], newNames);
  --two of the same name in this declaration
  top.toAbellaMsgs <-
      if length(names) == length(nub(names))
      then [] --no duplicates
      else [errorMsg("Cannot declare same type twice")];
  --check names are qualified with appropriate module
  top.toAbellaMsgs <-
      flatMap(\ q::QName ->
                if q.isQualified
                then if q.moduleName == top.currentModule
                     then []
                     else [errorMsg("Declared type name " ++
                              justShow(q.pp) ++ " does not have " ++
                              "correct module (expected " ++
                              justShow(top.currentModule.pp) ++ ")")]
                else [], names);

  top.provingTheorems = [];
}


abstract production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.pp = ppConcat([text("Type "), ppImplode(cat(text(","), line()),
                                       map((.pp), names)),
                     line(), ty.pp, text("."), realLine()]);
  local namesString_abella::String =
     if null(names)
     then ""
     else implode(", ", map((.abella_pp), names));
  top.abella_pp = "Type " ++ namesString_abella ++ "   " ++
                  ty.abella_pp ++ ".\n";

  top.toAbella =
      [anyTopCommand(typeDeclaration(newNames, ty.toAbella))];
  production newNames::[QName] =
      map(\ q::QName ->
            if q.isQualified
            then q
            else addQNameBase(top.currentModule, q.shortName),
          names);

  --redifining a previously-defined constructor from this module
  top.toAbellaMsgs <-
      foldr(\ q::QName rest::[Message] ->
              case lookupEnv(q, top.constructorEnv) of
              | [] -> rest
              | _ ->
                errorMsg("Constructor " ++ justShow(q.pp) ++
                   " already exists and cannot be defined again")::rest
              end,
            [], newNames);
  --two of the same name in this declaration
  top.toAbellaMsgs <-
      if length(names) == length(nub(names))
      then [] --no duplicates
      else [errorMsg("Cannot declare same constructor twice")];
  --check names are qualified with appropriate module
  top.toAbellaMsgs <-
      flatMap(\ q::QName ->
                if q.isQualified
                then if q.moduleName == top.currentModule
                     then []
                     else [errorMsg("Declared constructor name " ++
                              justShow(q.pp) ++ " does not have correct " ++
                              "module (expected " ++
                              justShow(top.currentModule.pp) ++ ")")]
                else [], names);
  --check it is defining a proof-level type
  top.toAbellaMsgs <-
      case last(ty.full.toList) of
      | arrowType(_, _) -> [] --not possible
      | ty ->
        let fullTy::TypeEnvItem =
            decorate ty.headConstructor with
            {typeEnv = top.typeEnv;}.fullType
        in
          if fullTy.isProofType
          then [] --fine to add
          else [errorMsg("Cannot add new constructor to type " ++
                         justShow(fullTy.name.pp))]
        end
      end;

  top.provingTheorems = [];
}


abstract production importCommand
top::TopCommand ::= name::String
{
  top.pp = cat(text("Import \"" ++ name ++ "\"."), realLine());
  top.abella_pp = justShow(top.pp);

  top.toAbella = [];
  top.toAbellaMsgs <- [errorMsg("Cannot import in Extensibella")];

  top.provingTheorems = [];
}
