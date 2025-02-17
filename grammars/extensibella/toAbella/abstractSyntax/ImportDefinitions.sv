grammar extensibella:toAbella:abstractSyntax;

{-
  This file is to allow us to read in definitions from Abella files.
  We want to read the file in, parse it, then run through it to gather
  the language information.

  We do this in a separate file because the attributes here have to do
  with reading a file, not proving as we see in the other files.
-}



nonterminal ListOfCommands with
   pp, abella_pp,
   ignoreDefErrors,
   typeEnv, relationEnv, constructorEnv, proverState, currentModule,
   commandList, tys, rels, constrs,
   newMutualRelGroups,
   declaredThms,
   interactive;
propagate proverState, currentModule, ignoreDefErrors,
          interactive on ListOfCommands;

synthesized attribute commandList::[AnyCommand];

synthesized attribute tys::[TypeEnvItem];
synthesized attribute rels::[RelationEnvItem];
synthesized attribute constrs::[ConstructorEnvItem];

--groups of relations defined together in a mutual group
synthesized attribute newMutualRelGroups::[[QName]];

synthesized attribute declaredThms::[(QName, Metaterm)];


abstract production emptyListOfCommands
top::ListOfCommands ::=
{
  top.pp = text("");
  top.abella_pp = "";

  top.commandList = [];

  top.tys = [];
  top.rels = [];
  top.constrs = [];

  top.newMutualRelGroups = [];

  top.declaredThms = [];
}


abstract production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.pp = docGroup(a.pp) ++ rest.pp;
  top.abella_pp = a.abella_pp ++ rest.abella_pp;

  top.commandList = ^a::rest.commandList;

  top.tys = a.tys ++ rest.tys;
  top.rels = a.rels ++ rest.rels;
  top.constrs = a.constrs ++ rest.constrs;

  top.newMutualRelGroups =
      a.newMutualRelGroups ++ rest.newMutualRelGroups;

  a.typeEnv = top.typeEnv;
  a.relationEnv = top.relationEnv;
  a.constructorEnv = top.constructorEnv;

  rest.typeEnv = addEnv(top.typeEnv, a.tys);
  rest.relationEnv = addEnv(top.relationEnv, a.rels);
  rest.constructorEnv = addEnv(top.constructorEnv, a.constrs);

  top.declaredThms = a.declaredThms ++ rest.declaredThms;
}





attribute
   ignoreDefErrors,
   tys, rels, constrs,
   newMutualRelGroups,
   declaredThms
occurs on AnyCommand;
propagate ignoreDefErrors on AnyCommand;

aspect production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.tys = c.tys;
  top.rels = c.rels;
  top.constrs = c.constrs;

  top.newMutualRelGroups = c.newMutualRelGroups;

  --filter out anything containing dollar signs
  top.declaredThms =
      filter(\ p::(QName, Metaterm) ->
               indexOf("$", p.1.shortName) == -1,
             c.provingTheorems);
}


aspect production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];

  top.newMutualRelGroups = [];

  top.declaredThms = [];
}


aspect production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];

  top.newMutualRelGroups = [];

  top.declaredThms = [];
}


aspect production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];

  top.newMutualRelGroups = [];

  top.declaredThms = [];
}





attribute
   ignoreDefErrors,
   tys, rels, constrs,
   newMutualRelGroups
occurs on TopCommand;

aspect default production
top::TopCommand ::=
{
  top.newMutualRelGroups = [];
}

aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.tys =
      flatMap(\ p::(QName, Type) ->
                case p.1 of
                | projQName(s) ->
                  [langTypeEnvItem(tyQName(^s), 0,
                      foldr(addTypeList, emptyTypeList(),
                        --drop `ty -> ty -> prop` from end to get args
                         take(length(p.2.toList) - 3, p.2.toList)),
                      map(snd,
                          filter(\ inner::(QName, QName) ->
                                   p.1 == inner.1,
                                 defs.relationClauseModules)))]
                | _ -> []
                end,
              preds);
  top.rels =
      --only output rels if no errors or this is a module
      --  specification, so we can avoid error checking
      --also only output if this isn't a stand-in rule
      if (top.ignoreDefErrors ||
          !any(map((.isError), top.toAbellaMsgs))) &&
         !head(preds).1.isStandInRuleQName
      then flatMap(\ p::(QName, Type) ->
                     case p.1 of
                     | extQName(pc, s) ->
                       [extRelationEnvItem(p.1,
                           foldr(addTypeList, emptyTypeList(), p.2.toList),
                           pc, map(snd,
                                   filter(\ inner::(QName, QName) ->
                                            p.1 == inner.1,
                                          defs.relationClauseModules)),
                           flatMap(\ d::Def ->
                                     if decorate d with {
                                           currentModule=top.currentModule;
                                        }.defRel == p.1
                                     then [d.defTuple] else [],
                                   defs.toList))]
                     | projQName(_) -> []
                     | _ ->
                       [fixedRelationEnvItem(p.1,
                           foldr(addTypeList, emptyTypeList(), p.2.toList))]
                     end,
                   fullNames)
      else [];
  top.constrs = [];

  top.newMutualRelGroups = [map(fst, preds)];
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.tys = []; --no tys from codefinitions
  top.rels =
      --only output rels if no errors or this is a module
      --specification, so we can avoid error checking
      if top.ignoreDefErrors || !any(map((.isError), top.toAbellaMsgs))
      then flatMap(\ p::(QName, Type) ->
                     case p.1 of
                     | extQName(pc, s) ->
                       [extRelationEnvItem(p.1,
                           foldr(addTypeList, emptyTypeList(), p.2.toList),
                           pc, error("codefinitionDeclarationClauseModules"),
                           error("codefinitionDeclarationDefs"))]
                     | projQName(_) -> []
                     | _ ->
                       [fixedRelationEnvItem(p.1,
                           foldr(addTypeList, emptyTypeList(), p.2.toList))]
                     end,
                   preds)
      else [];
  top.constrs = [];
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.tys =
      --only output tys if no errors or this is a module
      --specification, so we can avoid error checking
      if top.ignoreDefErrors || !any(map((.isError), top.toAbellaMsgs))
      then flatMap(\ q::QName ->
                     case q of
                     --get these from projection definitions
                     | tyQName(s) -> []
                     | _ -> [proofTypeEnvItem(q, k.len)]
                     end,
                   names)
      else [];
  top.rels = [];
  top.constrs = [];
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.tys = [];
  top.rels = [];
  top.constrs =
      --only output constrs if no errors or this is a module
      --specification, so we can avoid error checking
      if top.ignoreDefErrors || !any(map((.isError), top.toAbellaMsgs))
      then map(constructorEnvItem(_,
                  last(ty.toList),
                  foldr(addTypeList, emptyTypeList(),
                        take(length(ty.toList) - 1, ty.toList))),
               names)
      else [];
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production proveObligations
top::TopCommand ::= names::[QName] newThms::ExtThms newAlsos::ExtThms
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production projectionConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production extIndDeclaration
top::TopCommand ::=  body::ExtIndBody thms::ExtThms also::ExtThms
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production proveExtInd
top::TopCommand ::= rels::[QName] oldThms::[QName] newRels::ExtIndBody
                    newThms::ExtThms newAlsos::ExtThms
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production extSizeDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production addExtSize
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production projRelDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}


aspect production addProjRel
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.tys = [];
  top.rels = [];
  top.constrs = [];
}
