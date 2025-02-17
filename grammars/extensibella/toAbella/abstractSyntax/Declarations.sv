grammar extensibella:toAbella:abstractSyntax;


nonterminal Kind with pp, abella_pp, len;

abstract production typeKind
top::Kind ::=
{
  top.pp = text("type");
  top.abella_pp = "type";

  top.len = 0;
}


abstract production arrowKind
top::Kind ::= k::Kind
{
  top.pp = cat(text("type -> "), k.pp);
  top.abella_pp = "type -> " ++ k.abella_pp;

  top.len = 1 + k.len;
}





attribute
   toAbella<Type>, toAbellaMsgs
occurs on Type;
propagate toAbellaMsgs on Type;

aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.toAbella = arrowType(ty1.toAbella, ty2.toAbella);
}


aspect production nameType
top::Type ::= name::QName
{
  top.toAbella = name.fullType.type;
}


aspect production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.toAbella = functorType(functorTy.toAbella, argTy.toAbella);
}


aspect production varType
top::Type ::= name::String
{
  top.toAbella = ^top;
}


aspect production errorType
top::Type ::=
{
  top.toAbella = error("errorType.toAbella");
}


attribute
   toAbella<TypeList>, toAbellaMsgs
occurs on TypeList;
propagate toAbellaMsgs on TypeList;

aspect production emptyTypeList
top::TypeList ::=
{
  top.toAbella = emptyTypeList();
}


aspect production addTypeList
top::TypeList ::= ty::Type rest::TypeList
{
  top.toAbella = addTypeList(ty.toAbella, rest.toAbella);
}


attribute
   toAbella<MaybeType>, toAbellaMsgs
occurs on MaybeType;
propagate toAbellaMsgs on MaybeType;

aspect production nothingType
top::MaybeType ::=
{
  top.toAbella = nothingType();
}


aspect production justType
top::MaybeType ::= ty::Type
{
  top.toAbella = justType(ty.toAbella);
}





nonterminal Defs with
   pps, abella_pp,
   toAbella<Defs>, toAbellaMsgs,
   toList<Def>, len,
   relationClauseModules,
   beingDefined,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          proverState, toAbellaMsgs, beingDefined on Defs;

inherited attribute beingDefined::[(QName, Type)];

abstract production singleDefs
top::Defs ::= d::Def
{
  top.pps = [d.pp];
  top.abella_pp = d.abella_pp;

  top.toAbella = singleDefs(d.toAbella);

  top.relationClauseModules = d.relationClauseModules;

  top.toList = [^d];
  top.len = 1;
}


abstract production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.pps = d.pp::rest.pps;
  top.abella_pp = d.abella_pp ++ ";\n" ++ rest.abella_pp;

  top.toAbella = consDefs(d.toAbella, rest.toAbella);

  top.relationClauseModules =
      d.relationClauseModules ++ rest.relationClauseModules;

  top.toList = ^d::rest.toList;
  top.len = 1 + rest.len;
}





nonterminal Def with
   pp, abella_pp,
   toAbella<Def>, toAbellaMsgs,
   relationClauseModules,
   beingDefined, defRel, defTuple,
   typeEnv, constructorEnv, relationEnv, proverState, currentModule;
propagate typeEnv, constructorEnv, relationEnv, proverState,
          currentModule, toAbellaMsgs, beingDefined on Def;

synthesized attribute defRel::QName;
synthesized attribute defTuple::([Term], Maybe<Metaterm>);

abstract production factDef
top::Def ::= defRel::QName args::TermList
{
  top.pp = foldr1(\ d::Document rest::Document ->
                    docGroup(d ++ line() ++ rest),
                  defRel.pp::args.pps);
  top.abella_pp = defRel.abella_pp ++ " " ++ args.abella_pp;

  args.boundNames =
      filter(\ s::String -> isCapitalized(s), args.usedNames);

  top.toAbella = factDef(head(foundDef).1, args.toAbella);

  top.toAbellaMsgs <-
      case foundDef of
      | [] -> [errorMsg("Relation " ++ justShow(defRel.pp) ++
                  " is not being defined")]
      | [_] -> []
      | l ->
        [errorMsg("Cannot determine which relation " ++
            justShow(defRel.pp) ++
            " is being defined; possibilities are: " ++
            implode(", ", map(justShow, map((.pp), map(fst, l)))))]
      end;

  production foundDef::[(QName, Type)] =
      flatMap(\ p::(QName, Type) ->
                if defRel.isQualified
                then if p.1 == ^defRel then [p] else []
                else if p.1.shortName == defRel.shortName
                     then [p] else [],
              top.beingDefined);

  top.relationClauseModules =
      case foundDef of
      | [(extQName(pc, sub), ty)] ->
        let fullList::[Term] = args.full.toList
        in
          if length(fullList) < pc
          then []
          else case elemAtIndex(fullList, pc).headRel of
               | just(x) -> [(extQName(pc, ^sub), x.moduleName)]
               | nothing() -> []
               end
        end
      | [(projQName(sub), ty)] ->
        let fullList::[Term] = args.full.toList
        in
          case elemAtIndex(fullList, length(fullList) - 2).headRel of
          | just(x) -> [(projQName(^sub), x.moduleName)]
          | nothing() -> []
          end
        end
      | _ -> []
      end;

  top.defRel = if defRel.isQualified
               then ^defRel
               else addQNameBase(top.currentModule, defRel.shortName);
  top.defTuple = (args.toList, nothing());
}


abstract production ruleDef
top::Def ::= defRel::QName args::TermList body::Metaterm
{
  top.pp = foldr1(\ d::Document rest::Document ->
                    docGroup(d ++ line() ++ rest),
                  defRel.pp::args.pps) ++ text(" :=") ++
           nest(2, line() ++ docGroup(body.pp));
  top.abella_pp = defRel.abella_pp ++ " " ++ args.abella_pp ++
                  " := " ++ body.abella_pp;

  local boundNames::[String] =
      filter(\ s::String -> isCapitalized(s), args.usedNames);
  args.boundNames = boundNames;
  body.boundNames = boundNames;

  top.toAbella =
      ruleDef(head(foundDef).1, args.toAbella, body.toAbella);

  top.toAbellaMsgs <-
      case foundDef of
      | [] -> [errorMsg("Relation " ++ justShow(defRel.pp) ++
                  " is not being defined")]
      | [_] -> []
      | l ->
        [errorMsg("Cannot determine which relation " ++
            justShow(defRel.pp) ++
            " is being defined; possibilities are: " ++
            implode(", ", map(justShow, map((.pp), map(fst, l)))))]
      end;

  production foundDef::[(QName, Type)] =
      flatMap(\ p::(QName, Type) ->
                if defRel.isQualified
                then if p.1 == ^defRel then [p] else []
                else if p.1.shortName == defRel.shortName
                     then [p] else [],
              top.beingDefined);

  top.relationClauseModules =
      case foundDef of
      | [(extQName(pc, sub), ty)] ->
        let fullList::[Term] = args.full.toList
        in
          if length(fullList) < pc
          then []
          else case elemAtIndex(fullList, pc).headRel of
               | just(x) -> [(extQName(pc, ^sub), x.moduleName)]
               | nothing() -> []
               end
        end
      | [(projQName(sub), ty)] ->
        let fullList::[Term] = args.full.toList
        in
          case elemAtIndex(fullList, length(fullList) - 2).headRel,
               body of
          | _, falseMetaterm() ->
            --placeholder clause because we can't have empty relations
            []
          | just(x), _ -> [(projQName(^sub), x.moduleName)]
          | nothing(), _ -> []
          end
        end
      | _ -> []
      end;

  top.defRel = if defRel.isQualified
               then ^defRel
               else addQNameBase(top.currentModule, defRel.shortName);
  top.defTuple = (args.toList, just(^body));
}
