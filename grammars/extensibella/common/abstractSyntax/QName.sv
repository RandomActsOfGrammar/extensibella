grammar extensibella:common:abstractSyntax;

{-
  We split into QName and SubQName to handle prefixes that may or may
  not occur at the beginning of a given QName.
-}

nonterminal QName with baseAdded<QName>, moduleName<QName>;
nonterminal SubQName with baseAdded<SubQName>, moduleName<SubQName>;
attribute
   pp, abella_pp,
   typeEnv, constructorEnv, relationEnv,
   shortName, isQualified,
   boundNames,
   addBase,
   typeErrors, typeFound, fullType,
   constrErrors, constrFound, fullConstr,
   relErrors, relFound, fullRel,
   compareTo, isEqual
occurs on QName, SubQName;
propagate typeEnv, constructorEnv, relationEnv on QName, SubQName;

synthesized attribute shortName::String;
synthesized attribute moduleName<a>::a;
synthesized attribute isQualified::Boolean;

--Put a new base name on the end (e.g. turn a:b:c into a:b:c:d)
inherited attribute addBase::String;
synthesized attribute baseAdded<a>::a;

--lookup as a type
synthesized attribute typeErrors::[Message];
synthesized attribute typeFound::Boolean;
synthesized attribute fullType::TypeEnvItem;

--lookup as a constructor
--can yield either a strict constructor or a relation, since those can
--   be used as arguments to relations (thus in Term) as well
synthesized attribute constrErrors::[Message];
synthesized attribute constrFound::Boolean;
synthesized attribute fullConstr::Either<RelationEnvItem ConstructorEnvItem>;

--lookup as a relation
synthesized attribute relErrors::[Message];
synthesized attribute relFound::Boolean;
synthesized attribute fullRel::RelationEnvItem;

--for internal use
synthesized attribute sub::SubQName occurs on QName;


abstract production baseName
top::SubQName ::= name::String
{
  top.pp = text(name);
  top.abella_pp = name;

  top.isQualified = false;
  top.shortName = name;
  top.moduleName = error("Cannot access moduleName if unqualified " ++
                         "(" ++ name ++ ")");

  top.baseAdded = addModule(name, baseName(top.addBase));

  --lookup name as a nonterminal
  production attribute possibleTys::[TypeEnvItem] =
     lookupEnv(basicQName(^top), top.typeEnv);
  top.typeErrors =
      case possibleTys of
      | [] -> [errorMsg("Unknown type " ++ name)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate type " ++ name ++ "; " ++
                  "possibilities are " ++
                  implode(", ", map(justShow, map((.pp),
                                map((.name), possibleTys)))))]
      end;
  top.typeFound = length(possibleTys) == 1;
  top.fullType =
      case possibleTys of
      | x::_ -> x
      | [] -> error("Could not find full type for " ++ name)
      end;

  --lookup name as a relation
  production attribute possibleRels::[RelationEnvItem] =
     lookupEnv(basicQName(^top), top.relationEnv);
  top.relErrors =
      case possibleRels of
      | [] -> [errorMsg("Unknown relation " ++ name)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate relation " ++ name ++
                  "; possibilities are " ++
                  implode(", ", map(justShow, map((.pp),
                                map((.name), possibleRels)))))]
      end;
  top.relFound = length(possibleRels) == 1;
  top.fullRel =
      case possibleRels of
      | x::_ -> x
      | [] -> error("Could not find full relation for " ++ name)
      end;

  --lookup name as a constructor
  --any time we can use a constructor, we can also use a relation,
  --   so include them
  --filter out unknown constructors, since we don't mean them when we
  --   look up a constructor
  production attribute possibleConstrs::[ConstructorEnvItem] =
     filter(\ c::ConstructorEnvItem ->
              case c.name of
              | unknownIQName(_) -> false
              | unknownKQName(_) -> false
              | _ -> true
              end,
        lookupEnv(basicQName(^top), top.constructorEnv));
  top.constrErrors =
      case possibleConstrs, possibleRels of
      | [], [] -> [errorMsg("Unknown constant " ++ name)]
      | [_], [] -> []
      | [], [_] -> []
      | l1, l2 ->
        [errorMsg("Indeterminate constant " ++ name ++ "; " ++
            "possibilities are " ++
            implode(", ", map(justShow,
                map((.pp), map((.name), l1) ++ map((.name), l2)))))]
      end;
  top.constrFound =
      length(possibleConstrs) + length(possibleRels) == 1;
  top.fullConstr =
      case possibleConstrs, possibleRels of
      | x::_, _ -> right(x)
      | _, x::_ -> left(x)
      | [], [] ->
        error("Could not find full constructor for " ++ name)
      end;

  propagate compareTo, isEqual;
}


abstract production addModule
top::SubQName ::= name::String rest::SubQName
{
  top.pp = ppConcat([text(name), text(":"), rest.pp]);
  top.abella_pp = name ++ name_sep ++ rest.abella_pp;

  local showed::String = justShow(top.pp);

  top.isQualified = true;
  top.shortName = rest.shortName;
  top.moduleName = case rest of
                   | baseName(_) -> baseName(name)
                   | _ -> addModule(name, rest.moduleName)
                   end;

  rest.addBase = top.addBase;
  top.baseAdded = addModule(name, rest.baseAdded);

  --lookup name as a nonterminal
  production attribute possibleTys::[TypeEnvItem] =
     lookupEnv(basicQName(^top), top.typeEnv);
  top.typeErrors =
      case possibleTys of
      | [] -> [errorMsg("Unknown type " ++ showed)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate type " ++ showed ++ "; " ++
                  "possibilities are " ++
                  implode(", ", map(justShow, map((.pp),
                                map((.name), possibleTys)))))]
      end;
  top.typeFound = length(possibleTys) == 1;
  top.fullType =
      case possibleTys of
      | x::_ -> x
      | [] -> error("Could not find full type for " ++ showed)
      end;

  --lookup name as a relation
  production attribute possibleRels::[RelationEnvItem] =
     lookupEnv(basicQName(^top), top.relationEnv);
  top.relErrors =
      case possibleRels of
      | [] -> [errorMsg("Unknown relation " ++ showed)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate relation " ++ showed ++
                  "; possibilities are " ++
                  implode(", ", map(justShow, map((.pp),
                                map((.name), possibleRels)))))]
      end;
  top.relFound = length(possibleRels) == 1;
  top.fullRel =
      case possibleRels of
      | x::_ -> x
      | [] -> error("Could not find full relation for " ++ showed)
      end;

  --lookup name as a constructor
  --any time we can use a constructor, we can also use a relation,
  --   so include them
  --filter out unknown constructors, since we don't mean them when we
  --   look up a constructor
  production attribute possibleConstrs::[ConstructorEnvItem] =
     filter(\ c::ConstructorEnvItem ->
              case c.name of
              | unknownIQName(_) -> false
              | unknownKQName(_) -> false
              | _ -> true
              end,
        lookupEnv(basicQName(^top), top.constructorEnv));
  top.constrErrors =
      case possibleConstrs, possibleRels of
      | [], [] -> [errorMsg("Unknown constant " ++ showed)]
      | [_], [] -> []
      | [], [_] -> []
      | l1, l2 ->
        [errorMsg("Indeterminate constant " ++ showed ++ "; " ++
            "possibilities are " ++
            implode(", ", map(justShow,
                map((.pp), map((.name), l1) ++ map((.name), l2)))))]
      end;
  top.constrFound =
      length(possibleConstrs) + length(possibleRels) == 1;
  top.fullConstr =
      case possibleConstrs, possibleRels of
      | x::_, _ -> right(x)
      | _, x::_ -> left(x)
      | [], [] ->
        error("Could not find full constructor for " ++ showed)
      end;

  propagate compareTo, isEqual;
}




{-
  We only check the SubQName for equality because the user never
  enters the prefix, and indeed cannot enter it.
-}
--fixed relations from a language
abstract production fixQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$fix__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = fixQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = ^rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--extensible relations from a language
abstract production extQName
top::QName ::= pc::Integer rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$ext__" ++ toString(pc) ++ "__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = extQName(pc, rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = ^rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--projection relations
abstract production projQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$proj__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = projQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = ^rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--types defined in a language
abstract production tyQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$ty__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = tyQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = ^rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--constructor standing in for those from unknown modules
abstract production unknownIQName
top::QName ::= rest::QName
{
  top.pp = rest.pp;
  top.abella_pp = "$unknownI__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = rest.moduleName;

  rest.addBase = top.addBase;
  top.baseAdded = unknownIQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = rest.sub;

  rest.compareTo =
       case top.compareTo of
       | unknownIQName(r) -> r
       | x -> x
       end;
  top.isEqual = rest.isEqual;
}
abstract production unknownKQName
top::QName ::= rest::QName
{
  top.pp = rest.pp;
  top.abella_pp = "$unknownK__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = rest.moduleName;

  rest.addBase = top.addBase;
  top.baseAdded = unknownKQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = rest.sub;

  rest.compareTo =
       case top.compareTo of
       | unknownKQName(r) -> r
       | x -> x
       end;
  top.isEqual = rest.isEqual;
}


--extension size of relation rest
abstract production extSizeQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$extSize__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = extSizeQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = ^rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--projection version of relation rest
abstract production projRelQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$projRel__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = projRelQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = ^rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--anything from the standard library
abstract production libQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$lib__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = libQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = ^rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--special definition for passing along stand-in rule
--rest is the relation for which the stand-in rule is being defined
abstract production standInRuleQName
top::QName ::= rest::QName
{
  top.abella_pp = "$stand-in_rule__" ++ rest.abella_pp;
  top.isStandInRuleQName = true;
  forwards to @rest;
}
synthesized attribute isStandInRuleQName::Boolean occurs on QName;
aspect default production
top::QName ::=
{
  top.isStandInRuleQName = false;
}


--anything without a prefix
abstract production basicQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = basicQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = ^rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}





function addQNameBase
QName ::= module::QName name::String
{
  module.addBase = name;
  return module.baseAdded;
}


--identifier must be fully-qualified
function sameModule
Boolean ::= moduleName::QName identifier::QName
{
  return if !identifier.isQualified
         then error("Identifier must be qualified (" ++
                    justShow(identifier.pp) ++ ")")
         else addQNameBase(^moduleName, identifier.shortName) ==
              basicQName(identifier.sub); --drop any special qualifiers
}


function toQName
QName ::= name::String
{
  --choose splitter based on whether it uses colons
  local splitter::String =
      if indexOf(":", name) >= 0 then ":" else name_sep;
  local buildSub::(SubQName ::= Integer String) =
      \ i::Integer name::String ->
        foldrLastElem(addModule, baseName,
           explode(splitter, substring(i, length(name), name)));
  return
      if startsWith("$fix__", name)
      then fixQName(buildSub(6, name))
      else if startsWith("$ext__", name)
      then let shortened::String = substring(6, length(name), name)
           in
           let stop::Integer = indexOf("__", shortened)
           in
           let pc::Integer = toInteger(substring(0, stop, shortened))
           in
             extQName(pc, buildSub(stop + 2, shortened))
           end end end
      else if startsWith("$proj__", name)
      then projQName(buildSub(7, name))
      else if startsWith("$ty__", name)
      then tyQName(buildSub(5, name))
      else if startsWith("$lib__", name)
      then libQName(buildSub(6, name))
      else if startsWith("$unknownI__", name)
      then unknownIQName(toQName(substring(11, length(name), name)))
      else if startsWith("$unknownK__", name)
      then unknownKQName(toQName(substring(11, length(name), name)))
      else if startsWith("$extSize__", name)
      then extSizeQName(buildSub(10, name))
      else if startsWith("$projRel__", name)
      then projRelQName(buildSub(10, name))
      else if startsWith("$stand-in_rule__", name)
      then standInRuleQName(toQName(substring(16, length(name), name)))
      else basicQName(buildSub(0, name));
}
