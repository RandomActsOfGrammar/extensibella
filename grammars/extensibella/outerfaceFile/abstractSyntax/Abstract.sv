grammar extensibella:outerfaceFile:abstractSyntax;

imports extensibella:common:abstractSyntax;
imports extensibella:toAbella:abstractSyntax;

imports silver:langutil:pp;
imports silver:langutil only pp, pps;



function processModuleOuterfaces
([DefElement], [ThmElement]) ::= mods::[(QName, Outerface)]
{
  local allDefs::[DefElement] =
      flatMap((.defElements), map(snd, mods));
  local allThms::[(QName, [ThmElement])] =
      map(\ p::(QName, Outerface) -> (p.1, p.2.thmElements),
          mods);
  local sortedThms::[(QName, [ThmElement])] =
      sortBy(\ p1::(QName, [ThmElement]) p2::(QName, [ThmElement]) ->
               justShow(p1.1.pp) < justShow(p2.1.pp), allThms);
  local justThms::[[ThmElement]] = map(snd, sortedThms);
  local finalThms::[ThmElement] = combineAllThms(justThms);
  return (allDefs, finalThms);
}



function combineAllThms
[ThmElement] ::= modThms::[[ThmElement]]
{
  local firsts::[ThmElement] = map(head, modThms);
  local rests::[[ThmElement]] = map(tail, modThms);
  local first::ThmElement =
      getFirst(tail(firsts), head(firsts), rests);
  local cleaned::[[ThmElement]] = cleanModThms(first, modThms);
  return
     case modThms of
     | [] -> []
     | [l] -> l
     | _ -> first::combineAllThms(cleaned)
     end;
}


function getFirst
ThmElement ::= modThms::[ThmElement] thusFar::ThmElement
             --rest of ThmElements in all modules (drops first one)
               fullRestMods::[[ThmElement]]
{
  return
      case modThms, thusFar of
      | [], x -> x
      --things without extended proofs first
      | _::_, nonextensibleTheorem(_, _, _)
        when !existsLater(thusFar, fullRestMods) -> thusFar
      | nonextensibleTheorem(_, _, _)::_, _
        when !existsLater(head(modThms), fullRestMods) ->
        head(modThms)
      | _::_, splitElement(_, _)
        when !existsLater(thusFar, fullRestMods) -> thusFar
      | splitElement(_, _)::_, _
        when !existsLater(head(modThms), fullRestMods) ->
        head(modThms)
      --anything at this point is extensible
      | t::r, _ when existsLater(thusFar, fullRestMods) ->
        --can't take thusFar yet, so try again
        getFirst(r, t, fullRestMods)
      | t::r, _ ->
        --thusFar is still valid, but keep going in case there is
        --   something non-extensible later
        getFirst(r, thusFar, fullRestMods)
      end;
}

--check if t is anywhere in rest
function existsLater
Boolean ::= t::ThmElement rest::[[ThmElement]]
{
  return any(map(containsBy(equalish, t, _), rest));
}

--test if two ThmElements are for the same thing
function equalish
Boolean ::= a::ThmElement b::ThmElement
{
  return
      case a, b of
      | nonextensibleTheorem(na, _, _),
        nonextensibleTheorem(nb, _, _) -> na == nb
      | splitElement(an, alst), splitElement(bn, blst) ->
        an == bn && alst == blst
      | extensibleMutualTheoremGroup(athms, _),
        extensibleMutualTheoremGroup(bthms, _) ->
        --thms intersect; can ignore alsos because thms must exist first
        !null(intersect(map(fst, athms), map(fst, bthms)))
      | translationConstraintTheorem(an, _, _),
        translationConstraintTheorem(bn, _, _) -> an == bn
      | extIndElement(ar), extIndElement(br) ->
        !null(intersect(map(fst, ar), map(fst, br)))
      | _, _ -> false
      end;
}


function cleanModThms
[[ThmElement]] ::= remove::ThmElement modThms::[[ThmElement]]
{
  --whether to remove the first thing in the first list
  local removeFirst::Boolean =
      case head(head(modThms)), remove of
      | splitElement(aname, alst), splitElement(bname, blst) ->
        aname == bname && alst == blst
      | nonextensibleTheorem(aname, aparams, astmt),
        nonextensibleTheorem(bname, bparams, bstmt) ->
        aname == bname
      | extensibleMutualTheoremGroup(athms, _),
        extensibleMutualTheoremGroup(bthms, _) ->
        --need to check thms only, not alsos, because thms must be
        --present to add alsos
        !null(intersect(map(fst, athms), map(fst, bthms)))
      | translationConstraintTheorem(aname, abinds, abody),
        translationConstraintTheorem(bname, bbinds, bbody) ->
        aname == bname
      | extIndElement(arelinfo), extIndElement(brelinfo) ->
        !null(intersect(map(fst, arelinfo), map(fst, brelinfo)))
      | _, _ -> false
      end;
  return case modThms of
         | [] -> []
         | [_]::tl when removeFirst ->
           cleanModThms(remove, tl)
         | (_::rest)::tl when removeFirst ->
           rest::cleanModThms(remove, tl)
         | hd::tl -> --!removeFirst
           hd::cleanModThms(remove, tl)
         end;
}



synthesized attribute defElements::[DefElement];
synthesized attribute thmElements::[ThmElement];

nonterminal Outerface with pp, len, defElements, thmElements;

abstract production outerface
top::Outerface ::= t::TopCommands
{
  top.pp = t.pp;
  top.len = t.len;

  top.defElements = t.defElements;
  top.thmElements = t.thmElements;
}





nonterminal TopCommands with pp, len, defElements, thmElements;

abstract production endTopCommands
top::TopCommands ::=
{
  top.pp = text("");
  top.len = 0;

  top.defElements = [];
  top.thmElements = [];
}


abstract production addTopCommands
top::TopCommands ::= t::TopCommand rest::TopCommands
{
  top.pp = t.pp ++ rest.pp;
  top.len = 1 + rest.len;

  top.defElements = t.defElements ++ rest.defElements;
  top.thmElements = t.thmElements ++ rest.thmElements;
}





attribute
   defElements, thmElements
occurs on TopCommand;

aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.defElements = [];
  top.thmElements = [nonextensibleTheorem(name, params, body)];
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.defElements = [defineElement(preds, defs.defClauses)];
  top.thmElements = [];
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.defElements = [codefineElement(preds, defs.defClauses)];
  top.thmElements = [];
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.defElements =
      error("Should not have query command in interface file");
  top.thmElements =
      error("Should not have query command in interface file");
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  top.defElements = [];
  top.thmElements = [splitElement(theoremName, newTheoremNames)];
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.defElements = [];
  top.thmElements = [];
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.defElements = [kindElement(names, k)];
  top.thmElements = [];
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.defElements = [typeElement(names, ty)];
  top.thmElements = [];
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.defElements = [];
  top.thmElements = [];
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.defElements = [];
  top.thmElements = [extensibleMutualTheoremGroup(thms.thmInfo,
                                                  alsos.thmInfo)];
}


aspect production proveObligations
top::TopCommand ::= names::[QName]
{
  top.defElements =
      error("Should not have proveObligations in interface file");
  top.thmElements =
      error("Should not have proveObligations in interface file");
}


aspect production translationConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.defElements = [];
  top.thmElements = [translationConstraintTheorem(name, binds, body)];
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  top.defElements =
      error("Should not have proveConstraint in interface file");
  top.thmElements =
      error("Should not have proveConstraint in interface file");
}


aspect production extIndDeclaration
top::TopCommand ::= e::ExtIndBody
{
  top.defElements = [];
  top.thmElements = [extIndElement(e.extIndInfo)];
}


aspect production proveExtInd
top::TopCommand ::= rels::[QName]
{
  top.defElements =
      error("Should not have proveExtInd in interface file");
  top.thmElements =
      error("Should not have proveExtInd in interface file");
}





attribute
   thmInfo
occurs on ExtThms;

synthesized attribute thmInfo::[(QName, Bindings, ExtBody, String, Maybe<String>)];

aspect production endExtThms
top::ExtThms ::=
{
  top.thmInfo = [];
}


aspect production addExtThms
top::ExtThms ::= name::QName bindings::Bindings body::ExtBody
                 onLabel::String asName::Maybe<String> rest::ExtThms
{
  top.thmInfo = (name, bindings, body, onLabel, asName)::rest.thmInfo;
}





attribute
   defClauses
occurs on Defs, Def;

synthesized attribute defClauses::[(QName, TermList, Maybe<Metaterm>)];

aspect production singleDefs
top::Defs ::= d::Def
{
  top.defClauses = d.defClauses;
}


aspect production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.defClauses = d.defClauses ++ rest.defClauses;
}



aspect production factDef
top::Def ::= q::QName args::TermList
{
  top.defClauses = [(q, args, nothing())];
}


aspect production ruleDef
top::Def ::= q::QName args::TermList body::Metaterm
{
  top.defClauses = [(q, args, just(body))];
}
