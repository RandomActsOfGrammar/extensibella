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
  local first::ThmElement =
      getFirst(tail(firsts), head(firsts));
  local cleaned::[[ThmElement]] = cleanModThms(^first, modThms);
  return
     case modThms of
     | [] -> []
     | [l] -> l
     | _ -> ^first::combineAllThms(cleaned)
     end;
}


function getFirst
ThmElement ::= modThms::[ThmElement] thusFar::ThmElement
{
  {-
    We assume modThms is in the linearized order of imports, that is,
    if module M builds on module I, the first item remaining in M's
    order is earlier in modThms than the first item remaining in I's
    order.  If the first items in both orders are non-extensible, the
    one from M might depend on the one from I as the one from I was in
    the context when it was written.  Thus we need to take the *last*
    non-extensible thing we find, not the first.
  -}
  return
      case modThms of
      | [] -> ^thusFar
      | x::rest when x.is_nonextensible ->
        getFirst(rest, x)
      | x::rest when thusFar.is_nonextensible ->
        getFirst(rest, ^thusFar)
      --anything at this point is extensible, so earlier tag
      | t::r when lessTags(t.tag, thusFar.tag) ->
        --thusFar isn't minimum, so start with t
        getFirst(r, t)
      --same tags, so unify the two before continuing
      | t::r when equalTags(t.tag, thusFar.tag) ->
        getFirst(r, unionThmElements(t, ^thusFar))
      | t::r ->
        --thusFar is still minimum seen, so continue with it
        getFirst(r, ^thusFar)
      end;
}

--compare two tags, returning true if ta < tb
function lessTags
Boolean ::= ta::Tag tb::Tag
{
       --lower whole number
  return ta.1 < tb.1 ||
       --same whole number and lower fraction
         (ta.1 == tb.1 && ta.2 * tb.3 < tb.2 * ta.3) ||
       --same number and lower name
         (ta.1 == tb.1 && ta.2 == tb.2 && ta.3 == tb.3 &&
          ta.4 < tb.4);
}

function equalTags
Boolean ::= ta::Tag tb::Tag
{
       --same number and same name
  return ta.1 == tb.1 && ta.2 * tb.3 == tb.2 * ta.3 && ta.4 == tb.4;
}


--take two things with the same tag and combine them
--e.g. extensible theorem groups where some module adds new ones
function unionThmElements
ThmElement ::= a::ThmElement b::ThmElement
{
  return case a, b of
         | extensibleMutualTheoremGroup(athms, aalsos, atag),
           extensibleMutualTheoremGroup(bthms, balsos, btag) ->
           let addthms::[(QName, Bindings, ExtBody, InductionOns)] =
               filter(\ p::(QName, Bindings, ExtBody, InductionOns) ->
                        !containsBy(
                            \ p1::(QName, Bindings, ExtBody, InductionOns)
                              p2::(QName, Bindings, ExtBody, InductionOns) ->
                              p1.1 == p2.1,
                            p, athms),
                      bthms)
           in
           let addalsos::[(QName, Bindings, ExtBody, InductionOns)] =
               filter(\ p::(QName, Bindings, ExtBody, InductionOns) ->
                        !containsBy(
                            \ p1::(QName, Bindings, ExtBody, InductionOns)
                              p2::(QName, Bindings, ExtBody, InductionOns) ->
                              p1.1 == p2.1,
                            p, aalsos),
                      balsos)
           in
             extensibleMutualTheoremGroup(athms ++ addthms,
                aalsos ++ addalsos, atag)
           end end
         | extIndElement(arelinfo, athms, aalsos, atag),
           extIndElement(brelinfo, bthms, balsos, btag) ->
           let addrels::[(QName, [String], Bindings, ExtIndPremiseList, [String])] =
               filter(\ p::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
                        !containsBy(
                            \ p1::(QName, [String], Bindings, ExtIndPremiseList, [String])
                              p2::(QName, [String], Bindings, ExtIndPremiseList, [String]) ->
                              p1.1 == p2.1,
                            p, arelinfo),
                      brelinfo)
           in
           let addthms::[(QName, Bindings, ExtBody, InductionOns)] =
               filter(\ p::(QName, Bindings, ExtBody, InductionOns) ->
                        !containsBy(
                            \ p1::(QName, Bindings, ExtBody, InductionOns)
                              p2::(QName, Bindings, ExtBody, InductionOns) ->
                              p1.1 == p2.1,
                            p, athms),
                      bthms)
           in
           let addalsos::[(QName, Bindings, ExtBody, InductionOns)] =
               filter(\ p::(QName, Bindings, ExtBody, InductionOns) ->
                        !containsBy(
                            \ p1::(QName, Bindings, ExtBody, InductionOns)
                              p2::(QName, Bindings, ExtBody, InductionOns) ->
                              p1.1 == p2.1,
                            p, aalsos),
                      balsos)
           in
             extIndElement(arelinfo ++ addrels, athms ++ addthms,
                           aalsos ++ addalsos, atag)
           end end end
         | extSizeElement(arels, atag), extSizeElement(brels, btag) ->
           let addrels::[(QName, [String])] =
               filter(\ p::(QName, [String]) ->
                        !containsBy(\ p1::(QName, [String])
                                      p2::(QName, [String]) -> p1.1 == p2.1,
                            p, arels),
                      brels)
           in
             extSizeElement(arels ++ addrels, atag)
           end
         | projRelElement(arels, atag), projRelElement(brels, btag) ->
           let addrels::[(QName, [String])] =
               filter(\ p::(QName, [String]) ->
                        !containsBy(\ p1::(QName, [String])
                                      p2::(QName, [String]) -> p1.1 == p2.1,
                            p, arels),
                      brels)
           in
             projRelElement(arels ++ addrels, atag)
           end
         | projectionConstraintTheorem(_, _, _, _),
           projectionConstraintTheorem(_, _, _, _) ->
           ^a --can't extend with new, but is still labeled extensible
         | _, _ ->
           error("unionThmElements with mismatch or nonextensible")
         end;
}


function cleanModThms
[[ThmElement]] ::= remove::ThmElement modThms::[[ThmElement]]
{
  --whether to remove the first thing in the first list
  local removeFirst::Boolean =
      case head(head(modThms)), remove of
      | splitElement(aname, alst), splitElement(bname, blst) ->
        ^aname == ^bname && alst == blst
      | nonextensibleTheorem(aname, aparams, astmt),
        nonextensibleTheorem(bname, bparams, bstmt) ->
        ^aname == ^bname
      | extensibleMutualTheoremGroup(athms, _, atag),
        extensibleMutualTheoremGroup(bthms, _, btag) -> atag == btag
      | projectionConstraintTheorem(aname, abinds, abody, atag),
        projectionConstraintTheorem(bname, bbinds, bbody, btag) ->
        atag == btag
      | extIndElement(arelinfo, athms, aalsos, atag),
        extIndElement(brelinfo, bthms, balsos, btag) ->
        atag == btag
      | extSizeElement(arels, atag), extSizeElement(brels, btag) ->
        atag == btag
      | projRelElement(arels, atag), projRelElement(brels, btag) ->
        atag == btag
      | _, _ -> false
      end;
  return case modThms of
         | [] -> []
         | [_]::tl when removeFirst ->
           cleanModThms(^remove, tl)
         | (_::rest)::tl when removeFirst ->
           rest::cleanModThms(^remove, tl)
         | hd::tl -> --!removeFirst
           hd::cleanModThms(^remove, tl)
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


abstract production addTagTopCommands
top::TopCommands ::= tag::Tag t::TopCommand rest::TopCommands
{
  top.pp = t.pp ++ rest.pp;
  top.len = 1 + rest.len;

  t.downTag = tag;

  --We don't actually need the environments here, since everything is
  --fully qualified.  However, we use extIndInfo for ExtInd, which we
  --also use for processing during proving, and this uses the
  --environments for getting the full names there.  Thus they can be
  --empty here and it is fine, but they need to be here for MWDA.
  t.relationEnv = buildEnv([]);
  t.typeEnv = buildEnv([]);
  t.constructorEnv = buildEnv([]);

  top.defElements = t.defElements ++ rest.defElements;
  top.thmElements = t.thmElements ++ rest.thmElements;
}


abstract production addTopCommands
top::TopCommands ::= t::TopCommand rest::TopCommands
{
  top.pp = t.pp ++ rest.pp;
  top.len = 1 + rest.len;

  t.downTag = error("Down tag not needed if not in outerface file");

  --We don't actually need the environments here, since everything is
  --fully qualified.  However, we use extIndInfo for ExtInd, which we
  --also use for processing during proving, and this uses the
  --environments for getting the full names there.  Thus they can be
  --empty here and it is fine, but they need to be here for MWDA.
  t.relationEnv = buildEnv([]);
  t.typeEnv = buildEnv([]);
  t.constructorEnv = buildEnv([]);

  top.defElements = t.defElements ++ rest.defElements;
  top.thmElements = t.thmElements ++ rest.thmElements;
}





attribute
   defElements, thmElements, downTag
occurs on TopCommand;

inherited attribute downTag::Tag;

aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.defElements = [];
  top.thmElements = [nonextensibleTheorem(^name, params, ^body)];
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
  top.thmElements = [splitElement(^theoremName, newTheoremNames)];
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
  top.defElements = [kindElement(names, ^k)];
  top.thmElements = [];
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.defElements = [typeElement(names, ^ty)];
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
                        alsos.thmInfo, top.downTag)];
}


aspect production proveObligations
top::TopCommand ::= names::[QName] newThms::ExtThms newAlsos::ExtThms
{
  top.defElements =
      error("Should not have proveObligations in interface file");
  top.thmElements =
      error("Should not have proveObligations in interface file");
}


aspect production projectionConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.defElements = [];
  top.thmElements = [projectionConstraintTheorem(^name, ^binds, ^body,
                        top.downTag)];
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
top::TopCommand ::= e::ExtIndBody thms::ExtThms alsos::ExtThms
{
  top.defElements = [];
  top.thmElements = [extIndElement(e.extIndInfo, thms.thmInfo,
                                   alsos.thmInfo, top.downTag)];
}


aspect production proveExtInd
top::TopCommand ::= rels::[QName] oldThms::[QName] newRels::ExtIndBody
                    newThms::ExtThms newAlsos::ExtThms
{
  top.defElements =
      error("Should not have proveExtInd in interface file");
  top.thmElements =
      error("Should not have proveExtInd in interface file");
}


aspect production extSizeDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.defElements = [];
  top.thmElements = [extSizeElement(rels, top.downTag)];
}


aspect production addExtSize
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.defElements =
      error("Should not have addExtSize in interface file");
  top.thmElements =
      error("Should not have addExtSize in interface file");
}


aspect production projRelDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.defElements = [];
  top.thmElements = [projRelElement(rels, top.downTag)];
}


aspect production addProjRel
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.defElements =
      error("Should not have addProjRel in interface file");
  top.thmElements =
      error("Should not have addProjRel in interface file");
}





attribute
   thmInfo
occurs on ExtThms;

synthesized attribute thmInfo::[(QName, Bindings, ExtBody, InductionOns)];

aspect production endExtThms
top::ExtThms ::=
{
  top.thmInfo = [];
}


aspect production addExtThms
top::ExtThms ::= name::QName bindings::Bindings body::ExtBody
                 ons::InductionOns rest::ExtThms
{
  top.thmInfo = (^name, ^bindings, ^body, ^ons)::rest.thmInfo;
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
  top.defClauses = [(^q, ^args, nothing())];
}


aspect production ruleDef
top::Def ::= q::QName args::TermList body::Metaterm
{
  top.defClauses = [(^q, ^args, just(^body))];
}
