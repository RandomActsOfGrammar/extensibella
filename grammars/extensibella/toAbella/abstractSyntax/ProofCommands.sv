grammar extensibella:toAbella:abstractSyntax;


--things you can do inside of proofs

nonterminal ProofCommand with
   --pp/abella_pp should end with space
   pp, abella_pp,
   boundNames,
   currentModule, typeEnv, constructorEnv, relationEnv, proverState,
   toAbella<[ProofCommand]>, toAbellaMsgs,
   isUndo, interactive,
   stateListIn, stateListOut;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          proverState, boundNames, toAbellaMsgs, interactive
   on ProofCommand;

aspect default production
top::ProofCommand ::=
{
  top.isUndo = false;
  top.stateListOut =
      error("Should only access ProofCommand.stateListOut for undo");
}


abstract production inductionTactic
top::ProofCommand ::= h::HHint nl::[Integer]
{
  top.pp = h.pp ++ text("induction on ") ++
           ppImplode(text(" "), map(text, map(toString, nl))) ++
           text(".") ++ line();
  top.abella_pp = h.abella_pp ++ "induction on " ++
                  implode(" ", map(toString, nl)) ++ ".  ";

  top.toAbella = [top];

  local goal::Metaterm = top.proverState.state.goal.fromJust;
  local splits::[[Metaterm]] =
      map((.splitImplies), goal.splitConjunctions);
  top.toAbellaMsgs <-
      if !top.proverState.state.inProof
      then [] --not a proof
      else if length(nl) != length(splits)
      then [errorMsg("Expected " ++ toString(length(splits)) ++
               " induction arguments but was given " ++
               toString(length(nl)))]
      else
        flatMap( --(induction integer, premises and goal)
           \ p::(Integer, [Metaterm]) ->
             if p.1 >= length(p.2)
             then [errorMsg("Premise " ++ toString(p.1) ++ " does " ++
                            "not exist")]
             else
               let e::Metaterm = elemAtIndex(p.2, p.1 - 1)
               in
                 case e of
                 --Allowed induction
                 | relationMetaterm(rel, args, r)
                   --allow induction on append
                   when rel.shortName == appendName -> []
                 | relationMetaterm(rel, args, r) when
                   decorate rel with {
                     relationEnv = top.relationEnv;}.relFound -> []
                 | extSizeMetaterm(rel, args, r) -> []
                 | transRelMetaterm(rel, args, r) -> []
                 | appendMetaterm(t1, t2, res, r) -> []
                 --Disallowed induction
                 | relationMetaterm(rel, args, r) ->
                   --should be a special relation or unknown
                   [errorMsg("Cannot induct on " ++ justShow(e.pp))]
                 | _ -> [errorMsg("Cannot induct on non-relation")]
                 end
               end,
           zip(nl, splits));
}


abstract production coinductionTactic
top::ProofCommand ::= h::HHint
{
  top.pp = ppConcat([h.pp, text("coinduction."), line()]);
  top.abella_pp = h.abella_pp ++ "coinduction.  ";

  top.toAbella = [top];
}


abstract production introsTactic
top::ProofCommand ::= names::[String]
{
  local namesString::String =
     if null(names)
     then ""
     else " " ++ implode(" ", names);
  top.pp = cat(text("intros" ++ namesString ++ "."), line());
  top.abella_pp = "intros" ++ namesString ++ ".  ";

  top.toAbella = [top];
}


abstract production applyTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> theorem::Clearable
                      args::ApplyArgs withs::Withs
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  local nestLen::Integer = 2 + length(justShow(h.pp));
  top.pp = h.pp ++ text("apply ") ++ text(depthString) ++
           theorem.pp ++
           ( if args.len == 0 then text("")
             else text(" to ") ++
                  nest(nestLen,
                     foldr1(\ d::Document rest::Document ->
                              docGroup(d ++ line() ++ rest),
                            args.pps)) ) ++
           ( if withs.len == 0 then text("")
             else text(" with") ++
                  nest(nestLen, line() ++
                     foldr1(\ d::Document rest::Document ->
                              docGroup(d ++ line() ++ rest),
                            withs.pps)) ) ++
           text(".") ++ line();
  local argsString_abella::String =
     if args.len == 0
     then ""
     else " to " ++ args.abella_pp;
  local withsString_abella::String =
     if withs.len == 0
     then ""
     else " with " ++ withs.abella_pp;
  top.abella_pp =
      h.abella_pp ++ "apply " ++ depthString ++ theorem.abella_pp ++
      argsString_abella ++ withsString_abella ++ ".  ";

  top.toAbella =
      [applyTactic(h, depth, theorem.toAbella,
                   args.toAbella, withs.toAbella)];
}


abstract production backchainTactic
top::ProofCommand ::= depth::Maybe<Integer> theorem::Clearable
                      withs::Withs
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  top.pp = text("backchain ") ++ text(depthString) ++
           theorem.pp ++ (if withs.len == 0 then text("")
                           else text(" to") ++ line() ++
                                ppImplode(line(), withs.pps)) ++
              text(".") ++ line();
  local withsString_abella::String =
     if withs.len == 0
     then ""
     else " with " ++ withs.abella_pp;
  top.abella_pp = "backchain " ++ depthString ++ theorem.abella_pp ++
                  withsString_abella ++ ".  ";

  top.toAbella =
      [backchainTactic(depth, theorem.toAbella, withs.toAbella)];
}


abstract production caseTactic
top::ProofCommand ::= h::HHint hyp::String keep::Boolean
{
  top.pp = h.pp ++ text("case ") ++ text(hyp) ++
           (if keep then text(" (keep).") else text(".")) ++ line();
  top.abella_pp = h.abella_pp ++ "case " ++ hyp ++
                  if keep then " (keep).  " else ".  ";

  top.toAbella = [top];

  local maybeHypBody::Maybe<Metaterm> =
      lookup(hyp, top.proverState.state.hypList);
  local hypBody::Metaterm = maybeHypBody.fromJust;
  hypBody.relationEnv = top.relationEnv;
  hypBody.constructorEnv = top.constructorEnv;
  --check hyp isn't an extensible relation or has PC filled in
  top.toAbellaMsgs <-
      if !maybeHypBody.isJust
      then [errorMsg("Unknown hypothesis " ++ hyp)]
      else
         case hypBody of
         | relationMetaterm(rel, args, r) ->
           if !rel.relFound
           then [] --already covered
           else if rel.fullRel.name == is_string
           then [errorMsg("Cannot do case analysis on " ++
                    justShow(is_string.pp) ++ " relation")] --because $is_char
           else if !rel.fullRel.isExtensible
           then [] --can do case analysis on non-extensible whenever
           else if length(args.isStructuredList) <= rel.fullRel.pcIndex
           then [] --too few args
           else if !elemAtIndex(args.isStructuredList,
                                rel.fullRel.pcIndex)
           then [errorMsg("Cannot do case analysis on extensible " ++
                    "relation " ++ justShow(rel.pp) ++ " with " ++
                    "unstructured primary component")]
           else if elemAtIndex(args.toList,
                               rel.fullRel.pcIndex).isUnknownTerm &&
                   !sameModule(top.currentModule, rel.fullRel.name)
           then [errorMsg("Cannot do case analysis on host " ++
                    "extensible relation with unknown primary " ++
                    "component")]
           else []
         | _ -> []
         end;
}


abstract production assertTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> m::Metaterm
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  top.pp = h.pp ++ text("assert ") ++ text(depthString) ++ m.pp ++
           text(".") ++ line();
  top.abella_pp = h.abella_pp ++ "assert " ++ depthString ++
                  m.abella_pp ++ ".  ";

  top.toAbella = [assertTactic(h, depth, m.toAbella)];
}


abstract production existsTactic
top::ProofCommand ::= ew::EWitnesses
{
  top.pp = ppConcat([text("exists "),
              ppImplode(cat(text(","), line()), ew.pps), text("."),
              line()]);
  top.abella_pp = "exists " ++ ew.abella_pp ++ ".  ";

  top.toAbella = [existsTactic(ew.toAbella)];
}


abstract production witnessTactic
top::ProofCommand ::= ew::EWitnesses
{
  top.pp = ppConcat([text("witness "),
              ppImplode(cat(text(","), line()), ew.pps), text("."),
              line()]);
  top.abella_pp = "witness " ++ ew.abella_pp ++ ".  ";

  top.toAbella = [witnessTactic(ew.toAbella)];
}


abstract production searchTactic
top::ProofCommand ::=
{
  top.pp = cat(text("search."), line());
  top.abella_pp = "search.  ";

  top.toAbella = [top];
}


abstract production searchDepthTactic
top::ProofCommand ::= n::Integer
{
  top.pp = cat(text("search " ++ toString(n) ++ "."), line());
  top.abella_pp = "search " ++ toString(n) ++ ".  ";

  top.toAbella = [top];
}


abstract production searchWitnessTactic
top::ProofCommand ::= sw::SearchWitness
{
  top.pp = text("search with ") ++ sw.pp ++ text(".") ++ line();
  top.abella_pp = "search with " ++ sw.abella_pp ++ ".  ";

  top.toAbella = [searchWitnessTactic(sw.toAbella)];
}


abstract production asyncTactic
top::ProofCommand ::=
{
  top.pp = cat(text("async."), line());
  top.abella_pp = "async.  ";

  top.toAbella = [top];
}


abstract production splitTactic
top::ProofCommand ::=
{
  top.pp = cat(text("split."), line());
  top.abella_pp = "split.  ";

  top.toAbella = [top];
}


abstract production splitStarTactic
top::ProofCommand ::=
{
  top.pp = cat(text("split*."), line());
  top.abella_pp = "split*.  ";

  top.toAbella = [top];
}


abstract production leftTactic
top::ProofCommand ::=
{
  top.pp = cat(text("left."), line());
  top.abella_pp = "left.  ";

  top.toAbella = [top];
}


abstract production rightTactic
top::ProofCommand ::=
{
  top.pp = cat(text("right."), line());
  top.abella_pp = "right.  ";

  top.toAbella = [top];
}


abstract production skipTactic
top::ProofCommand ::=
{
  top.pp = cat(text("skip."), line());
  top.abella_pp = "skip.  ";

  top.toAbella = [top];
}


abstract production abortCommand
top::ProofCommand ::=
{
  top.pp = cat(text("abort."), line());
  top.abella_pp = "abort.  ";

  top.toAbella = [top];
}


abstract production undoCommand
top::ProofCommand ::=
{
  top.pp = cat(text("undo."), line());
  top.abella_pp = "undo.  ";

  top.toAbella = repeat(undoCommand(), head(top.stateListIn).1);

  top.toAbellaMsgs <-
      if top.interactive
      then []
      else [errorMsg("Undo command should not be used in " ++
                     "non-interactive settings")];

  top.isUndo = true;
  top.stateListOut = tail(top.stateListIn);
}


--I have no idea what the arrow does, but there are clears with and without it
abstract production clearCommand
top::ProofCommand ::= removes::[String] hasArrow::Boolean
{
  top.pp = ppConcat([text("clear "),
              text(if hasArrow then "-> " else ""),
              ppImplode(line(), map(text, removes)), text("."),
              line()]);
  top.abella_pp = justShow(top.pp);

  top.toAbella = [top];
}


abstract production renameTactic
top::ProofCommand ::= original::String renamed::String
{
  top.pp = cat(text("rename " ++ original ++ " to " ++
                    renamed ++ "."), line());
  top.abella_pp = "rename " ++ original ++ " to " ++ renamed ++ ".  ";

  top.toAbella = [top];
}


--this assumes newText does NOT include the quotation marks
abstract production abbrevCommand
top::ProofCommand ::= hyps::[String] newText::String
{
  top.pp = cat(text("abbrev " ++ implode(" ", hyps) ++
                    " \"" ++ newText ++ "\"."), line());
  top.abella_pp = justShow(top.pp);

  top.toAbella = error("Cannot abbreviate");
  top.toAbellaMsgs <-
     [errorMsg("Abbreviation of hypotheses not currently supported")];
}


abstract production unabbrevCommand
top::ProofCommand ::= hyps::[String]
{
  top.pp = cat(text("unabbrev " ++ implode(" ", hyps) ++ "\"."),
               line());
  top.abella_pp = justShow(top.pp);

  top.toAbella = error("Cannot abbreviate");
  top.toAbellaMsgs <-
     [errorMsg("Abbreviation of hypotheses not currently supported")];
}


abstract production permuteTactic
top::ProofCommand ::= names::[String] hyp::Maybe<String>
{
  local hypString::String = case hyp of | just(h) -> " " ++ h | nothing() -> "" end;
  top.pp = ppConcat([text("permute "),
              ppImplode(line(), map(text, names)), text(hypString),
              text("."), line()]);
  top.abella_pp = justShow(top.pp);

  top.toAbella = [top];
}


abstract production unfoldStepsTactic
top::ProofCommand ::= steps::Integer all::Boolean
{
  top.pp = cat(text("unfold " ++ toString(steps) ++
                    if all then "(all)." else "."), line());
  top.abella_pp = justShow(top.pp);

  top.toAbella = [top];
}


abstract production unfoldIdentifierTactic
top::ProofCommand ::= id::QName all::Boolean
{
  top.pp = text("unfold ") ++ id.pp ++ text(if all then "(all)."
                                            else ".") ++ line();
  top.abella_pp = "unfold " ++ id.abella_pp ++ if all then " (all).  "
                                                      else ".  ";

  top.toAbella = [unfoldIdentifierTactic(id.fullRel.name, all)];

  top.toAbellaMsgs <- id.relErrors;
}


abstract production unfoldTactic
top::ProofCommand ::= all::Boolean
{
  top.pp = text("unfold " ++ if all then "(all)." else ".") ++ line();
  top.abella_pp = justShow(top.pp);

  top.toAbella = [top];

  top.toAbellaMsgs <-
      if !top.proverState.state.goal.isJust
      then error("Impossible (unfoldTactic)")
      else 
        case decorate top.proverState.state.goal.fromJust with {
               relationEnv = top.relationEnv;
               constructorEnv = top.constructorEnv;
             } of
        | relationMetaterm(r, a, _) ->
          let rel::RelationEnvItem = --r must be qualified, so only one
              head(lookupEnv(r, top.proverState.knownRels))
          in
            if !rel.isExtensible
            then [] --always fine, since no other rules can be added
            else if decorate elemAtIndex(a.toList, rel.pcIndex) with {
                       relationEnv=top.relationEnv;
                       constructorEnv=top.constructorEnv;
                    }.isStructured
            then [] --no new rules can be added, so fine
            else [errorMsg("Cannot unfold conclusion of extensible " ++
                     "relation with unfilled primary component")]
          end
        | transRelMetaterm(r, a, _) ->
          let rel::RelationEnvItem = --r must be qualified, so only one
              head(lookupEnv(r, top.proverState.knownRels))
          in
            if !rel.isExtensible
            then [] --always fine, since no other rules can be added
            else if decorate elemAtIndex(a.toList, rel.pcIndex) with {
                       relationEnv=top.relationEnv;
                       constructorEnv=top.constructorEnv;
                    }.isStructured
            then [] --no new rules can be added, so fine
            else [errorMsg("Cannot unfold conclusion of extensible " ++
                     "relation with unfilled primary component")]
          end
        | extSizeMetaterm(r, a, _) ->
          let rel::RelationEnvItem = --r must be qualified, so only one
              head(lookupEnv(r, top.proverState.knownRels))
          in
            if !rel.isExtensible
            then [] --always fine, since no other rules can be added
            else if decorate elemAtIndex(a.toList, rel.pcIndex) with {
                       relationEnv=top.relationEnv;
                       constructorEnv=top.constructorEnv;
                    }.isStructured
            then [] --no new rules can be added, so fine
            else [errorMsg("Cannot unfold conclusion of extensible " ++
                     "relation with unfilled primary component")]
          end
        | translationMetaterm(a, ty, orig, trans) ->
          if orig.isStructured
          then [] --no new rules can be added, so fine
          else [errorMsg("Cannot unfold conclusion of translation " ++
                   "with unfilled primary component")]
        | _ -> [errorMsg("Cannot unfold conclusion of this form")]
        end;
}





nonterminal Clearable with
   pp, abella_pp,
   toAbella<Clearable>, toAbellaMsgs,
   typeEnv, constructorEnv, relationEnv, proverState;
propagate toAbellaMsgs, proverState,
          typeEnv, constructorEnv, relationEnv on Clearable;

--I don't know what the star is, but some have it
abstract production clearable
top::Clearable ::= star::Boolean hyp::QName instantiation::TypeList
{
  local instPP::Document =
     if instantiation.len == 0
     then text("")
     else text("[") ++ ppImplode(text(", "), instantiation.pps) ++
          text("]");
  top.pp = text(if star then "*" else "") ++ hyp.pp ++
           docGroup(instPP);
  local instString_abella::String =
     if instantiation.abella_pp == ""
     then ""
     else "[" ++ instantiation.abella_pp ++ "]";
  top.abella_pp = (if star then "*" else "") ++ hyp.abella_pp ++
                  instString_abella;

  production hypFound::Boolean =
     foldr(\ p::(String, Metaterm) found::Boolean ->
             found || p.1 == hyp.shortName,
           false, top.proverState.state.hypList);
  production possibleThms::[(QName, Metaterm)] =
     findTheorem(hyp, top.proverState);
  top.toAbella =
      clearable(star,
                if hyp.isQualified || hypFound
                then hyp
                else head(possibleThms).1, instantiation.toAbella);

  top.toAbellaMsgs <-
      if hypFound
      then []
      else case possibleThms of
           | [] -> [errorMsg("Unknown hypothesis or theorem " ++
                             justShow(hyp.pp))]
           | [_] -> []
           | l -> [errorMsg("Indeterminate theorem " ++
                      justShow(hyp.pp) ++ "; possibilities are " ++
                      implode(", ", map(justShow,
                                        map((.pp), map(fst, l)))))]
           end;
}





nonterminal ApplyArgs with
   pps, abella_pp,
   toList<ApplyArg>, len,
   boundNames,
   toAbella<ApplyArgs>, toAbellaMsgs,
   typeEnv, constructorEnv, relationEnv, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          proverState, boundNames, toAbellaMsgs on ApplyArgs;

abstract production endApplyArgs
top::ApplyArgs ::=
{
  top.pps = [];
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.toAbella = endApplyArgs();
}


abstract production addApplyArgs
top::ApplyArgs ::= a::ApplyArg rest::ApplyArgs
{
  top.pps = a.pp::rest.pps;
  top.abella_pp = a.abella_pp ++
           if rest.abella_pp == "" then "" else " " ++ rest.abella_pp;

  top.toList = a::rest.toList;
  top.len = 1 + rest.len;

  top.toAbella = addApplyArgs(a.toAbella, rest.toAbella);
}






nonterminal ApplyArg with
   pp, abella_pp,
   boundNames,
   toAbella<ApplyArg>, toAbellaMsgs,
   typeEnv, constructorEnv, relationEnv, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          proverState, boundNames, toAbellaMsgs on ApplyArg;

abstract production hypApplyArg
top::ApplyArg ::= hyp::String instantiation::TypeList
{
  local instPP::Document =
     if instantiation.len == 0
     then text("")
     else text("[") ++ ppImplode(text(", "),  instantiation.pps) ++
          text("]");
  top.pp = text(hyp) ++ instPP;
  local instString_abella::String =
     if instantiation.abella_pp == ""
     then ""
     else "[" ++ instantiation.abella_pp ++ "]";
  top.abella_pp = hyp ++ instString_abella;

  top.toAbella = hypApplyArg(hyp, instantiation.toAbella);
}

abstract production starApplyArg
top::ApplyArg ::= name::String instantiation::TypeList
{
  local instPP::Document =
     if instantiation.len == 0
     then text("")
     else text("[") ++ ppImplode(text(", "), instantiation.pps) ++
          text("]");
  top.pp = text("*") ++ text(name) ++ instPP;
  local instString_abella::String =
     if instantiation.abella_pp == ""
     then ""
     else "[" ++ instantiation.abella_pp ++ "]";
  top.abella_pp = "*" ++ name ++ instString_abella;

  top.toAbella = starApplyArg(name, instantiation.toAbella);
}





nonterminal Withs with
   pps, abella_pp,
   toList<(String, Term)>, len,
   boundNames,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState,
   toAbella<Withs>, toAbellaMsgs;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          proverState, toAbellaMsgs, boundNames on Withs;

abstract production endWiths
top::Withs ::=
{
  top.pps = [];
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.toAbella = endWiths();
}


abstract production addWiths
top::Withs ::= name::String term::Term rest::Withs
{
  top.pps = ppConcat([text(name), text(" = "), term.pp])::rest.pps;
  top.abella_pp = name ++ " = " ++ term.abella_pp ++
                 if rest.len == 0 then "" else ", " ++ rest.abella_pp;

  top.toList = (name, term)::rest.toList;
  top.len = 1 + rest.len;

  top.toAbella = addWiths(name, term.toAbella, rest.toAbella);
}





nonterminal EWitnesses with
   pps, abella_pp,
   boundNames,
   typeEnv, constructorEnv, relationEnv, proverState,
   toAbella<EWitnesses>, toAbellaMsgs;
propagate typeEnv, constructorEnv, relationEnv,
          proverState, boundNames, toAbellaMsgs on EWitnesses;

abstract production oneEWitnesses
top::EWitnesses ::= e::EWitness
{
  top.pps = [e.pp];
  top.abella_pp = e.abella_pp;

  top.toAbella = oneEWitnesses(e.toAbella);
}


abstract production addEWitnesses
top::EWitnesses ::= e::EWitness rest::EWitnesses
{
  top.pps = e.pp::rest.pps;
  top.abella_pp = e.abella_pp ++ ", " ++ rest.abella_pp;

  top.toAbella = addEWitnesses(e.toAbella, rest.toAbella);
}





nonterminal EWitness with
   pp, abella_pp,
   boundNames,
   typeEnv, constructorEnv, relationEnv, proverState,
   toAbella<EWitness>, toAbellaMsgs;
propagate typeEnv, constructorEnv, relationEnv,
          proverState, boundNames, toAbellaMsgs on EWitness;

abstract production termEWitness
top::EWitness ::= t::Term
{
  top.pp = t.pp;
  top.abella_pp = t.abella_pp;

  top.toAbella = termEWitness(t.toAbella);
}


abstract production nameEWitness
top::EWitness ::= name::String t::Term
{
  top.pp = cat(text(name ++ " = "), t.pp);
  top.abella_pp = name ++ " = " ++ t.abella_pp;

  top.toAbella = nameEWitness(name, t.toAbella);
}





nonterminal HHint with
   pp, abella_pp;

abstract production nameHint
top::HHint ::= name::String
{
  top.pp = text(name ++ ": ");
  top.abella_pp = name ++ ": ";
}


abstract production noHint
top::HHint ::=
{
  top.pp = text("");
  top.abella_pp = "";
}

