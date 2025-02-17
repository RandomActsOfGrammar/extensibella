grammar extensibella:main:compose;

{-
  The purpose here is to map from modular proof states to composed
  ones.  The changes with which we are concerned are
  * Hypotheses changing from R to R_P
  * Adding extra hypotheses
  * Hypothesis names changing
  * The unknown/generic term changing to a real term
  * Variables mapping to new terms/variable names
  We gather up the relevant information about these changes to allow
  the mapping of old proofs to new ones.

  Attributes occur on the elements of the old state, with the elements
  of the new state passed down as attributes.
-}

--new state element against which to unify
inherited attribute mapTo<a>::a;
--whether it succeeds or not
synthesized attribute mapSuccess::Boolean;
--hyp info:  [(old hyp name, new hyp name, is now R_P)]
synthesized attribute hypMap::[(String, String, Boolean)];
--threading:  [(old var name, new corresponding term)]
threaded attribute varMap_in, varMap::[(String, Term)];
--the term to which unknown maps
monoid attribute unknownMap::Maybe<Term> with
   nothing(), unknownMap_combine;
global unknownMap_combine::(Maybe<Term> ::= Maybe<Term> Maybe<Term>) =
   \ a::Maybe<Term> b::Maybe<Term> ->
     case a, b of
     | just(ta), just(tb) -> --look for bugs (otherwise could ignore)
       if ta == tb then a else error("impossible mismatch")
     | just(ta), _ -> a
     | _, _ -> b
     end;

--for finding generic cases
--separate from mapping
monoid attribute containsUnknownK::Boolean with false, ||;
monoid attribute containsUnknownI::Boolean with false, ||;



attribute
   containsUnknownK, containsUnknownI,
   mapTo<ProofState>, mapSuccess, hypMap, varMap, unknownMap
occurs on ProofState;
propagate containsUnknownK, containsUnknownI on ProofState;

aspect production proofInProgress
top::ProofState ::= subgoalNum::SubgoalNum currGoal::CurrentGoal
                    futureGoals::[Subgoal]
{
  --must be full in order to compare, and our initial ones aren't
  local fullGoal::CurrentGoal = currGoal.full;
  fullGoal.mapTo =
      case top.mapTo of
      | proofInProgress(_, c, _) -> ^c
      | _ -> error("Should not access (proofInProgress)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | proofInProgress(_, _, _) -> fullGoal.mapSuccess
      | _ -> false
      end;
  top.hypMap = fullGoal.hypMap;
  top.varMap = fullGoal.varMap;
  top.unknownMap := fullGoal.unknownMap;
}


--don't actually ever need these
aspect production noProof
top::ProofState ::=
{
  top.mapSuccess = false;
  top.hypMap = error("Should not access (noProof)");
  top.varMap = error("Should not access (noProof)");
  top.unknownMap := error("Should not access (noProof)");
}

aspect production proofCompleted
top::ProofState ::=
{
  top.mapSuccess = false;
  top.hypMap = error("Should not access (proofCompleted)");
  top.varMap = error("Should not access (proofCompleted)");
  top.unknownMap := error("Should not access (proofCompleted)");
}

aspect production proofAborted
top::ProofState ::=
{
  top.mapSuccess = false;
  top.hypMap = error("Should not access (proofAborted)");
  top.varMap = error("Should not access (proofAborted)");
  top.unknownMap := error("Should not access (proofAborted)");
}





attribute
   containsUnknownK, containsUnknownI,
   mapTo<CurrentGoal>, mapSuccess, hypMap, varMap, unknownMap
occurs on CurrentGoal;
propagate containsUnknownK, containsUnknownI on CurrentGoal;

aspect production currentGoal
top::CurrentGoal ::= vars::[String] ctx::Context goal::Metaterm
{
  goal.varMap_in = [];
  goal.mapTo = case top.mapTo of
               | currentGoal(_, _, g) -> ^g
               end;

  local ctxMap::Maybe<([(String, String, Boolean)],
                       [(String, Term)], Maybe<Term>)> =
      mapContext(ctx.extensibella:common:abstractSyntax:hypList,
                 top.mapTo.extensibella:common:abstractSyntax:hypList,
                 goal.varMap);

  top.mapSuccess = goal.mapSuccess && ctxMap.isJust;
  top.varMap =
      case ctxMap of
      | just((_, x, _)) -> x
      | nothing() -> error("currentGoal.varMap")
      end;
  top.hypMap =
      case ctxMap of
      | just((x, _, _)) -> x
      | nothing() -> error("currentGoal.hypMap")
      end;
  top.unknownMap :=
      unknownMap_combine(goal.unknownMap,
         case ctxMap of
         | just((_, _, x)) -> x
         | nothing() -> error("currentGoal.unknownMap")
         end);
}


attribute
   containsUnknownK, containsUnknownI
occurs on Context, Hypothesis;
propagate containsUnknownK, containsUnknownI on Context, Hypothesis;





{-
  We do the mapping for the context with a function rather than
  attributes for simplicity.  The abstract syntax for contexts has a
  branching structure, while the actual structure for contexts, and
  the one with which we want to work here, is linear.  Thus we use a
  function over lists.  This will allow us easily to skip a hypothesis
  if it doesn't work to unify with it, something that would be nearly
  impossible with the branching structure.
-}
function mapContext
Maybe<([(String, String, Boolean)], --hypMap
       [(String, Term)], --varMap
       Maybe<Term>)> ::= --unknownMap
   oldHyps::[(String, Metaterm)]
   newHyps::[(String, Metaterm)]
   varMap_in::[(String, Term)]
{
  local body::Metaterm = head(oldHyps).2;
  body.mapTo = head(newHyps).2;
  body.varMap_in = varMap_in;
  --Note body could map here and still be wrong.  Spurious success is
  --   possible, so we also need to check the subcall's success.
  local again::Maybe<([(String, String, Boolean)],
                      [(String, Term)], Maybe<Term>)> =
      mapContext(tail(oldHyps), tail(newHyps), body.varMap);

  return
      case oldHyps, newHyps of
      | [], _ -> just(([], varMap_in, nothing()))
      | _::_, [] -> nothing() --must map all old hyps
      | (oh, ob)::_, (nh, nb)::_ ->
        if body.mapSuccess && again.isJust
        then --fully successful map, so add this hyp binding
             case again of
             | just((hypMap, varMap, unknownMap)) ->
               let addT::Boolean =
                   case ob, nb of
                   | relationMetaterm(_, _, _),
                     projRelMetaterm(_, _, _) -> true
                   | _, _ -> false
                   end
               in
                 just(((oh, nh, addT)::hypMap, varMap,
                       unknownMap_combine(body.unknownMap,
                                          unknownMap)))
               end
             | nothing() -> error("mapContext nothing()")
             end
        else --something failed, so try skipping first new hyp
             --either body mapping failed or had spurious map
             mapContext(oldHyps, tail(newHyps), varMap_in)
      end;
}





attribute
   containsUnknownK, containsUnknownI,
   mapTo<Metaterm>, mapSuccess, varMap_in, varMap, unknownMap
occurs on Metaterm;
propagate unknownMap, containsUnknownK, containsUnknownI on Metaterm;
propagate varMap_in, varMap on Metaterm excluding bindingMetaterm;

aspect production relationMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  args.mapTo =
      case top.mapTo of
      | relationMetaterm(_, x, _) -> ^x
      | projRelMetaterm(_, x, _) -> ^x
      | _ -> error("Should not access (relationMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | relationMetaterm(rel2, _, r2) ->
        args.mapSuccess && ^rel2 == ^rel && ^r2 == ^r
      | projRelMetaterm(rel2, _, r2) ->
        args.mapSuccess && ^rel2 == ^rel && ^r2 == ^r
      | _ -> false
      end;
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.mapSuccess =
      case top.mapTo of
      | trueMetaterm() -> true
      | _ -> false
      end;
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.mapSuccess =
      case top.mapTo of
      | falseMetaterm() -> true
      | _ -> false
      end;
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  t1.mapTo =
      case top.mapTo of
      | eqMetaterm(x, _) -> ^x
      | _ -> error("Should not access (eqMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | eqMetaterm(_, x) -> ^x
      | _ -> error("Should not access (eqMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | eqMetaterm(_, _) -> t1.mapSuccess && t2.mapSuccess
      | _ -> false
      end;
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  t1.mapTo =
      case top.mapTo of
      | impliesMetaterm(x, _) -> ^x
      | _ -> error("Should not access (impliesMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | impliesMetaterm(_, x) -> ^x
      | _ -> error("Should not access (impliesMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | impliesMetaterm(_, _) -> t1.mapSuccess && t2.mapSuccess
      | _ -> false
      end;
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  t1.mapTo =
      case top.mapTo of
      | orMetaterm(x, _) -> ^x
      | _ -> error("Should not access (orMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | orMetaterm(_, x) -> ^x
      | _ -> error("Should not access (orMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | orMetaterm(_, _) -> t1.mapSuccess && t2.mapSuccess
      | _ -> false
      end;
}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  t1.mapTo =
      case top.mapTo of
      | andMetaterm(x, _) -> ^x
      | _ -> error("Should not access (andMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | andMetaterm(_, x) -> ^x
      | _ -> error("Should not access (andMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | andMetaterm(_, _) -> t1.mapSuccess && t2.mapSuccess
      | _ -> false
      end;
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder nameBindings::Bindings body::Metaterm
{
  body.mapTo =
      case top.mapTo of
      | bindingMetaterm(_, _, nbody) -> ^nbody
      | _ -> error("Should not access (bindingMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | bindingMetaterm(nb, nn, nbody) ->
        ^b == ^nb &&
        nameBindings.len == nn.len &&
        body.mapSuccess
      | _ -> false
      end;

  --remove existing bindings for names bound here, as they are
  --   different bound vars
  body.varMap_in =
      removeBindings(nameBindings.usedNames, top.varMap_in);
  --get rid of the new bindings and put the old bindings in again
  top.varMap =
      addBindings(nameBindings.usedNames, top.varMap_in,
         removeBindings(nameBindings.usedNames, body.varMap));
}
function addBindings
[(String, Term)] ::=
   names::[String] source::[(String, Term)] l::[(String, Term)]
{
  return
      case names of
      | [] -> l
      | x::rest when lookup(x, source) matches just(v) ->
        addBindings(rest, source, (x, v)::l) --add binding
      | x::rest -> addBindings(rest, source, l)
      end;
}
function removeBindings
[(String, Term)] ::= names::[String] l::[(String, Term)]
{
  return
      case names of
      | [] -> l
      | x::rest -> removeBindings(rest, removeOne(x, l))
      end;
}
function removeOne
[(String, Term)] ::= name::String l::[(String, Term)]
{
  return
      case l of
      | [] -> []
      | (x, v)::rest ->
        if x == name then rest else (x, v)::removeOne(name, rest)
      end;
}


aspect production projectionMetaterm
top::Metaterm ::= args::TermList ty::QName orig::Term proj::Term
{
  args.mapTo =
      case top.mapTo of
      | projectionMetaterm(a, _, _, _) -> ^a
      | _ -> error("Should not access (projectionMetaterm)")
      end;
  orig.mapTo =
      case top.mapTo of
      | projectionMetaterm(_, _, o, _) -> ^o
      | _ -> error("Should not access (projectionMetaterm)")
      end;
  proj.mapTo =
      case top.mapTo of
      | projectionMetaterm(_, _, _, t) -> ^t
      | _ -> error("Should not access (projectionMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | projectionMetaterm(a, t, o, r) ->
        args.mapSuccess && orig.mapSuccess && proj.mapSuccess &&
        ^ty == ^t --no mapping types, only equality
      | _ -> false
      end;
}


aspect production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.mapTo =
      case top.mapTo of
      | plusMetaterm(x, _, _) -> ^x
      | _ -> error("Should not access (plusMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | plusMetaterm(_, x, _) -> ^x
      | _ -> error("Should not access (plusMetaterm)")
      end;
  result.mapTo =
      case top.mapTo of
      | plusMetaterm(_, _, x) -> ^x
      | _ -> error("Should not access (plusMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | plusMetaterm(_, _, _) ->
        t1.mapSuccess && t2.mapSuccess && result.mapSuccess
      | _ -> false
      end;
}


aspect production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.mapTo =
      case top.mapTo of
      | minusMetaterm(x, _, _) -> ^x
      | _ -> error("Should not access (minusMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | minusMetaterm(_, x, _) -> ^x
      | _ -> error("Should not access (minusMetaterm)")
      end;
  result.mapTo =
      case top.mapTo of
      | minusMetaterm(_, _, x) -> ^x
      | _ -> error("Should not access (minusMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | minusMetaterm(_, _, _) ->
        t1.mapSuccess && t2.mapSuccess && result.mapSuccess
      | _ -> false
      end;
}


aspect production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.mapTo =
      case top.mapTo of
      | multiplyMetaterm(x, _, _) -> ^x
      | _ -> error("Should not access (multiplyMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | multiplyMetaterm(_, x, _) -> ^x
      | _ -> error("Should not access (multiplyMetaterm)")
      end;
  result.mapTo =
      case top.mapTo of
      | multiplyMetaterm(_, _, x) -> ^x
      | _ -> error("Should not access (multiplyMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | multiplyMetaterm(_, _, _) ->
        t1.mapSuccess && t2.mapSuccess && result.mapSuccess
      | _ -> false
      end;
}


aspect production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.mapTo =
      case top.mapTo of
      | divideMetaterm(x, _, _) -> ^x
      | _ -> error("Should not access (divideMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | divideMetaterm(_, x, _) -> ^x
      | _ -> error("Should not access (divideMetaterm)")
      end;
  result.mapTo =
      case top.mapTo of
      | divideMetaterm(_, _, x) -> ^x
      | _ -> error("Should not access (divideMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | divideMetaterm(_, _, _) ->
        t1.mapSuccess && t2.mapSuccess && result.mapSuccess
      | _ -> false
      end;
}


aspect production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.mapTo =
      case top.mapTo of
      | modulusMetaterm(x, _, _) -> ^x
      | _ -> error("Should not access (modulusMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | modulusMetaterm(_, x, _) -> ^x
      | _ -> error("Should not access (modulusMetaterm)")
      end;
  result.mapTo =
      case top.mapTo of
      | modulusMetaterm(_, _, x) -> ^x
      | _ -> error("Should not access (modulusMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | modulusMetaterm(_, _, _) ->
        t1.mapSuccess && t2.mapSuccess && result.mapSuccess
      | _ -> false
      end;
}


aspect production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  t.mapTo =
      case top.mapTo of
      | negateMetaterm(x, _) -> ^x
      | _ -> error("Should not access (negateMetaterm)")
      end;
  result.mapTo =
      case top.mapTo of
      | negateMetaterm(_, x) -> ^x
      | _ -> error("Should not access (negateMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | negateMetaterm(_, _) ->
        t.mapSuccess && result.mapSuccess
      | _ -> false
      end;
}


aspect production lessMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  t1.mapTo =
      case top.mapTo of
      | lessMetaterm(x, _) -> ^x
      | _ -> error("Should not access (lessMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | lessMetaterm(_, x) -> ^x
      | _ -> error("Should not access (lessMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | lessMetaterm(_, _) ->
        t1.mapSuccess && t2.mapSuccess
      | _ -> false
      end;
}


aspect production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  t1.mapTo =
      case top.mapTo of
      | lessEqMetaterm(x, _) -> ^x
      | _ -> error("Should not access (lessEqMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | lessEqMetaterm(_, x) -> ^x
      | _ -> error("Should not access (lessEqMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | lessEqMetaterm(_, _) ->
        t1.mapSuccess && t2.mapSuccess
      | _ -> false
      end;
}


aspect production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  t1.mapTo =
      case top.mapTo of
      | greaterMetaterm(x, _) -> ^x
      | _ -> error("Should not access (greaterMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | greaterMetaterm(_, x) -> ^x
      | _ -> error("Should not access (greaterMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | greaterMetaterm(_, _) ->
        t1.mapSuccess && t2.mapSuccess
      | _ -> false
      end;
}


aspect production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  t1.mapTo =
      case top.mapTo of
      | greaterEqMetaterm(x, _) -> ^x
      | _ -> error("Should not access (greaterEqMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | greaterEqMetaterm(_, x) -> ^x
      | _ -> error("Should not access (greaterEqMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | greaterEqMetaterm(_, _) ->
        t1.mapSuccess && t2.mapSuccess
      | _ -> false
      end;
}


aspect production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term r::Restriction
{
  t1.mapTo =
      case top.mapTo of
      | appendMetaterm(x, _, _, _) -> ^x
      | _ -> error("Should not access (appendMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | appendMetaterm(_, x, _, _) -> ^x
      | _ -> error("Should not access (appendMetaterm)")
      end;
  result.mapTo =
      case top.mapTo of
      | appendMetaterm(_, _, x, _) -> ^x
      | _ -> error("Should not access (appendMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | appendMetaterm(_, _, _, r2) ->
        t1.mapSuccess && t2.mapSuccess && result.mapSuccess && ^r == ^r2
      | _ -> false
      end;
}


aspect production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.mapTo =
      case top.mapTo of
      | orBoolMetaterm(x, _, _) -> ^x
      | _ -> error("Should not access (orBoolMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | orBoolMetaterm(_, x, _) -> ^x
      | _ -> error("Should not access (orBoolMetaterm)")
      end;
  result.mapTo =
      case top.mapTo of
      | orBoolMetaterm(_, _, x) -> ^x
      | _ -> error("Should not access (orBoolMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | orBoolMetaterm(_, _, _) ->
        t1.mapSuccess && t2.mapSuccess && result.mapSuccess
      | _ -> false
      end;
}


aspect production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.mapTo =
      case top.mapTo of
      | andBoolMetaterm(x, _, _) -> ^x
      | _ -> error("Should not access (andBoolMetaterm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | andBoolMetaterm(_, x, _) -> ^x
      | _ -> error("Should not access (andBoolMetaterm)")
      end;
  result.mapTo =
      case top.mapTo of
      | andBoolMetaterm(_, _, x) -> ^x
      | _ -> error("Should not access (andBoolMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | andBoolMetaterm(_, _, _) ->
        t1.mapSuccess && t2.mapSuccess && result.mapSuccess
      | _ -> false
      end;
}


aspect production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  t.mapTo =
      case top.mapTo of
      | notBoolMetaterm(x, _) -> ^x
      | _ -> error("Should not access (notBoolMetaterm)")
      end;
  result.mapTo =
      case top.mapTo of
      | notBoolMetaterm(_, x) -> ^x
      | _ -> error("Should not access (notBoolMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | notBoolMetaterm(_, _) ->
        t.mapSuccess && result.mapSuccess
      | _ -> false
      end;
}


aspect production extSizeMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  args.mapTo =
      case top.mapTo of
      | extSizeMetaterm(_, a, _) -> ^a
      | _ -> error("Should not access (extSizeMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | extSizeMetaterm(rel2, _, r2) ->
        ^rel == ^rel2 && args.mapSuccess && ^r == ^r2
      | _ -> false
      end;
}


aspect production projRelMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  args.mapTo =
      case top.mapTo of
      | projRelMetaterm(_, a, _) -> ^a
      | _ -> error("Should not access (projRelMetaterm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | projRelMetaterm(rel2, _, r2) ->
        ^rel == ^rel2 && args.mapSuccess && ^r == ^r2
      | _ -> false
      end;
}





attribute
   containsUnknownK, containsUnknownI,
   mapTo<Term>, mapSuccess, varMap_in, varMap, unknownMap
occurs on Term;
propagate varMap_in, varMap on Term excluding nameTerm;
propagate unknownMap, containsUnknownK, containsUnknownI on
   Term excluding unknownITerm, unknownKTerm;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  f.mapTo =
      case top.mapTo of
      | applicationTerm(x, _) -> ^x
      | _ -> error("Should not access (applicationTerm)")
      end;
  args.mapTo =
      case top.mapTo of
      | applicationTerm(_, x) -> ^x
      | _ -> error("Should not access (applicationTerm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | applicationTerm(_, _) -> f.mapSuccess && args.mapSuccess
      | _ -> false
      end;
}


aspect production nameTerm
top::Term ::= name::QName mty::MaybeType
{
  local lookedUp::Maybe<Term> =
      lookup(name.shortName, top.varMap_in);

  top.mapSuccess =
      if name.isQualified
      then case top.mapTo of --constructor, so need same one
           | nameTerm(q, _) -> ^q == ^name
           | _ -> false
           end
      else case lookedUp of --var case
           | nothing() -> true --no previous binding
           | just(t) -> t == top.mapTo --must be same term everywhere
           end;

  top.varMap =
      if name.isQualified
      then top.varMap_in
      else case lookedUp of --add new binding if one isn't present
           | nothing() -> (name.shortName, top.mapTo)::top.varMap_in
           | just(_) -> top.varMap_in
           end;
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  t1.mapTo =
      case top.mapTo of
      | consTerm(x, _) -> ^x
      | _ -> error("Should not access (consTerm)")
      end;
  t2.mapTo =
      case top.mapTo of
      | consTerm(_, x) -> ^x
      | _ -> error("Should not access (consTerm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | consTerm(_, _) -> t1.mapSuccess && t2.mapSuccess
      | _ -> false
      end;
}


aspect production nilTerm
top::Term ::=
{
  top.mapSuccess =
      case top.mapTo of
      | nilTerm() -> true
      | _ -> false
      end;
}


aspect production underscoreTerm
top::Term ::= mty::MaybeType
{
  top.mapSuccess =
      error("Should not have underscoreTerm in proof state mapping");
}


aspect production unknownITerm
top::Term ::= ty::QName
{
  top.mapSuccess = true;
  top.unknownMap := just(top.mapTo);

  top.containsUnknownK := false;
  top.containsUnknownI := true;
}


aspect production unknownKTerm
top::Term ::= ty::QName
{
  top.mapSuccess = true;
  top.unknownMap := just(top.mapTo);

  top.containsUnknownK := true;
  top.containsUnknownI := false;
}


aspect production intTerm
top::Term ::= i::Integer
{
  top.mapSuccess =
      case top.mapTo of
      | intTerm(i2) -> i == i2
      | _ -> false
      end;
}


aspect production stringTerm
top::Term ::= contents::String
{
  top.mapSuccess =
      case top.mapTo of
      | stringTerm(c) -> c == contents
      | _ -> false
      end;
}


aspect production trueTerm
top::Term ::=
{
  top.mapSuccess =
      case top.mapTo of
      | trueTerm() -> true
      | _ -> false
      end;
}


aspect production falseTerm
top::Term ::=
{
  top.mapSuccess =
      case top.mapTo of
      | falseTerm() -> true
      | _ -> false
      end;
}


aspect production listTerm
top::Term ::= contents::ListContents
{
  contents.mapTo =
      case top.mapTo of
      | listTerm(c) -> ^c
      | _ -> error("Should not access (listTerm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | listTerm(_) -> contents.mapSuccess
      | _ -> false
      end;
}


aspect production pairTerm
top::Term ::= contents::PairContents
{
  contents.mapTo =
      case top.mapTo of
      | pairTerm(c) -> ^c
      | _ -> error("Should not access (pairTerm)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | pairTerm(_) -> contents.mapSuccess
      | _ -> false
      end;
}


aspect production charTerm
top::Term ::= char::String
{
  top.mapSuccess =
      case top.mapTo of
      | charTerm(x) -> x == char
      | _ -> false
      end;
}





attribute
   containsUnknownK, containsUnknownI,
   mapTo<TermList>, mapSuccess, varMap_in, varMap, unknownMap
occurs on TermList;
propagate varMap_in, varMap, unknownMap,
          containsUnknownK, containsUnknownI on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  t.mapTo =
      case top.mapTo of
      | singleTermList(x) -> ^x
      | consTermList(x, emptyTermList()) -> ^x
      | _ -> error("Should not access (singleTermList)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | singleTermList(_) -> t.mapSuccess
      | consTermList(_, emptyTermList()) -> t.mapSuccess
      | _ -> false
      end;
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  t.mapTo =
      case top.mapTo of
      | consTermList(x, _) -> ^x
      | singleTermList(x) -> ^x
      | _ -> error("Should not access (consTermList)")
      end;
  rest.mapTo =
      case top.mapTo of
      | consTermList(_, x) -> ^x
      | singleTermList(_) -> emptyTermList()
      | _ -> error("Should not access (consTermList)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | consTermList(_, _) -> t.mapSuccess && rest.mapSuccess
      | singleTermList(_) -> t.mapSuccess && rest.mapSuccess
      | _ -> false
      end;
}


aspect production emptyTermList
top::TermList ::=
{
  top.mapSuccess =
      case top.mapTo of
      | emptyTermList() -> true
      | _ -> false
      end;
}





attribute
   containsUnknownK, containsUnknownI,
   mapTo<ListContents>, mapSuccess, varMap_in, varMap, unknownMap
occurs on ListContents;
propagate varMap_in, varMap, unknownMap,
          containsUnknownK, containsUnknownI on ListContents;

aspect production emptyListContents
top::ListContents ::=
{
  top.mapSuccess =
      case top.mapTo of
      | emptyListContents() -> true
      | _ -> false
      end;
}


aspect production addListContents
top::ListContents ::= t::Term rest::ListContents
{
  t.mapTo =
      case top.mapTo of
      | addListContents(x, _) -> ^x
      | _ -> error("Should not access (addListContents)")
      end;
  rest.mapTo =
      case top.mapTo of
      | addListContents(_, x) -> ^x
      | _ -> error("Should not access (addListContents)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | addListContents(_, _) -> t.mapSuccess && rest.mapSuccess
      | _ -> false
      end;
}





attribute
   containsUnknownK, containsUnknownI,
   mapTo<PairContents>, mapSuccess, varMap_in, varMap, unknownMap
occurs on PairContents;
propagate varMap_in, varMap, unknownMap,
          containsUnknownK, containsUnknownI on PairContents;

aspect production singlePairContents
top::PairContents ::= t::Term
{
  t.mapTo =
      case top.mapTo of
      | singlePairContents(x) -> ^x
      | _ -> error("Should not access (singlePairContents)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | singlePairContents(_) -> t.mapSuccess
      | _ -> false
      end;
}


aspect production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  t.mapTo =
      case top.mapTo of
      | addPairContents(x, _) -> ^x
      | _ -> error("Should not access (addPairContents)")
      end;
  rest.mapTo =
      case top.mapTo of
      | addPairContents(_, x) -> ^x
      | _ -> error("Should not access (addPairContents)")
      end;

  top.mapSuccess =
      case top.mapTo of
      | addPairContents(_, _) -> t.mapSuccess && rest.mapSuccess
      | _ -> false
      end;
}
