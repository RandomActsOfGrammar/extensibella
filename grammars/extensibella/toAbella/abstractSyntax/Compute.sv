grammar extensibella:toAbella:abstractSyntax;


abstract production computeTactic
top::ProofCommand ::= hyp::String
{
  top.pp = text("compute " ++ hyp ++ ".") ++ line();
  top.abella_pp = justShow(top.pp);

  local state::ProofState = top.proverState.state;
  local maybeHypBody::Maybe<Metaterm> = lookup(hyp, state.hypList);
  local hypBody::Metaterm = maybeHypBody.fromJust;
  hypBody.relationEnv = top.relationEnv;
  hypBody.constructorEnv = top.constructorEnv;
  hypBody.boundNames = state.usedNames;
  hypBody.computeHyp = hyp;

  top.toAbellaMsgs <-
      case maybeHypBody of
      | nothing() -> [errorMsg("Unknown hypothesis " ++ hyp)]
      | just(_) ->
        if hypBody.isComputable
        then []
        else [errorMsg("Cannot compute " ++ hyp ++ " (" ++ justShow(hypBody.pp) ++ ")")]
      end;
  {-

    The problem here is that we are getting the Abella version of the
    state, and therefore the hypothesis, rather than the Extensibella
    version.  This is less than useful in this case, and I am
    wondering if it is also a bad thing overall.  How much would it
    break if I changed it to be the Extensibella version of the state
    and hypothesis instead?  That seems more useful in general for
    computation within Extensibella.

  -}

  top.toAbella = hypBody.computeCmds;
}




synthesized attribute isComputable::Boolean occurs on Metaterm;
inherited attribute computeHyp::String occurs on Metaterm;
synthesized attribute computeCmds::[ProofCommand] occurs on Metaterm;
propagate computeHyp on Metaterm;

aspect default production
top::Metaterm ::=
{
  top.isComputable = false;
  top.computeCmds = error("Should not access computeCmds if not computable");
}


function buildCaseTactics
[ProofCommand] ::= initialBody::Metaterm num::Integer
{
  return
      foldl(\ rest::[ProofCommand] i::Integer ->
              rest ++
              [caseTactic(nameHint("$" ++ toString(i + 1)),
                          "$" ++ toString(i), false)],
            --solved immediately, as this is a hyp
            [assertTactic(nameHint("$0"), nothing(), ^initialBody)],
            range(0, num));
}


function abs
Integer ::= i::Integer
{
  return if i < 0 then -i else i;
}

function min
Integer ::= a::Integer b::Integer
{
  return if a < b then a else b;
}


aspect production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  --we limit this to the easiest cases for now, even though any cases
  --of two constants and a name are fine theoretically
  --"simplest cases" are those that will not branch in using case
  top.isComputable =
      case t1, t2, result of
      | intTerm(i1), intTerm(i2), nameTerm(_, _) -> true
      | intTerm(i1), nameTerm(_, _), intTerm(ir) ->
        i1 == 0 ||
        (i1 > 0 && ir <= 0) ||
        (i1 < 0 && ir >= 0)
      | _, _, _ -> false
      end;

  local numComputes::Integer =
      case t1, t2, result of
      | intTerm(i1), intTerm(i2), _ ->
        if i1 >= 0 && i2 >= 0
        then i1 + 1
        else if i1 >= 0 -- i2 < 0
        then min(i1, -i2 - 1) + 1 --(-i2 - 1) because $negSuccInt
         -- i1 < 0
        else if i2 == 0
        then 1
        else if i2 > 0
        then min(-i1 - 1, i2) + 1 --(-i1 - 1) because $negSuccInt
         -- i2 < 0
        else -i1 --no "+1" because $negSuccInt encoding takes care of last step
      | intTerm(i1), _, intTerm(ir) ->
        if i1 >= 0
        then i1 + 1
         -- last allowed:  i1 < 0 && ir >= 0
        else -i1
      | _, _, _ -> error("Should not access (plusMetaterm.computeCmds)")
      end;
  top.computeCmds = buildCaseTactics(^top, numComputes);
}


aspect production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.isComputable =
      case t1, t2, result of
      | intTerm(i1), intTerm(i2), nameTerm(_, _) -> true
      | _, _, _ -> false
      end;

  local numComputes::Integer =
      case t1, t2 of
      | intTerm(i1), intTerm(i2) ->
        if i1 >= 0 && i2 < 0
        then i1 + 2
        else if i1 >= 0 -- i2 >= 0
        then min(i1, i2 - 1) + 2
         -- i1 < 0
        else if i2 == 0
        then 2
        else if i2 > 0
        then min(-i1 - 1, i2) + 2
         -- i2 >= 0
        else -i1 + 1
      | _, _ -> error("Should not access (minusMetaterm.computeCmds)")
      end;
  top.computeCmds = buildCaseTactics(^top, numComputes);
}


aspect production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  --should do this, but more complex
  top.isComputable = false;
}


aspect production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  --should do this, but more complex
  top.isComputable = false;
}


aspect production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  --should do this, but more complex
  top.isComputable = false;
}


aspect production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.isComputable = (t.isConstant && !result.isConstant) ||
                     (!t.isConstant && result.isConstant);

  top.computeCmds = [caseTactic(noHint(), top.computeHyp, true)];
}


aspect production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term r::Restriction
{
  top.isComputable =
      case t1, t2, result of
      --can always compute with full list first and a name to set
      | _, _, nameTerm(_, _) -> fullList(^t1)
      | _, nameTerm(_, _), _ -> fullList(^t1)
      --only completely-known strings
      | stringTerm(""), _, nameTerm(_, _) -> true
      | stringTerm(""), nameTerm(_, _), _ -> true
      | stringTerm(_), stringTerm(_), nameTerm(_, _) -> true
      | stringTerm(_), nameTerm(_, _), stringTerm(_) -> true
      --nothing else
      | _, _, _ -> unsafeTracePrint(false, "Cannot do " ++ justShow(t1.pp) ++ " (1)\n")
      end;
  local fullList::(Boolean ::= Term) =
      \ t::Term -> case t of
                   | nilTerm() -> true
                   | consTerm(_, r) -> fullList(^r)
                   | listTerm(_) -> true
                   | _ -> unsafeTracePrint(false, "Cannot do " ++ justShow(t1.pp) ++ " (2)\n")
                   end;

  --number of elements in the list we need to go through
  local num::Integer = listLen(^t1);
  local listLen::(Integer ::= Term) =
      \ t::Term -> case t of
                   | nilTerm() -> 0
                   | consTerm(_, r) -> 1 + listLen(^r)
                   | listTerm(c) -> c.len
                   | _ -> 0
                   end;

  --num + 1 cases
  top.computeCmds = buildCaseTactics(^top, num + 1);
{-      foldl(\ rest::[ProofCommand] i::Integer ->
              rest ++
              [caseTactic(nameHint("$" ++ toString(i + 1)),
                          "$" ++ toString(i), false)],
            --solved immediately, as this is a hyp
            [assertTactic(nameHint("$0"), nothing(), top)],
            range(0, num + 1));-}
}


aspect production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.isComputable =
      (t1.isConstant && t2.isConstant && !result.isConstant) ||
      case t1, t2 of
      | falseTerm(), nameTerm(_, _) when result.isConstant -> true
      | nameTerm(_, _), falseTerm() when result.isConstant -> true
      | _, _ -> false
      end;

  top.computeCmds = [caseTactic(noHint(), top.computeHyp, true)];
}


aspect production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.isComputable =
      (t1.isConstant && t2.isConstant && !result.isConstant) ||
      case t1, t2 of
      | trueTerm(), nameTerm(_, _) when result.isConstant -> true
      | nameTerm(_, _), trueTerm() when result.isConstant -> true
      | _, _ -> false
      end;

  top.computeCmds = [caseTactic(noHint(), top.computeHyp, true)];
}


aspect production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.isComputable = (t.isConstant && !result.isConstant) ||
                     (!t.isConstant && result.isConstant);

  top.computeCmds = [assertTactic(nameHint("$0"), nothing(), ^top),
                     caseTactic(noHint(), "$0", false)];
}
