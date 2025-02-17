grammar extensibella:common:concreteSyntax;


import extensibella:common:abstractSyntax;

import silver:langutil only pp, pps;


synthesized attribute ast<a>::a;

--a count of how many levels of a restriction
synthesized attribute count::Integer;



--Either for a parse error allowed by the grammar but disallowed semantically
closed nonterminal Metaterm_c with ast<Either<String Metaterm>>;
closed nonterminal SubMetaterm_c with ast<Either<String Metaterm>>;


{-concrete productions top::Metaterm_c
| 'true'
{ }
| 'false'
{ }
| t1::Term_c '=' t2::Term_c
{ }
| b::Binder_c bl::BindingList_c ',' m::Metaterm_c
{ }
| m1::Metaterm_c '->' m2::Metaterm_c
{ }
| m1::Metaterm_c '\/' m2::Metaterm_c
{ }
| m1::Metaterm_c '/\' m2::Metaterm_c
{ }
| '(' m::Metaterm_c ')'
{ }
| t::Term_c r::Restriction_c
{ }-}
{-
  The original grammar rules, translated from the OCaml Yacc grammar,
  are above.  That grammar had an ambiguity where `(Term)` could not
  be parsed:
  - It could be a Term followed by an empty Restriction inside
    Metaterm_c parentheses.
  - It could be a Term in Exp parentheses, which is then a Term
    followed by an empty Restriction as a Metaterm_c.
  These end up being equal treatments.  The refactoring below
  eliminates the first possibility, since any Term in Metaterm_c
  parentheses must be followed by a non-empty restriction set.  This
  makes the grammar unambiguous, but still able to parse the same
  strings.
-}
concrete productions top::Metaterm_c
| tm::Term_c
  { top.ast =
        case tm.ast of
        | trueTerm() -> right(trueMetaterm())
        | falseTerm() -> right(falseMetaterm())
        | applicationTerm(nameTerm(q, _), args) ->
          right(relationMetaterm(^q, ^args, emptyRestriction()))
        | t -> left("Cannot treat " ++ justShow(t.pp) ++
                    " as a proposition")
        end; }
--extension size
| '<' rel::Id_t '{' 'ES' '}' '>' args::ExpList_c
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    emptyRestriction())); }
| '<' rel::Id_t '{' 'ES' '}' '>' args::ExpList_c r::Stars_c
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Id_t '{' 'ES' '}' '>' args::ExpList_c r::Pluses_c
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Id_t '{' 'ES' '}' '>' args::ExpList_c r::Ats_c
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Id_t '{' 'ES' '}' '>' args::ExpList_c r::Hashes_c
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Qname_t '{' 'ES' '}' '>' args::ExpList_c
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    emptyRestriction())); }
| '<' rel::Qname_t '{' 'ES' '}' '>' args::ExpList_c r::Stars_c
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Qname_t '{' 'ES' '}' '>' args::ExpList_c r::Pluses_c
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Qname_t '{' 'ES' '}' '>' args::ExpList_c r::Ats_c
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Qname_t '{' 'ES' '}' '>' args::ExpList_c r::Hashes_c
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Id_t '{' 'ES' '}' '>' args::ExpList_c ')'
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    emptyRestriction())); }
| '(' '<' rel::Id_t '{' 'ES' '}' '>' args::ExpList_c r::Stars_c ')'
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Id_t '{' 'ES' '}' '>' args::ExpList_c r::Pluses_c ')'
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Id_t '{' 'ES' '}' '>' args::ExpList_c r::Ats_c ')'
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Id_t '{' 'ES' '}' '>' args::ExpList_c r::Hashes_c ')'
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Qname_t '{' 'ES' '}' '>' args::ExpList_c ')'
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    emptyRestriction())); }
| '(' '<' rel::Qname_t '{' 'ES' '}' '>' args::ExpList_c r::Stars_c ')'
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Qname_t '{' 'ES' '}' '>' args::ExpList_c r::Pluses_c ')'
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Qname_t '{' 'ES' '}' '>' args::ExpList_c r::Ats_c ')'
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Qname_t '{' 'ES' '}' '>' args::ExpList_c r::Hashes_c ')'
  { top.ast = right(extSizeMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
--projection version of a relation
| '<' rel::Id_t '{' 'P' '}' '>' args::ExpList_c
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    emptyRestriction())); }
| '<' rel::Id_t '{' 'P' '}' '>' args::ExpList_c r::Stars_c
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Id_t '{' 'P' '}' '>' args::ExpList_c r::Pluses_c
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Id_t '{' 'P' '}' '>' args::ExpList_c r::Ats_c
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Id_t '{' 'P' '}' '>' args::ExpList_c r::Hashes_c
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Qname_t '{' 'P' '}' '>' args::ExpList_c
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    emptyRestriction())); }
| '<' rel::Qname_t '{' 'P' '}' '>' args::ExpList_c r::Stars_c
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Qname_t '{' 'P' '}' '>' args::ExpList_c r::Pluses_c
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Qname_t '{' 'P' '}' '>' args::ExpList_c r::Ats_c
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '<' rel::Qname_t '{' 'P' '}' '>' args::ExpList_c r::Hashes_c
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Id_t '{' 'P' '}' '>' args::ExpList_c ')'
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                     emptyRestriction())); }
| '(' '<' rel::Id_t '{' 'P' '}' '>' args::ExpList_c r::Stars_c ')'
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Id_t '{' 'P' '}' '>' args::ExpList_c r::Pluses_c ')'
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Id_t '{' 'P' '}' '>' args::ExpList_c r::Ats_c ')'
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Id_t '{' 'P' '}' '>' args::ExpList_c r::Hashes_c ')'
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Qname_t '{' 'P' '}' '>' args::ExpList_c ')'
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    emptyRestriction())); }
| '(' '<' rel::Qname_t '{' 'P' '}' '>' args::ExpList_c r::Stars_c ')'
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Qname_t '{' 'P' '}' '>' args::ExpList_c r::Pluses_c ')'
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Qname_t '{' 'P' '}' '>' args::ExpList_c r::Ats_c ')'
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
| '(' '<' rel::Qname_t '{' 'P' '}' '>' args::ExpList_c r::Hashes_c ')'
  { top.ast = right(projRelMetaterm(toQName(rel.lexeme), args.ast,
                                    r.ast)); }
--something else
| s::SubMetaterm_c
  { top.ast = s.ast; }


concrete productions top::SubMetaterm_c
| t1::Term_c '=' t2::Term_c
  { top.ast = right(eqMetaterm(t1.ast, t2.ast)); }
| b::Binder_c bl::BindingList_c ',' m::Metaterm_c
  { top.ast =
        bind(m.ast,
             \ ma::Metaterm ->
               right(bindingMetaterm(b.ast, bl.ast, ma))); }
| m1::Metaterm_c '->' m2::Metaterm_c
  { top.ast =
        bind(m1.ast,
             \ m1::Metaterm ->
               bind(m2.ast,
                    \ m2::Metaterm ->
                      right(impliesMetaterm(m1, m2)))); }
| m1::Metaterm_c '\/' m2::Metaterm_c
  { top.ast =
        bind(m1.ast,
             \ m1::Metaterm ->
               bind(m2.ast,
                    \ m2::Metaterm ->
                      right(orMetaterm(m1, m2)))); }
| m1::Metaterm_c '/\' m2::Metaterm_c
  { top.ast =
        bind(m1.ast,
             \ m1::Metaterm ->
               bind(m2.ast,
                    \ m2::Metaterm ->
                      right(andMetaterm(m1, m2)))); }
| '(' m::SubMetaterm_c ')'
  { top.ast = m.ast; }
--Restrictions
| tm::Term_c s::Stars_c
  { top.ast =
        case tm.ast of
        | trueTerm() ->
          left("Cannot have restrictions on true")
        | falseTerm() ->
          left("Cannot have restrictions on false")
        | applicationTerm(nameTerm(q, _), args) ->
          right(relationMetaterm(^q, ^args, s.ast))
        | t -> left("Cannot treat " ++ justShow(t.pp) ++
                    " as a proposition")
        end; }
| tm::Term_c p::Pluses_c
  { top.ast =
        case tm.ast of
        | trueTerm() ->
          left("Cannot have restrictions on true")
        | falseTerm() ->
          left("Cannot have restrictions on false")
        | applicationTerm(nameTerm(q, _), args) ->
          right(relationMetaterm(^q, ^args, p.ast))
        | t -> left("Cannot treat " ++ justShow(t.pp) ++
                    " as a proposition")
        end; }
| tm::Term_c a::Ats_c
  { top.ast =
        case tm.ast of
        | trueTerm() ->
          left("Cannot have restrictions on true")
        | falseTerm() ->
          left("Cannot have restrictions on false")
        | applicationTerm(nameTerm(q, _), args) ->
          right(relationMetaterm(^q, ^args, a.ast))
        | t -> left("Cannot treat " ++ justShow(t.pp) ++
                    " as a proposition")
        end; }
| tm::Term_c h::Hashes_c
  { top.ast =
        case tm.ast of
        | trueTerm() ->
          left("Cannot have restrictions on true")
        | falseTerm() ->
          left("Cannot have restrictions on false")
        | applicationTerm(nameTerm(q, _), args) ->
          right(relationMetaterm(^q, ^args, h.ast))
        | t -> left("Cannot treat " ++ justShow(t.pp) ++
                    " as a proposition")
        end; }
--Projection
| args::ExpList_c '|{' ty::Id_t '}-' o::Term_c '~~>' t::Term_c
  { top.ast =
        right(projectionMetaterm(args.ast, toQName(ty.lexeme),
                                 o.ast, t.ast)); }
| args::ExpList_c '|{' ty::Qname_t '}-' o::Term_c '~~>' t::Term_c
  { top.ast =
        right(projectionMetaterm(args.ast, toQName(ty.lexeme),
                                 o.ast, t.ast)); }
| '|{' ty::Id_t '}-' o::Term_c '~~>' t::Term_c
  { top.ast =
        right(projectionMetaterm(emptyTermList(), toQName(ty.lexeme),
                                 o.ast, t.ast)); }
| '|{' ty::Qname_t '}-' o::Term_c '~~>' t::Term_c
  { top.ast =
        right(projectionMetaterm(emptyTermList(), toQName(ty.lexeme),
                                 o.ast, t.ast)); }
--Special relations
| t1::Term_c '+' t2::Term_c '=' t3::Term_c
  { top.ast = right(plusMetaterm(t1.ast, t2.ast, t3.ast)); }
| t1::Term_c '-' t2::Term_c '=' t3::Term_c
  { top.ast = right(minusMetaterm(t1.ast, t2.ast, t3.ast)); }
| t1::Term_c '*' t2::Term_c '=' t3::Term_c
  { top.ast = right(multiplyMetaterm(t1.ast, t2.ast, t3.ast)); }
| t1::Term_c '/' t2::Term_c '=' t3::Term_c
  { top.ast = right(divideMetaterm(t1.ast, t2.ast, t3.ast)); }
| t1::Term_c 'mod' t2::Term_c '=' t3::Term_c
  { top.ast = right(modulusMetaterm(t1.ast, t2.ast, t3.ast)); }
| t1::Term_c '<' t2::Term_c
  { top.ast = right(lessMetaterm(t1.ast, t2.ast)); }
| t1::Term_c '<=' t2::Term_c
  { top.ast = right(lessEqMetaterm(t1.ast, t2.ast)); }
| t1::Term_c '>' t2::Term_c
  { top.ast = right(greaterMetaterm(t1.ast, t2.ast)); }
| t1::Term_c '>=' t2::Term_c
  { top.ast = right(greaterEqMetaterm(t1.ast, t2.ast)); }
| t1::Term_c '++' t2::Term_c '=' t3::Term_c
  { top.ast = right(appendMetaterm(t1.ast, t2.ast, t3.ast,
                                   emptyRestriction())); }
| t1::Term_c '||' t2::Term_c '=' t3::Term_c
  { top.ast = right(orBoolMetaterm(t1.ast, t2.ast, t3.ast)); }
| t1::Term_c '&&' t2::Term_c '=' t3::Term_c
  { top.ast = right(andBoolMetaterm(t1.ast, t2.ast, t3.ast)); }
| '!' t1::Term_c '=' t2::Term_c
  { top.ast = right(notBoolMetaterm(t1.ast, t2.ast)); }
--Symmetry for the same
| t3::Term_c '=' t1::Term_c '+' t2::Term_c
  { top.ast = right(plusMetaterm(t1.ast, t2.ast, t3.ast)); }
| t3::Term_c '=' t1::Term_c '-' t2::Term_c
  { top.ast = right(minusMetaterm(t1.ast, t2.ast, t3.ast)); }
| t3::Term_c '=' t1::Term_c '*' t2::Term_c
  { top.ast = right(multiplyMetaterm(t1.ast, t2.ast, t3.ast)); }
| t3::Term_c '=' t1::Term_c '/' t2::Term_c
  { top.ast = right(divideMetaterm(t1.ast, t2.ast, t3.ast)); }
| t3::Term_c '=' t1::Term_c 'mod' t2::Term_c
  { top.ast = right(modulusMetaterm(t1.ast, t2.ast, t3.ast)); }
| t3::Term_c '=' t1::Term_c '++' t2::Term_c
  { top.ast = right(appendMetaterm(t1.ast, t2.ast, t3.ast,
                                   emptyRestriction())); }
| t3::Term_c '=' t1::Term_c '||' t2::Term_c
  { top.ast = right(orBoolMetaterm(t1.ast, t2.ast, t3.ast)); }
| t3::Term_c '=' t1::Term_c '&&' t2::Term_c
  { top.ast = right(andBoolMetaterm(t1.ast, t2.ast, t3.ast)); }
| t2::Term_c '=' '!' t1::Term_c
  { top.ast = right(notBoolMetaterm(t1.ast, t2.ast)); }





closed nonterminal Term_c with ast<Term>;
closed nonterminal MidTerm_c with ast<Term>;
closed nonterminal Exp_c with ast<Term>;
closed nonterminal ExpList_c with ast<TermList>;
closed nonterminal PairBody_c with ast<PairContents>;
closed nonterminal ListBody_c with ast<ListContents>;
closed nonterminal PAId_c with ast<Term>;


concrete productions top::Term_c
| t1::MidTerm_c '::' t2::Term_c
  { top.ast = consTerm(t1.ast, t2.ast); }
| e::MidTerm_c
  { top.ast = e.ast; }


concrete productions top::MidTerm_c
| e::Exp_c args::ExpList_c
  { top.ast = applicationTerm(e.ast, args.ast); }
| e::Exp_c
  { top.ast = e.ast; }


concrete productions top::Exp_c
| '(' t::Term_c ')'
  { top.ast = t.ast; }
| p::PAId_c
  { top.ast = p.ast; }
| 'nil'
  { top.ast = nilTerm(); }
--New for encoding:
{- This doesn't work with fromAbella, so it is in toAbella:
| i::Number_t
  { top.ast = intTerm(toInteger(i.lexeme)); }-}
| i::NegativeInteger_t
  { top.ast = intTerm(toInteger(i.lexeme)); }
| s::QuotedString_t
  { top.ast = stringTerm(unescapeString(substring(1, length(s.lexeme)-1, s.lexeme))); }
| 'true'
  { top.ast = trueTerm(); }
| 'false'
  { top.ast = falseTerm(); }
| '(' pairBody::PairBody_c ')'
  { top.ast = pairTerm(pairBody.ast); }
| '[' listBody::ListBody_c ']'
  { top.ast = listTerm(listBody.ast); }
| '[' ']'
  { top.ast = listTerm(emptyListContents()); }


concrete productions top::ExpList_c
| e::Exp_c el::ExpList_c
  { top.ast = consTermList(e.ast, el.ast); }
| e::Exp_c
  { top.ast = singleTermList(e.ast); }


concrete productions top::PairBody_c
| t1::Term_c ',' t2::Term_c
  { top.ast = addPairContents(t1.ast, singlePairContents(t2.ast)); }
| t::Term_c ',' rest::PairBody_c
  { top.ast = addPairContents(t.ast, rest.ast); }


concrete productions top::ListBody_c
| t::Term_c
  { top.ast = addListContents(t.ast, emptyListContents()); }
| t::Term_c ',' rest::ListBody_c
  { top.ast = addListContents(t.ast, rest.ast); }


concrete productions top::PAId_c
| l::Qname_t
  { top.ast = nameTerm(toQName(l.lexeme), nothingType()); }
| '(' l::Qname_t ':' t::Ty_c ')'
  { top.ast = nameTerm(toQName(l.lexeme), justType(t.ast)); }
| l::Id_t
  { top.ast = nameTerm(toQName(l.lexeme), nothingType()); }
| '(' l::Id_t ':' t::Ty_c ')'
  { top.ast = nameTerm(toQName(l.lexeme), justType(t.ast)); }
| '_'
  { top.ast = underscoreTerm(nothingType()); }
| '(' '_' ':' t::Ty_c ')'
  { top.ast = underscoreTerm(justType(t.ast)); }





closed nonterminal PTy_c with ast<Type>;
closed nonterminal ATy_c with ast<Type>;
closed nonterminal Ty_c with ast<Type>;


concrete productions top::PTy_c
| 'string'
  { top.ast = stringType(); }
| i::Id_t
  { top.ast = if isUpper(substring(0, 1, i.lexeme))
              then varType(i.lexeme)
              else nameType(toQName(i.lexeme)); }
| i::Qname_t
  { top.ast = nameType(toQName(i.lexeme)); }
| '(' t::Ty_c ')'
  { top.ast = t.ast; }


concrete productions top::ATy_c
| 'string'
  { top.ast = stringType(); }
| i::Id_t
  { top.ast = if isUpper(substring(0, 1, i.lexeme))
              then varType(i.lexeme)
              else nameType(toQName(i.lexeme)); }
| i::Qname_t
  { top.ast = nameType(toQName(i.lexeme)); }
| a::ATy_c p::PTy_c
  { top.ast = functorType(a.ast, p.ast); }


concrete productions top::Ty_c
| a::ATy_c
  { top.ast = a.ast; }
| t1::Ty_c '->' t2::Ty_c
  { top.ast = arrowType(t1.ast, t2.ast); }
| '(' t::Ty_c ')'
  { top.ast = t.ast; }





closed nonterminal Binder_c with ast<Binder>;
closed nonterminal BindingList_c with ast<Bindings>;
closed nonterminal BindingOne_c with ast<[(String, MaybeType)]>;
closed nonterminal BindingVars_c with ast<[String]>;


concrete productions top::Binder_c
| 'forall'
  { top.ast = forallBinder(); }
| 'exists'
  { top.ast = existsBinder(); }
| 'nabla'
  { top.ast = nablaBinder(); }


concrete productions top::BindingList_c
| b::BindingOne_c
  { top.ast = foldr(\ p::(String, MaybeType) rest::Bindings ->
                      addBindings(p.1, p.2, rest),
                    oneBinding(head(b.ast).1, head(b.ast).2),
                    tail(b.ast)); }
| b::BindingOne_c rest::BindingList_c
  { top.ast = foldr(\ p::(String, MaybeType) rest::Bindings ->
                      addBindings(p.1, p.2, rest),
                    rest.ast, b.ast); }


concrete productions top::BindingOne_c
| i::Id_t
  { top.ast = [(i.lexeme, nothingType())]; }
| '(' bv::BindingVars_c ':' t::Ty_c ')'
  { top.ast = map(\x::String -> (x, justType(t.ast)), bv.ast); }


concrete productions top::BindingVars_c
| i::Id_t
  { top.ast = [i.lexeme]; }
| i::Id_t rest::BindingVars_c
  { top.ast = i.lexeme::rest.ast; }





closed nonterminal Stars_c with ast<Restriction>, count;
closed nonterminal Ats_c with ast<Restriction>, count;
closed nonterminal Pluses_c with ast<Restriction>, count;
closed nonterminal Hashes_c with ast<Restriction>, count;


concrete productions top::Stars_c
| '*' rest::Stars_c
  {
    top.count = rest.count + 1;
    top.ast = starRestriction(top.count);
  }
| '*'
  {
    top.count = 1;
    top.ast = starRestriction(1);
  }


concrete productions top::Ats_c
| '@' rest::Ats_c
  {
    top.count = rest.count + 1;
    top.ast = atRestriction(top.count);
  }
| '@'
  {
    top.count = 1;
    top.ast = atRestriction(top.count);
  }


concrete productions top::Pluses_c
| '+' rest::Pluses_c
  {
    top.count = rest.count + 1;
    top.ast = plusRestriction(top.count);
  }
| '+'
  {
    top.count = 1;
    top.ast = plusRestriction(top.count);
  }


concrete productions top::Hashes_c
| '#' rest::Hashes_c
  {
    top.count = rest.count + 1;
    top.ast = hashRestriction(top.count);
  }
| '#'
  {
    top.count = 1;
    top.ast = hashRestriction(top.count);
  }

