grammar extensibella:toAbella:abstractSyntax;


attribute
   toAbella<Metaterm>, toAbellaMsgs,
   proverState
occurs on Metaterm;
propagate proverState, toAbellaMsgs on Metaterm;

aspect production relationMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.toAbella = relationMetaterm(rel.fullRel.name, args.toAbella, ^r);

  top.toAbellaMsgs <- rel.relErrors;
}


aspect production extSizeMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.toAbella = relationMetaterm(extSizeQName(rel.fullRel.name.sub),
                                  args.toAbella, ^r);

  top.toAbellaMsgs <- rel.relErrors;
  top.toAbellaMsgs <-
      if !rel.relFound ||
         findExtSizeGroup(rel.fullRel.name, top.proverState).isJust
      then []
      else [errorMsg("Ext Size is not defined for " ++
               justShow(rel.fullRel.name.pp))];
}


aspect production projRelMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.toAbella = relationMetaterm(projRelQName(rel.fullRel.name.sub),
                                  args.toAbella, ^r);

  top.toAbellaMsgs <- rel.relErrors;
  top.toAbellaMsgs <-
      if !rel.relFound ||
         findProjRelGroup(rel.fullRel.name, top.proverState).isJust
      then []
      else [errorMsg("Projection version is not defined for " ++
               justShow(rel.fullRel.name.pp))];
  --defined, but currently being proven, so not in ExtIndGroups yet
  local projRelInState::Boolean =
      contains(rel.fullRel.name, top.proverState.state.projRels) ||
      contains(^rel, top.proverState.state.projRels);

  top.projRels := [^rel];
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.toAbella = ^top;
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.toAbella = ^top;
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.toAbella = eqMetaterm(t1.toAbella, t2.toAbella);
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.toAbella = impliesMetaterm(t1.toAbella, t2.toAbella);
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.toAbella = orMetaterm(t1.toAbella, t2.toAbella);
}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.toAbella = andMetaterm(t1.toAbella, t2.toAbella);
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder bindings::Bindings body::Metaterm
{
  top.toAbella = bindingMetaterm(^b, bindings.toAbella, body.toAbella);
}


aspect production projectionMetaterm
top::Metaterm ::= args::TermList ty::QName orig::Term proj::Term
{
  top.toAbella =
      relationMetaterm(
         projName(ty.fullType.name),
         buildApplicationArgs(args.toAbella.toList ++
                              [orig.toAbella, proj.toAbella]),
         emptyRestriction());

  top.toAbellaMsgs <- ty.typeErrors;
  top.toAbellaMsgs <-
      if !ty.typeFound
      then [] --covered by ty.typeErrors
      else if ty.fullType.isLangType
      then [] --projectable
      else [errorMsg("Type " ++ justShow(ty.fullType.name.pp) ++
               " is not part of the language and cannot be projected")];
}


aspect production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(integerAdditionName),
         buildApplicationArgs([t1.toAbella, t2.toAbella,
                              result.toAbella]),
         emptyRestriction());
}


aspect production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(integerSubtractionName),
         buildApplicationArgs([t1.toAbella, t2.toAbella,
                              result.toAbella]),
         emptyRestriction());
}


aspect production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(integerMultiplicationName),
         buildApplicationArgs([t1.toAbella, t2.toAbella,
                              result.toAbella]),
         emptyRestriction());
}


aspect production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(integerDivisionName),
         buildApplicationArgs([t1.toAbella, t2.toAbella,
                              result.toAbella]),
         emptyRestriction());
}


aspect production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(integerModulusName),
         buildApplicationArgs([t1.toAbella, t2.toAbella,
                              result.toAbella]),
         emptyRestriction());
}


aspect production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(integerNegateName),
         buildApplicationArgs([t.toAbella, result.toAbella]),
         emptyRestriction());
}


aspect production lessMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(integerLessName),
         buildApplicationArgs([t1.toAbella, t2.toAbella]),
         emptyRestriction());
}


aspect production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(integerLessEqName),
         buildApplicationArgs([t1.toAbella, t2.toAbella]),
         emptyRestriction());
}


aspect production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(integerGreaterName),
         buildApplicationArgs([t1.toAbella, t2.toAbella]),
         emptyRestriction());
}


aspect production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(integerGreaterEqName),
         buildApplicationArgs([t1.toAbella, t2.toAbella]),
         emptyRestriction());
}


aspect production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term r::Restriction
{
  top.toAbella =
      relationMetaterm(
         toQName(appendName),
         buildApplicationArgs([t1.toAbella, t2.toAbella,
                              result.toAbella]),
         ^r);
}


aspect production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(orName),
         buildApplicationArgs([t1.toAbella, t2.toAbella,
                              result.toAbella]),
         emptyRestriction());
}


aspect production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(andName),
         buildApplicationArgs([t1.toAbella, t2.toAbella,
                              result.toAbella]),
         emptyRestriction());
}


aspect production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.toAbella =
      relationMetaterm(
         toQName(notName),
         buildApplicationArgs([t.toAbella, result.toAbella]),
         emptyRestriction());
}





attribute
   toAbella<Bindings>, toAbellaMsgs
occurs on Bindings;
propagate toAbellaMsgs on Bindings;

aspect production oneBinding
top::Bindings ::= name::String mty::MaybeType
{
  top.toAbella = oneBinding(name, mty.toAbella);
}


aspect production addBindings
top::Bindings ::= name::String mty::MaybeType rest::Bindings
{
  top.toAbella = addBindings(name, mty.toAbella, rest.toAbella);
}





attribute
   toAbella<Term>, toAbellaMsgs,
   headRel,
   proverState
occurs on Term;
propagate proverState, toAbellaMsgs on Term;

synthesized attribute headRel::Maybe<QName>;

aspect default production
top::Term ::=
{
  top.headRel = nothing();
}


aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.toAbella = applicationTerm(f.toAbella, args.toAbella);

  top.headRel = f.headRel;
}


aspect production nameTerm
top::Term ::= name::QName mty::MaybeType
{
  top.toAbella =
      if name.isQualified
      then nameTerm(^name, mty.toAbella)
      else if contains(name.shortName, top.boundNames)
      then nameTerm(^name, mty.toAbella) --assume it refers to binding
      else --if not bound, assume defined name to look up
           nameTerm(
              case name.fullConstr of
              | left(x) -> x.name
              | right(x) -> x.name
              end, mty.toAbella);

  top.toAbellaMsgs <-
      if contains(name.shortName, top.boundNames)
      then []
      else name.constrErrors;

  top.headRel = just(^name);
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  top.toAbella = consTerm(t1.toAbella, t2.toAbella);
}


aspect production nilTerm
top::Term ::=
{
  top.toAbella = ^top;
}


aspect production underscoreTerm
top::Term ::= mty::MaybeType
{
  top.toAbella = underscoreTerm(mty.toAbella);
}


aspect production unknownITerm
top::Term ::= ty::QName
{
  top.toAbella = nameTerm(ty.fullType.unknownConstrI, nothingType());
  top.toAbellaMsgs <- ty.typeErrors;
  top.toAbellaMsgs <-
      if !ty.typeFound
      then [] --ty.typeErrors gives this
      else if ty.fullType.isLangType
      then []
      else [errorMsg("Cannot have an unknown I term for type " ++
               justShow(ty.fullType.name.pp) ++ " that is not " ++
               "defined as part of the language")];
}


aspect production unknownKTerm
top::Term ::= rel::QName
{
  top.toAbella = nameTerm(rel.fullRel.unknownConstrK, nothingType());
  top.toAbellaMsgs <- rel.relErrors;
  top.toAbellaMsgs <-
      if !rel.relFound
      then [] --rel.relErrors gives this
      else if rel.fullRel.isExtensible
      then []
      else [errorMsg("Cannot have an unknown K term for relation " ++
               justShow(rel.fullRel.name.pp) ++ " that is not " ++
               "extensible")];
}


aspect production intTerm
top::Term ::= i::Integer
{
  top.toAbella = integerToIntegerTerm(i);
}


aspect production stringTerm
top::Term ::= contents::String
{
  local charOrdinals::[Integer] = stringToChars(contents);
  local charConstants::[String] = map(ordinalToCharConstructor, charOrdinals);
  local charTerms::[Term] = map(basicNameTerm(_), charConstants);
  top.toAbella = foldr(consTerm, nilTerm(), charTerms);
}


aspect production trueTerm
top::Term ::=
{
  top.toAbella = basicNameTerm(trueName);
}


aspect production falseTerm
top::Term ::=
{
  top.toAbella = basicNameTerm(falseName);
}


aspect production charTerm
top::Term ::= c::String
{
  top.toAbella = error("Should not have charTerm in toAbella");
}


aspect production pairTerm
top::Term ::= contents::PairContents
{
  top.toAbella = contents.toAbella;
}


aspect production listTerm
top::Term ::= contents::ListContents
{
  top.toAbella = contents.toAbella;
}





attribute
   toAbella<Term>,
   proverState
occurs on ListContents;
propagate proverState on ListContents;

aspect production emptyListContents
top::ListContents ::=
{
  top.toAbella = nilTerm();
}


aspect production addListContents
top::ListContents ::= hd::Term tl::ListContents
{
  top.toAbella = consTerm(hd.toAbella, tl.toAbella);
}





attribute
   toAbella<Term>,
   proverState
occurs on PairContents;
propagate proverState on PairContents;

aspect production singlePairContents
top::PairContents ::= t::Term
{
  top.toAbella = t.toAbella;
}


aspect production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  top.toAbella =
      buildApplication(
         basicNameTerm(pairConstructorName),
         [t.toAbella, rest.toAbella]);
}





attribute
   toAbella<TermList>, toAbellaMsgs,
   proverState
occurs on TermList;
propagate proverState, toAbellaMsgs on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  top.toAbella = singleTermList(t.toAbella);
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.toAbella = consTermList(t.toAbella, rest.toAbella);
}


aspect production emptyTermList
top::TermList ::=
{
  top.toAbella = emptyTermList();
}

