grammar extensibella:toAbella:abstractSyntax;

--All full QNames, but otherwise the same
synthesized attribute full<a>::a;

attribute
   full<Defs>
occurs on Defs;

aspect production singleDefs
top::Defs ::= d::Def
{
  top.full = singleDefs(d.full);
}


aspect production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.full = consDefs(d.full, rest.full);
}




attribute
   full<Def>
occurs on Def;

aspect production factDef
top::Def ::= defRel::QName args::TermList
{
  top.full = factDef(defRel.fullRel.name, args.full);
}


aspect production ruleDef
top::Def ::= defRel::QName args::TermList body::Metaterm
{
  top.full = ruleDef(defRel.fullRel.name, args.full, body.full);
}





attribute
   full<ExtThms>
occurs on ExtThms;

aspect production endExtThms
top::ExtThms ::=
{
  top.full = endExtThms();
}


aspect production addExtThms
top::ExtThms ::= name::QName bindings::Bindings body::ExtBody
                 ons::InductionOns rest::ExtThms
{
  top.full =
      addExtThms(^fullName, ^bindings, body.full, ^ons, rest.full);
}





attribute
   full<ExtBody>
occurs on ExtBody;

aspect production endExtBody
top::ExtBody ::= conc::Metaterm
{
  top.full = endExtBody(conc.full);
}


aspect production addLabelExtBody
top::ExtBody ::= label::String m::Metaterm rest::ExtBody
{
  top.full = addLabelExtBody(label, m.full, rest.full);
}


aspect production addBasicExtBody
top::ExtBody ::= m::Metaterm rest::ExtBody
{
  top.full = addBasicExtBody(m.full, rest.full);
}


attribute
   full<Metaterm>
occurs on Metaterm;

aspect production relationMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.full =
      relationMetaterm(if rel.relFound then rel.fullRel.name else ^rel,
                       args.full, ^r);
}


aspect production extSizeMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.full =
      extSizeMetaterm(if rel.relFound then rel.fullRel.name else ^rel,
                      args.full, ^r);
}


aspect production projRelMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.full =
      projRelMetaterm(if rel.relFound then rel.fullRel.name else ^rel,
                      args.full, ^r);
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.full = ^top;
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.full = ^top;
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.full = eqMetaterm(t1.full, t2.full);
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.full = impliesMetaterm(t1.full, t2.full);
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.full = orMetaterm(t1.full, t2.full);
}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.full = andMetaterm(t1.full, t2.full);
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder bindings::Bindings body::Metaterm
{
  top.full = bindingMetaterm(^b, bindings.full, body.full);
}


aspect production projectionMetaterm
top::Metaterm ::= args::TermList ty::QName orig::Term proj::Term
{
  top.full = projectionMetaterm(args.full, ty.fullType.name,
                                orig.full, proj.full);
}


aspect production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = plusMetaterm(t1.full, t2.full, result.full);
}


aspect production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = minusMetaterm(t1.full, t2.full, result.full);
}


aspect production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = multiplyMetaterm(t1.full, t2.full, result.full);
}


aspect production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = divideMetaterm(t1.full, t2.full, result.full);
}


aspect production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = modulusMetaterm(t1.full, t2.full, result.full);
}


aspect production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.full = negateMetaterm(t.full, result.full);
}


aspect production lessMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.full = lessMetaterm(t1.full, t2.full);
}


aspect production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.full = lessEqMetaterm(t1.full, t2.full);
}


aspect production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.full = greaterMetaterm(t1.full, t2.full);
}


aspect production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.full = greaterEqMetaterm(t1.full, t2.full);
}


aspect production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term r::Restriction
{
  top.full = appendMetaterm(t1.full, t2.full, result.full, ^r);
}


aspect production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = orBoolMetaterm(t1.full, t2.full, result.full);
}


aspect production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = andBoolMetaterm(t1.full, t2.full, result.full);
}


aspect production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.full = notBoolMetaterm(t.full, result.full);
}





attribute
   full<Bindings>
occurs on Bindings;

aspect production oneBinding
top::Bindings ::= name::String mty::MaybeType
{
  top.full = oneBinding(name, mty.full);
}


aspect production addBindings
top::Bindings ::= name::String mty::MaybeType rest::Bindings
{
  top.full = addBindings(name, mty.full, rest.full);
}





attribute
   full<ExtIndBody>
occurs on ExtIndBody;

aspect production branchExtIndBody
top::ExtIndBody ::= e1::ExtIndBody e2::ExtIndBody
{
  top.full = branchExtIndBody(e1.full, e2.full);
}


aspect production emptyExtIndBody
top::ExtIndBody ::=
{
  top.full = emptyExtIndBody();
}


aspect production oneExtIndBody
top::ExtIndBody ::= boundVars::Bindings rel::QName relArgs::[String]
                    premises::ExtIndPremiseList ihNames::[String]
{
  top.full = oneExtIndBody(boundVars.full, rel.fullRel.name, relArgs,
                           premises.full, ihNames);
}





attribute
   full<ExtIndPremiseList>
occurs on ExtIndPremiseList;

aspect production emptyExtIndPremiseList
top::ExtIndPremiseList ::=
{
  top.full = emptyExtIndPremiseList();
}


aspect production addNameExtIndPremiseList
top::ExtIndPremiseList ::= name::String m::Metaterm
                           rest::ExtIndPremiseList
{
  top.full = addNameExtIndPremiseList(name, m.full, rest.full);
}


aspect production addExtIndPremiseList
top::ExtIndPremiseList ::= m::Metaterm rest::ExtIndPremiseList
{
  top.full = addExtIndPremiseList(m.full, rest.full);
}





attribute
   full<Term>
occurs on Term;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.full = applicationTerm(f.full, args.full);
}


aspect production nameTerm
top::Term ::= name::QName mty::MaybeType
{
  top.full =
      if (!name.isQualified && contains(name.shortName, top.boundNames)) ||
         !name.constrFound
      then nameTerm(^name, mty.full)
      else case name.fullConstr of
           | left(x) -> nameTerm(x.name, mty.full)
           | right(x) -> nameTerm(x.name, mty.full)
           end;
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  top.full = consTerm(t1.full, t2.full);
}


aspect production nilTerm
top::Term ::=
{
  top.full = ^top;
}


aspect production underscoreTerm
top::Term ::= mty::MaybeType
{
  top.full = ^top;
}


aspect production unknownITerm
top::Term ::= ty::QName
{
  top.full = unknownITerm(ty.fullType.name);
}


aspect production unknownKTerm
top::Term ::= ty::QName
{
  top.full = unknownKTerm(ty.fullType.name);
}


aspect production intTerm
top::Term ::= i::Integer
{
  top.full = ^top;
}


aspect production stringTerm
top::Term ::= contents::String
{
  top.full = ^top;
}


aspect production trueTerm
top::Term ::=
{
  top.full = ^top;
}


aspect production falseTerm
top::Term ::=
{
  top.full = ^top;
}


aspect production charTerm
top::Term ::= c::String
{
  top.full = ^top;
}


aspect production pairTerm
top::Term ::= contents::PairContents
{
  top.full = pairTerm(contents.full);
}


aspect production listTerm
top::Term ::= contents::ListContents
{
  top.full = listTerm(contents.full);
}





attribute
   full<ListContents>
occurs on ListContents;

aspect production emptyListContents
top::ListContents ::=
{
  top.full = emptyListContents();
}


aspect production addListContents
top::ListContents ::= hd::Term tl::ListContents
{
  top.full = addListContents(hd.full, tl.full);
}





attribute
   full<PairContents>
occurs on PairContents;

aspect production singlePairContents
top::PairContents ::= t::Term
{
  top.full = singlePairContents(t.full);
}


aspect production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  top.full = addPairContents(t.full, rest.full);
}





attribute
   full<TermList>
occurs on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  top.full = singleTermList(t.full);
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.full = consTermList(t.full, rest.full);
}


aspect production emptyTermList
top::TermList ::=
{
  top.full = emptyTermList();
}





attribute
   full<Type>
occurs on Type;

aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.full = arrowType(ty1.full, ty2.full);
}


aspect production nameType
top::Type ::= name::QName
{
  --fullType.type is guaranteed to be full
  top.full = name.fullType.type;
}


aspect production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.full = functorType(functorTy.full, argTy.full);
}


aspect production varType
top::Type ::= name::String
{
  top.full = ^top;
}


aspect production errorType
top::Type ::=
{
  top.full = ^top; --not sure this should be accessed
}


attribute
   full<TypeList>
occurs on TypeList;

aspect production emptyTypeList
top::TypeList ::=
{
  top.full = emptyTypeList();
}


aspect production addTypeList
top::TypeList ::= ty::Type rest::TypeList
{
  top.full = addTypeList(ty.full, rest.full);
}


attribute
   full<MaybeType>
occurs on MaybeType;

aspect production nothingType
top::MaybeType ::=
{
  top.full = nothingType();
}


aspect production justType
top::MaybeType ::= ty::Type
{
  top.full = justType(ty.full);
}





attribute
   full<ProofCommand>
occurs on ProofCommand;

aspect production inductionTactic
top::ProofCommand ::= h::HHint nl::[Integer]
{
  top.full = ^top;
}


aspect production coinductionTactic
top::ProofCommand ::= h::HHint
{
  top.full = ^top;
}


aspect production introsTactic
top::ProofCommand ::= names::[String]
{
  top.full = ^top;
}


aspect production applyTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> theorem::Clearable
                      args::ApplyArgs withs::Withs
{
  top.full = applyTactic(^h, depth, theorem.full, args.full, withs.full);
}


aspect production backchainTactic
top::ProofCommand ::= depth::Maybe<Integer> theorem::Clearable
                      withs::Withs
{
  top.full = backchainTactic(depth, theorem.full, withs.full);
}


aspect production caseTactic
top::ProofCommand ::= h::HHint hyp::String keep::Boolean
{
  top.full = ^top;
}


aspect production assertTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> m::Metaterm
{
  top.full = assertTactic(^h, depth, m.full);
}


aspect production existsTactic
top::ProofCommand ::= ew::EWitnesses
{
  top.full = existsTactic(ew.full);
}


aspect production witnessTactic
top::ProofCommand ::= ew::EWitnesses
{
  top.full = witnessTactic(ew.full);
}


aspect production searchTactic
top::ProofCommand ::=
{
  top.full = ^top;
}


aspect production searchDepthTactic
top::ProofCommand ::= n::Integer
{
  top.full = ^top;
}


aspect production searchWitnessTactic
top::ProofCommand ::= sw::SearchWitness
{
  top.full = searchWitnessTactic(sw.full);
}


aspect production asyncTactic
top::ProofCommand ::=
{
  top.full = ^top;
}


aspect production splitTactic
top::ProofCommand ::=
{
  top.full = ^top;
}


aspect production splitStarTactic
top::ProofCommand ::=
{
  top.full = ^top;
}


aspect production leftTactic
top::ProofCommand ::=
{
  top.full = ^top;
}


aspect production rightTactic
top::ProofCommand ::=
{
  top.full = ^top;
}


aspect production skipTactic
top::ProofCommand ::=
{
  top.full = ^top;
}


aspect production admitTactic
top::ProofCommand ::=
{
  top.full = ^top;
}


aspect production abortCommand
top::ProofCommand ::=
{
  top.full = ^top;
}


aspect production undoCommand
top::ProofCommand ::=
{
  top.full = ^top;
}


aspect production clearCommand
top::ProofCommand ::= removes::[String] hasArrow::Boolean
{
  top.full = ^top;
}


aspect production renameTactic
top::ProofCommand ::= original::String renamed::String
{
  top.full = ^top;
}


aspect production abbrevCommand
top::ProofCommand ::= hyps::[String] newText::String
{
  top.full = ^top;
}


aspect production unabbrevCommand
top::ProofCommand ::= hyps::[String]
{
  top.full = ^top;
}


aspect production permuteTactic
top::ProofCommand ::= names::[String] hyp::Maybe<String>
{
  top.full = ^top;
}


aspect production unfoldStepsTactic
top::ProofCommand ::= steps::Integer all::Boolean
{
  top.full = ^top;
}


aspect production unfoldIdentifierTactic
top::ProofCommand ::= id::QName all::Boolean
{
  top.full = unfoldIdentifierTactic(id.fullRel.name, all);
}


aspect production unfoldTactic
top::ProofCommand ::= all::Boolean
{
  top.full = ^top;
}


aspect production computeTactic
top::ProofCommand ::= hyp::String
{
  top.full = ^top;
}


attribute
   full<Clearable>
occurs on Clearable;

aspect production clearable
top::Clearable ::= star::Boolean hyp::QName instantiation::TypeList
{
  top.full =
      clearable(star,
                if hyp.isQualified || hypFound || null(possibleThms)
                then ^hyp
                else head(possibleThms).1, instantiation.full);
}


attribute
   full<ApplyArgs>
occurs on ApplyArgs;

aspect production endApplyArgs
top::ApplyArgs ::=
{
  top.full = ^top;
}


aspect production addApplyArgs
top::ApplyArgs ::= a::ApplyArg rest::ApplyArgs
{
  top.full = addApplyArgs(a.full, rest.full);
}


attribute
   full<ApplyArg>
occurs on ApplyArg;

aspect production hypApplyArg
top::ApplyArg ::= hyp::String instantiation::TypeList
{
  top.full = hypApplyArg(hyp, instantiation.full);
}


aspect production starApplyArg
top::ApplyArg ::= name::String instantiation::TypeList
{
  top.full = starApplyArg(name, instantiation.full);
}


attribute
   full<Withs>
occurs on Withs;

aspect production endWiths
top::Withs ::=
{
  top.full = ^top;
}


aspect production addWiths
top::Withs ::= name::String term::Term rest::Withs
{
  top.full = addWiths(name, term.full, rest.full);
}


attribute
   full<EWitnesses>
occurs on EWitnesses;

aspect production oneEWitnesses
top::EWitnesses ::= e::EWitness
{
  top.full = oneEWitnesses(e.full);
}


aspect production addEWitnesses
top::EWitnesses ::= e::EWitness rest::EWitnesses
{
  top.full = addEWitnesses(e.full, rest.full);
}


attribute
   full<EWitness>
occurs on EWitness;

aspect production termEWitness
top::EWitness ::= t::Term
{
  top.full = termEWitness(t.full);
}


aspect production nameEWitness
top::EWitness ::= name::String t::Term
{
  top.full = nameEWitness(name, t.full);
}


attribute
   full<SearchWitness>
occurs on SearchWitness;

aspect production trueSearchWitness
top::SearchWitness ::=
{
  top.full = ^top;
}


aspect production applySearchWitness
top::SearchWitness ::= name::String
{
  top.full = ^top;
}


aspect production leftSearchWitness
top::SearchWitness ::= sub::SearchWitness
{
  top.full = leftSearchWitness(sub.full);
}


aspect production rightSearchWitness
top::SearchWitness ::= sub::SearchWitness
{
  top.full = rightSearchWitness(sub.full);
}


aspect production splitSearchWitness
top::SearchWitness ::= l::SearchWitness r::SearchWitness
{
  top.full = splitSearchWitness(l.full, r.full);
}


aspect production introsSearchWitness
top::SearchWitness ::= names::[String] sub::SearchWitness
{
  top.full = introsSearchWitness(names, sub.full);
}


aspect production forallSearchWitness
top::SearchWitness ::= names::[String] sub::SearchWitness
{
  top.full = forallSearchWitness(names, sub.full);
}


aspect production existsSearchWitness
top::SearchWitness ::= withs::Withs sub::SearchWitness
{
  top.full = existsSearchWitness(withs.full, sub.full);
}


aspect production unfoldSearchWitness
top::SearchWitness ::= name::String n::Integer swl::[SearchWitness]
{
  top.full = unfoldSearchWitness(name, n,
                map(\ s::SearchWitness ->
                      decorate s with {
                        typeEnv = top.typeEnv;
                        relationEnv = top.relationEnv;
                        constructorEnv = top.constructorEnv;
                        boundNames = top.boundNames;
                      }.full,
                    swl));
}


aspect production starSearchWitness
top::SearchWitness ::=
{
  top.full = ^top;
}


aspect production eqSearchWitness
top::SearchWitness ::=
{
  top.full = ^top;
}





attribute
   full<NoOpCommand>
occurs on NoOpCommand;

aspect production setCommand
top::NoOpCommand ::= opt::String val::String
{
  top.full = ^top;
}


aspect production showCommand
top::NoOpCommand ::= theoremName::QName
{
  top.full = showCommand(head(possibleThms).1);
}


aspect production quitCommand
top::NoOpCommand ::=
{
  top.full = ^top;
}


aspect production backCommand
top::NoOpCommand ::= n::Integer
{
  top.full = ^top;
}


aspect production resetCommand
top::NoOpCommand ::=
{
  top.full = ^top;
}


aspect production showCurrentCommand
top::NoOpCommand ::=
{
  top.full = ^top;
}





attribute
   full<ProofState>
occurs on ProofState;

aspect production proofInProgress
top::ProofState ::= subgoalNum::SubgoalNum currGoal::CurrentGoal
                    futureGoals::[Subgoal]
{
  top.full = proofInProgress(subgoalNum, currGoal.full, futureGoals,
                             isAbellaForm = top.isAbellaForm);
}


aspect production noProof
top::ProofState ::=
{
  top.full = ^top;
}


aspect production proofCompleted
top::ProofState ::=
{
  top.full = ^top;
}


aspect production proofAborted
top::ProofState ::=
{
  top.full = ^top;
}





attribute
   full<CurrentGoal>
occurs on CurrentGoal;

aspect production currentGoal
top::CurrentGoal ::= vars::[String] ctx::Context goal::Metaterm
{
  top.full = currentGoal(vars, ctx.full, goal.full);
}





attribute
   full<Context>
occurs on Context;

aspect production emptyContext
top::Context ::=
{
  top.full = emptyContext();
}


aspect production singleContext
top::Context ::= h::Hypothesis
{
  top.full = singleContext(h.full);
}


aspect production branchContext
top::Context ::= c1::Context c2::Context
{
  top.full = branchContext(c1.full, c2.full);
}





attribute
   full<Hypothesis>
occurs on Hypothesis;

aspect production metatermHyp
top::Hypothesis ::= name::String body::Metaterm
{
  top.full = metatermHyp(name, body.full);
}
