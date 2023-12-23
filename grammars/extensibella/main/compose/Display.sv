grammar extensibella:main:compose;

{-
  We need a way to put the composed proofs in the file.  We could do
  that with .abella_pp, but that makes it hard to read, so we define
  our own here.
-}

synthesized attribute simple_pp::String occurs on
   SubQName, QName, Term, TermList, Metaterm, Bindings, Type,
   MaybeType, TypeList, ProofCommand, Withs, Clearable, ApplyArg,
   ApplyArgs, EWitnesses, EWitness, NoOpCommand, TopCommand, Defs,
   Def, AnyCommand, ListOfCommands;

aspect production baseName
top::SubQName ::= name::String
{
  top.simple_pp = name;
}


aspect production addModule
top::SubQName ::= name::String rest::SubQName
{
  top.simple_pp = name ++ name_sep ++ rest.simple_pp;
}


aspect production fixQName
top::QName ::= rest::SubQName
{
  top.simple_pp = rest.simple_pp;
}


aspect production extQName
top::QName ::= pc::Integer rest::SubQName
{
  top.simple_pp = rest.simple_pp;
}


aspect production transQName
top::QName ::= rest::SubQName
{
  top.simple_pp = rest.simple_pp;
}


aspect production tyQName
top::QName ::= rest::SubQName
{
  top.simple_pp = rest.simple_pp;
}


aspect production unknownQName
top::QName ::= rest::SubQName
{
  top.simple_pp = error("unknownQName.simple_pp");
}


aspect production extSizeQName
top::QName ::= rest::SubQName
{
  top.simple_pp = rest.simple_pp ++ "__ES";
}


aspect production transRelQName
top::QName ::= rest::SubQName
{
  top.simple_pp = rest.simple_pp ++ "__T";
}


aspect production libQName
top::QName ::= rest::SubQName
{
  --can't change library names
  top.simple_pp = top.abella_pp;
}


aspect production basicQName
top::QName ::= rest::SubQName
{
  top.simple_pp =
      if sameModule(extensibellaStdLib, top)
      then top.abella_pp --stdLib names stay same
      else rest.simple_pp;
}





aspect default production
top::Metaterm ::=
{
  top.simple_pp =
      error("non-Abella metaterm.simple_pp (" ++ justShow(top.pp) ++ ")");
}


aspect production relationMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.simple_pp = rel.simple_pp ++ " " ++ args.simple_pp ++ r.abella_pp;
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.simple_pp = "true";
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.simple_pp = "false";
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.simple_pp = t1.simple_pp ++ " = " ++ t2.simple_pp;
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.simple_pp =
      (if t1.isAtomic then t1.simple_pp
       else "(" ++ t1.simple_pp ++ ")") ++ " -> " ++ t2.simple_pp;
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.simple_pp =
      (if t1.isAtomic then t1.simple_pp
       else "(" ++ t1.simple_pp ++ ")") ++ " \\/ " ++
      (if t2.isAtomic then t2.simple_pp
       else "(" ++ t2.simple_pp ++ ")");
}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.simple_pp =
      (if t1.isAtomic then t1.simple_pp
       else "(" ++ t1.simple_pp ++ ")") ++ " /\\ " ++
      (if t2.isAtomic then t2.simple_pp
       else "(" ++ t2.simple_pp ++ ")");
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder nameBindings::Bindings body::Metaterm
{
  top.simple_pp =
      b.abella_pp ++ " " ++ nameBindings.simple_pp ++ ", " ++
      body.simple_pp;
}


aspect production oneBinding
top::Bindings ::= name::String mty::MaybeType
{
  top.simple_pp =
      if mty.isJust
      then "(" ++ name ++ " : " ++ mty.simple_pp ++ ")"
      else name;
}


aspect production extensibella:common:abstractSyntax:addBindings
top::Bindings ::= name::String mty::MaybeType rest::Bindings
{
  top.simple_pp =
      (if mty.isJust
       then "(" ++ name ++ " : " ++ mty.simple_pp ++ ")"
       else name) ++ " " ++ rest.simple_pp;
}





aspect default production
top::Term ::=
{
  top.simple_pp =
      error("non-Abella term.simple_pp (" ++ justShow(top.pp) ++ ")");
}


aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.simple_pp =
      (if f.isAtomic then f.simple_pp else "(" ++ f.simple_pp ++ ")") ++
      " " ++ args.simple_pp;
}


aspect production nameTerm
top::Term ::= name::QName mty::MaybeType
{
  top.simple_pp =
      if mty.isJust
      then "(" ++ name.simple_pp ++ " : " ++ mty.simple_pp ++ ")"
      else name.simple_pp;
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  top.simple_pp =
      (if t1.isAtomic then t1.simple_pp
       else "(" ++ t1.simple_pp ++ ")") ++ "::" ++
      (if t2.isAtomic then t2.simple_pp
       else "(" ++ t2.simple_pp ++ ")");
}


aspect production nilTerm
top::Term ::=
{
  top.simple_pp = "nil";
}


aspect production singleTermList
top::TermList ::= t::Term
{
  top.simple_pp =
      if t.isAtomic then t.simple_pp else "(" ++ t.simple_pp ++ ")";
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.simple_pp =
      (if t.isAtomic then t.simple_pp else "(" ++ t.simple_pp ++ ")") ++
      " " ++ rest.simple_pp;
}


aspect production emptyTermList
top::TermList ::=
{
  top.simple_pp = "";
}





aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.simple_pp =
      (if ty1.isAtomic then ty1.simple_pp
       else "(" ++ ty1.simple_pp ++ ")" ) ++ " -> " ++ ty2.simple_pp;
}


aspect production nameType
top::Type ::= name::QName
{
  top.simple_pp = name.simple_pp;
}


aspect production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.simple_pp = functorTy.simple_pp ++ " " ++
                  if argTy.isAtomic then argTy.simple_pp
                  else "(" ++ argTy.simple_pp ++ ")";
}


aspect production varType
top::Type ::= name::String
{
  top.simple_pp = name;
}


aspect production errorType
top::Type ::=
{
  top.simple_pp = error("errorType.simple_pp");
}


aspect production emptyTypeList
top::TypeList ::=
{
  top.simple_pp = "";
}


aspect production addTypeList
top::TypeList ::= ty::Type rest::TypeList
{
  top.simple_pp = if rest.len == 0
                  then ty.simple_pp
                  else ty.simple_pp ++ ", " ++ rest.simple_pp;
}


aspect production nothingType
top::MaybeType ::=
{
  top.simple_pp = "";
}


aspect production justType
top::MaybeType ::= ty::Type
{
  top.simple_pp = ty.simple_pp;
}





aspect production emptyListOfCommands
top::ListOfCommands ::=
{
  top.simple_pp = "";
}


aspect production addListOfCommands
top::ListOfCommands ::= c::AnyCommand rest::ListOfCommands
{
  top.simple_pp = c.simple_pp ++ rest.simple_pp;
}





aspect production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.simple_pp = c.simple_pp;
}


aspect production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.simple_pp = c.simple_pp;
}


aspect production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.simple_pp = c.simple_pp;
}


aspect production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.simple_pp = error("anyParseFailure.simple_pp");
}





aspect default production
top::TopCommand ::=
{
  top.simple_pp =
      error("non-Abella top command.simple_pp (" ++ justShow(top.pp) ++ ")");
}


aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.simple_pp = "Theorem " ++ name.simple_pp ++
      (if null(params) then "" else " [" ++ implode(", ", params) ++ "]") ++
      " : " ++ body.simple_pp ++ ".\n";
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.simple_pp = "Define " ++
      implode(",\n      ",
         map(\ p::(QName, Type) ->
               p.1.simple_pp ++ " : " ++ p.2.simple_pp, preds)) ++
      " by " ++ defs.simple_pp ++ ".\n";
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.simple_pp = "Codefine " ++
      implode(",\n        ",
         map(\ p::(QName, Type) ->
               p.1.simple_pp ++ " : " ++ p.2.simple_pp, preds)) ++
      " by " ++ defs.simple_pp ++ ".\n";
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.simple_pp = "Query " ++ m.simple_pp ++ ".\n";
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  top.simple_pp = "Split " ++ theoremName.simple_pp ++ " as " ++
      implode(", ", map((.simple_pp), newTheoremNames)) ++ ".\n";
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.simple_pp = error("closeCommand.simple_pp");
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.simple_pp = "Kind " ++ implode(", ", map((.simple_pp), names)) ++
                  "   " ++ k.abella_pp ++ ".\n";
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.simple_pp = "Type " ++ implode(", ", map((.simple_pp), names)) ++
                  "   " ++ ty.simple_pp ++ ".\n";
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.simple_pp = top.abella_pp;
}



aspect production singleDefs
top::Defs ::= d::Def
{
  top.simple_pp = d.simple_pp;
}


aspect production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.simple_pp = d.simple_pp ++ ";\n" ++ rest.simple_pp;
}


aspect production factDef
top::Def ::= defRel::QName args::TermList
{
  top.simple_pp = defRel.simple_pp ++ " " ++ args.simple_pp;
}


aspect production ruleDef
top::Def ::= defRel::QName args::TermList body::Metaterm
{
  top.simple_pp = defRel.simple_pp ++ " " ++ args.simple_pp ++
      " := " ++ body.simple_pp;
}





aspect production setCommand
top::NoOpCommand ::= opt::String val::String
{
  top.simple_pp = top.abella_pp;
}


aspect production showCommand
top::NoOpCommand ::= theoremName::QName
{
  top.simple_pp = "Show " ++ theoremName.simple_pp ++ ".\n";
}


aspect production quitCommand
top::NoOpCommand ::=
{
  top.simple_pp = "Quit.\n";
}


aspect production backCommand
top::NoOpCommand ::= n::Integer
{
  top.simple_pp = top.abella_pp;
}


aspect production resetCommand
top::NoOpCommand ::=
{
  top.simple_pp = top.abella_pp;
}


aspect production showCurrentCommand
top::NoOpCommand ::=
{
  top.simple_pp = error("showCurrentCommand.simple_pp");
}





aspect default production
top::ProofCommand ::=
{
  top.simple_pp =
      error("non-Abella proof command.simple_pp (" ++ justShow(top.pp) ++ ")");
}


aspect production inductionTactic
top::ProofCommand ::= h::HHint nl::[Integer]
{
  top.simple_pp = top.abella_pp;
}


aspect production coinductionTactic
top::ProofCommand ::= h::HHint
{
  top.simple_pp = top.abella_pp;
}


aspect production introsTactic
top::ProofCommand ::= names::[String]
{
  top.simple_pp = top.abella_pp;
}


aspect production applyTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> theorem::Clearable
                      args::ApplyArgs withs::Withs
{
  top.simple_pp =
      h.abella_pp ++ "apply " ++
      (if depth.isJust then toString(depth.fromJust) ++ " " else "") ++
      theorem.simple_pp ++
      (if args.len == 0 then "" else " to " ++ args.simple_pp) ++
      (if withs.len == 0 then "" else " with " ++ withs.simple_pp) ++ ". ";
}


aspect production backchainTactic
top::ProofCommand ::= depth::Maybe<Integer> theorem::Clearable withs::Withs
{
  top.simple_pp = "backchain " ++
      (if depth.isJust then toString(depth.fromJust) ++ " " else "") ++
      theorem.simple_pp ++
      (if withs.len == 0 then "" else " with " ++ withs.simple_pp) ++ ". ";
}


aspect production caseTactic
top::ProofCommand ::= h::HHint hyp::String keep::Boolean
{
  top.simple_pp = h.abella_pp ++ " case " ++ hyp ++
      (if keep then " (keep)" else "") ++ ". ";
}


aspect production assertTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> m::Metaterm
{
  top.simple_pp = h.abella_pp ++ "assert " ++
      (if depth.isJust then toString(depth.fromJust) ++ " " else "") ++
      m.simple_pp ++ ". ";
}


aspect production existsTactic
top::ProofCommand ::= ew::EWitnesses
{
  top.simple_pp = "exists " ++ ew.simple_pp ++ ". ";
}


aspect production witnessTactic
top::ProofCommand ::= ew::EWitnesses
{
  top.simple_pp = "witness " ++ ew.simple_pp ++ ". ";
}


aspect production searchTactic
top::ProofCommand ::=
{
  top.simple_pp = "search. ";
}


aspect production searchDepthTactic
top::ProofCommand ::= n::Integer
{
  top.simple_pp = "search " ++ toString(n) ++ ". ";
}


aspect production splitTactic
top::ProofCommand ::=
{
  top.simple_pp = "split. ";
}


aspect production splitStarTactic
top::ProofCommand ::=
{
  top.simple_pp = "split*. ";
}


aspect production leftTactic
top::ProofCommand ::=
{
  top.simple_pp = "left. ";
}


aspect production rightTactic
top::ProofCommand ::=
{
  top.simple_pp = "right. ";
}


aspect production skipTactic
top::ProofCommand ::=
{
  top.simple_pp = "skip. ";
}


aspect production abortCommand
top::ProofCommand ::=
{
  top.simple_pp = "abort. ";
}


aspect production undoCommand
top::ProofCommand ::=
{
  top.simple_pp = "undo. ";
}


aspect production clearCommand
top::ProofCommand ::= removes::[String] hasArrow::Boolean
{
  top.simple_pp = top.abella_pp;
}


aspect production unfoldStepsTactic
top::ProofCommand ::= steps::Integer all::Boolean
{
  top.simple_pp = top.abella_pp;
}


aspect production unfoldIdentifierTactic
top::ProofCommand ::= id::QName all::Boolean
{
  top.simple_pp =
      "unfold " ++ id.simple_pp ++ if all then " (all). "
                                          else ". ";
}


aspect production unfoldTactic
top::ProofCommand ::= all::Boolean
{
  top.simple_pp = top.abella_pp;
}



aspect production clearable
top::Clearable ::= star::Boolean hyp::QName instantiation::TypeList
{
  top.simple_pp = (if star then "*" else "") ++ hyp.simple_pp ++
      (if instantiation.len == 0 then ""
       else "[" ++ instantiation.simple_pp ++ "]");
}



aspect production endApplyArgs
top::ApplyArgs ::=
{
  top.simple_pp = "";
}


aspect production addApplyArgs
top::ApplyArgs ::= a::ApplyArg rest::ApplyArgs
{
  top.simple_pp = a.simple_pp ++
      if rest.len == 0 then "" else  " " ++ rest.simple_pp;
}


aspect production hypApplyArg
top::ApplyArg ::= hyp::String instantiation::TypeList
{
  top.simple_pp = hyp ++ if instantiation.len == 0
                         then ""
                         else "[" ++ instantiation.simple_pp ++ "]";
}


aspect production starApplyArg
top::ApplyArg ::= name::String instantiation::TypeList
{
  top.simple_pp = "*" ++ name ++ if instantiation.len == 0
                                 then ""
                                 else "[" ++ instantiation.simple_pp ++ "]";
}



aspect production endWiths
top::Withs ::=
{
  top.simple_pp = "";
}


aspect production addWiths
top::Withs ::= name::String term::Term rest::Withs
{
  top.simple_pp = name ++ " = " ++ term.simple_pp ++
      if rest.len == 0 then "" else ", " ++ rest.simple_pp;
}



aspect production oneEWitnesses
top::EWitnesses ::= e::EWitness
{
  top.simple_pp = e.simple_pp;
}


aspect production addEWitnesses
top::EWitnesses ::= e::EWitness rest::EWitnesses
{
  top.simple_pp = e.simple_pp ++ ", " ++ rest.simple_pp;
}


aspect production termEWitness
top::EWitness ::= t::Term
{
  top.simple_pp = t.simple_pp;
}


aspect production nameEWitness
top::EWitness ::= name::String t::Term
{
  top.simple_pp = name ++ " = " ++ t.simple_pp;
}
