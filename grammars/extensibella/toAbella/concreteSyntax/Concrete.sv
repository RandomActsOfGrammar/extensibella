grammar extensibella:toAbella:concreteSyntax;






closed nonterminal ModuleDecl_c
   layout {Whitespace_t, BlockComment_t, OneLineComment_t}
   with ast<Maybe<QName>>; --just if module decl, nothing if quit

concrete productions top::ModuleDecl_c
| 'Module' q::Qname_t '.'
  { top.ast = just(toQName(q.lexeme)); }
| 'Module' q::Id_t '.' --Because Qname_t assumes at least one colon
  { top.ast = just(toQName(q.lexeme)); }
| 'Quit' '.'
  { top.ast = nothing(); }






closed nonterminal FullFile_c
   layout {Whitespace_t, BlockComment_t, OneLineComment_t}
   with ast<(Maybe<QName>, ListOfCommands)>;
closed nonterminal ListOfCommands_c
   layout {Whitespace_t, BlockComment_t, OneLineComment_t}
   with ast<ListOfCommands>;

concrete productions top::FullFile_c
| m::ModuleDecl_c contents::ListOfCommands_c
  { top.ast = (m.ast, contents.ast); }

concrete productions top::ListOfCommands_c
|
  { top.ast = emptyListOfCommands(); }
| a::AnyCommand_c rest::ListOfCommands_c
  { top.ast = addListOfCommands(a.ast, rest.ast); }




--AnyCommand to handle common parsing errors gracefully
closed nonterminal PureCommand_c with ast<AnyCommand>;
closed nonterminal PureTopCommand_c with ast<AnyCommand>;
closed nonterminal CommonCommand_c with ast<NoOpCommand>;
closed nonterminal AnyCommand_c
   layout {Whitespace_t, BlockComment_t, OneLineComment_t}
   with ast<AnyCommand>;
closed nonterminal TheoremStmts_c with ast<Either<String ExtThms>>;
closed nonterminal ExtBody_c with ast<Either<String ExtBody>>;
closed nonterminal ExtIndBodies_c with ast<ExtIndBody>;
closed nonterminal ExtIndBody_c with ast<ExtIndBody>;
closed nonterminal QnameList_c with ast<[QName]>;

concrete productions top::AnyCommand_c
| c::PureTopCommand_c
  { top.ast = c.ast; }
| c::PureCommand_c
  { top.ast = c.ast; }
| c::CommonCommand_c
  { top.ast = anyNoOpCommand(c.ast); }

concrete productions top::PureCommand_c
| h::HHint_c 'induction' 'on' nl::NumList_c '.'
  { top.ast = anyProofCommand(inductionTactic(h.ast, nl.ast)); }
| h::HHint_c 'coinduction' '.'
  { top.ast = anyProofCommand(coinductionTactic(h.ast)); }
| h::HHint_c 'apply' md::MaybeDepth_c c::Clearable_c 'to'
  a::ApplyArgs_c '.'
  { top.ast = anyProofCommand(applyTactic(h.ast, md.ast, c.ast,
                                          a.ast, endWiths())); }
| h::HHint_c 'apply' md::MaybeDepth_c c::Clearable_c 'to'
  a::ApplyArgs_c 'with' w::Withs_c '.'
  { top.ast = anyProofCommand(applyTactic(h.ast, md.ast, c.ast,
                                          a.ast, w.ast)); }
| h::HHint_c 'apply' md::MaybeDepth_c c::Clearable_c 'with'
  w::Withs_c '.'
  { top.ast = anyProofCommand(applyTactic(h.ast, md.ast, c.ast,
                                          endApplyArgs(), w.ast)); }
| h::HHint_c 'apply' md::MaybeDepth_c c::Clearable_c '.'
  { top.ast = anyProofCommand(applyTactic(h.ast, md.ast, c.ast,
                                 endApplyArgs(), endWiths())); }
| 'backchain' md::MaybeDepth_c c::Clearable_c '.'
  { top.ast = anyProofCommand(backchainTactic(md.ast, c.ast,
                                 endWiths())); }
| 'backchain' md::MaybeDepth_c c::Clearable_c 'with' w::Withs_c '.'
  { top.ast = anyProofCommand(backchainTactic(md.ast, c.ast, w.ast)); }
| h::HHint_c 'case' hy::Hyp_c '.'
  { top.ast = anyProofCommand(caseTactic(h.ast, hy.ast, false)); }
| h::HHint_c 'case' hy::Hyp_c '(' 'keep' ')' '.'
  { top.ast = anyProofCommand(caseTactic(h.ast, hy.ast, true)); }
| h::HHint_c 'assert' m::Metaterm_c '.'
  { top.ast =
        case m.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(ma) ->
          anyProofCommand(assertTactic(h.ast, nothing(), ma))
        end; }
| 'exists' ew::EWitnesses_c '.'
  { top.ast = anyProofCommand(existsTactic(ew.ast)); }
| 'witness' ew::EWitnesses_c '.'
  { top.ast = anyProofCommand(witnessTactic(ew.ast)); }
| 'search' '.'
  { top.ast = anyProofCommand(searchTactic()); }
| 'search' n::Number_t '.'
  { top.ast = anyProofCommand(
                 searchDepthTactic(toInteger(n.lexeme))); }
| 'search' 'with' sw::SearchWitness_c '.'
  { top.ast = anyProofCommand(searchWitnessTactic(sw.ast)); }
| 'async' '.'
  { top.ast = anyProofCommand(asyncTactic()); }
| 'split' '.'
  { top.ast = anyProofCommand(splitTactic()); }
| 'split*' '.'
  { top.ast = anyProofCommand(splitStarTactic()); }
| 'left' '.'
  { top.ast = anyProofCommand(leftTactic()); }
| 'right' '.'
  { top.ast = anyProofCommand(rightTactic()); }
| 'intros' '.'
  { top.ast = anyProofCommand(introsTactic([])); }
| 'intros' names::HypList_c '.'
  { top.ast = anyProofCommand(introsTactic(names.ast)); }
| 'skip' '.'
  { top.ast = anyProofCommand(skipTactic()); }
| 'abort' '.'
  { top.ast = anyProofCommand(abortCommand()); }
| 'undo' '.'
  { top.ast = anyProofCommand(undoCommand()); }
| 'unfold' cs::ClauseSel_c ss::SolSel_c '.'
  { top.ast = anyProofCommand(cs.ast(ss.ast)); }
| 'clear' hl::HypList_c '.'
  { top.ast = anyProofCommand(clearCommand(hl.ast, false)); }
| 'clear' '->' hl::HypList_c '.'
  { top.ast = anyProofCommand(clearCommand(hl.ast, true)); }
| 'abbrev' hl::HypList_c q::QString_t '.'
  { top.ast = anyProofCommand(
                 abbrevCommand(hl.ast, removeQuotes(q.lexeme))); }
| 'unabbrev' hl::HypList_c '.'
  { top.ast = anyProofCommand(unabbrevCommand(hl.ast)); }
| 'rename' original::Id_t 'to' newname::Id_t '.'
  { top.ast = anyProofCommand(renameTactic(original.lexeme,
                                           newname.lexeme)); }
| 'permute' p::Perm_c '.'
  { top.ast = anyProofCommand(permuteTactic(p.ast, nothing())); }
| 'permute' p::Perm_c h::Hyp_c '.'
  { top.ast = anyProofCommand(permuteTactic(p.ast, just(h.ast))); }
| 'compute' hyp::Id_t '.'
  { top.ast = anyProofCommand(computeTactic(hyp.lexeme)); }

concrete productions top::PureTopCommand_c
| 'Theorem' name::Id_t params::TheoremTyparams_c ':' body::Metaterm_c '.'
  { top.ast =
        case body.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(ba) ->
          anyTopCommand(
             theoremDeclaration(toQName(name.lexeme), params.ast, ba))
        end; }
| 'Theorem' name::Qname_t params::TheoremTyparams_c ':' body::Metaterm_c '.'
  { top.ast =
        case body.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(ba) ->
          anyTopCommand(
             theoremDeclaration(toQName(name.lexeme), params.ast, ba))
        end; }
| 'Define' x::IdTys_c 'by' o::OptSemi_t d::Defs_c '.'
  { top.ast =
        case d.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(da) -> anyTopCommand(definitionDeclaration(x.ast, da))
        end; }
| 'CoDefine' x::IdTys_c 'by' o::OptSemi_t d::Defs_c '.'
  { top.ast =
        case d.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(da) ->
          anyTopCommand(codefinitionDeclaration(x.ast, da))
        end; }
| 'Query' m::Metaterm_c '.'
  { top.ast =
        case m.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(ma) -> anyTopCommand(queryCommand(ma))
        end; }
| 'Kind' il::QnameList_c k::Knd_c '.'
  { top.ast = anyTopCommand(kindDeclaration(il.ast, k.ast)); }
| 'Type' il::QnameList_c t::Ty_c '.'
  { top.ast = anyTopCommand(typeDeclaration(il.ast, t.ast)); }
| 'Close' al::ATyList_c '.'
  { top.ast = anyTopCommand(closeCommand(al.ast)); }
| 'Split' name::Id_t '.'
  { top.ast = anyTopCommand(splitTheorem(toQName(name.lexeme), [])); }
| 'Split' name::Id_t 'as' il::QnameList_c '.'
  { top.ast = anyTopCommand(splitTheorem(toQName(name.lexeme), il.ast)); }
| 'Split' name::Qname_t '.'
  { top.ast = anyTopCommand(splitTheorem(toQName(name.lexeme), [])); }
| 'Split' name::Qname_t 'as' il::QnameList_c '.'
  { top.ast = anyTopCommand(splitTheorem(toQName(name.lexeme), il.ast)); }
--For reading the standard library, written in Abella
| 'Import' s::QuotedString_t '.'
  { top.ast =
        anyTopCommand(
           importCommand(
              unescapeString(
                 substring(1, length(s.lexeme)-1, s.lexeme)))); }
--New for extensibility
| 'Extensible_Theorem' thms::TheoremStmts_c '.'
  { top.ast =
        case thms.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(lst) ->
          anyTopCommand(extensibleTheoremDeclaration(lst, endExtThms()))
        end; }
| 'Extensible_Theorem' thms::TheoremStmts_c 'also' alsos::TheoremStmts_c '.'
  { top.ast =
        case thms.ast, alsos.ast of
        | left(msg), _ -> anyParseFailure(msg)
        | _, left(msg) -> anyParseFailure(msg)
        | right(lstT), right(lstA) ->
          anyTopCommand(extensibleTheoremDeclaration(lstT, lstA))
        end; }
| 'Prove' thms::QnameList_c '.'
  { top.ast = anyTopCommand(proveObligations(thms.ast)); }
| 'Extensible_Theorem' newthms::TheoremStmts_c 'with' oldthms::QnameList_c '.'
  { top.ast =
        case newthms.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(lst) -> todoError("Adding extensible theorems to groups not done yet")
        end; }
| 'Translation_Constraint' name::Id_t ':'
  'forall' binds::BindingList_c ',' body::ExtBody_c '.'
  { top.ast =
        case body.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(b) ->
          anyTopCommand(
                 translationConstraint(toQName(name.lexeme),
                                       binds.ast, b))
        end; }
| 'Translation_Constraint' name::Qname_t ':'
  'forall' binds::BindingList_c ',' body::ExtBody_c '.'
  { top.ast =
        case body.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(b) ->
          anyTopCommand(
                 translationConstraint(toQName(name.lexeme),
                                       binds.ast, b))
        end; }
| 'Prove_Constraint' tc::Qname_t '.'
  { top.ast = anyTopCommand(proveConstraint(toQName(tc.lexeme))); }
-----
| 'Ext_Ind' e::ExtIndBodies_c '.'
  { top.ast = anyTopCommand(extIndDeclaration(e.ast)); }
| 'Prove_Ext_Ind' rels::QnameList_c '.'
  { top.ast = anyTopCommand(proveExtInd(rels.ast)); }
| 'Prove_Ext_Ind' e::ExtIndBodies_c 'with' oldRels::QnameList_c '.'
  { top.ast = todoError("Adding new relations to ExtInd groups not done yet"); }


nonterminal VarList_c with ast<[String]>;

concrete productions top::VarList_c
| name::Id_t
  { top.ast = [name.lexeme]; }
| name::Id_t rest::VarList_c
  { top.ast = name.lexeme::rest.ast; }


concrete productions top::TheoremStmts_c
| name::Id_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c
  'on' label::Id_t
  { top.ast =
        case body.ast of
        | left(msg) -> left(msg)
        | right(b) ->
          right(addExtThms(toQName(name.lexeme), binds.ast, b,
                           label.lexeme, nothing(), endExtThms()))
        end; }
| name::Id_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c
  'on' label::Id_t 'as' nameIH::Id_t
  { top.ast =
        case body.ast of
        | left(msg) -> left(msg)
        | right(b) ->
          right(addExtThms(toQName(name.lexeme), binds.ast, b,
                   label.lexeme, just(nameIH.lexeme), endExtThms()))
        end; }
| name::Id_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c
  'on' label::Id_t ',' rest::TheoremStmts_c
  { top.ast =
        case body.ast, rest.ast of
        | left(msg1), left(msg2) -> left(msg1 ++ "\n" ++ msg2)
        | left(msg), _ -> left(msg)
        | _, left(msg) -> left(msg)
        | right(b), right(rst) ->
          right(addExtThms(toQName(name.lexeme), binds.ast, b,
                           label.lexeme, nothing(), rst))
        end; }
| name::Id_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c
  'on' label::Id_t 'as' nameIH::Id_t ',' rest::TheoremStmts_c
  { top.ast =
        case body.ast, rest.ast of
        | left(msg1), left(msg2) -> left(msg1 ++ "\n" ++ msg2)
        | left(msg), _ -> left(msg)
        | _, left(msg) -> left(msg)
        | right(b), right(rst) ->
          right(addExtThms(toQName(name.lexeme), binds.ast, b,
                           label.lexeme, just(nameIH.lexeme), rst))
        end; }
| name::Qname_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c
  'on' label::Id_t
  { top.ast =
        case body.ast of
        | left(msg) -> left(msg)
        | right(b) ->
          right(addExtThms(toQName(name.lexeme), binds.ast, b,
                           label.lexeme, nothing(), endExtThms()))
        end; }
| name::Qname_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c
  'on' label::Id_t 'as' nameIH::Id_t
  { top.ast =
        case body.ast of
        | left(msg) -> left(msg)
        | right(b) ->
          right(addExtThms(toQName(name.lexeme), binds.ast, b,
                   label.lexeme, just(nameIH.lexeme), endExtThms()))
        end; }
| name::Qname_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c
  'on' label::Id_t ',' rest::TheoremStmts_c
  { top.ast =
        case body.ast, rest.ast of
        | left(msg1), left(msg2) -> left(msg1 ++ "\n" ++ msg2)
        | left(msg), _ -> left(msg)
        | _, left(msg) -> left(msg)
        | right(b), right(rst) ->
          right(addExtThms(toQName(name.lexeme), binds.ast, b,
                           label.lexeme, nothing(), rst))
        end; }
| name::Qname_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c
  'on' label::Id_t 'as' nameIH::Id_t ',' rest::TheoremStmts_c
  { top.ast =
        case body.ast, rest.ast of
        | left(msg1), left(msg2) -> left(msg1 ++ "\n" ++ msg2)
        | left(msg), _ -> left(msg)
        | _, left(msg) -> left(msg)
        | right(b), right(rst) ->
          right(addExtThms(toQName(name.lexeme), binds.ast, b,
                           label.lexeme, just(nameIH.lexeme), rst))
        end; }
  --These are to get errors which are more helpful, because I forget
  --   the labels a lot and can't figure out why it doesn't work.
  --I'm assuming, at least for now, that we don't need these with 'as'
  --   clauses.
| name::Id_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c
  { top.ast =
        left("Must include relation on which to do induction for theorem " ++
             toString(name.lexeme)); }
| name::Id_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c ','
  rest::TheoremStmts_c
  { top.ast =
        left("Must include relation on which to do induction for theorem " ++
              toString(name.lexeme) ++ "\n" ++
             case rest.ast of
             | left(msg) -> msg
             | right(_) -> ""
             end); }
| name::Qname_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c
  { top.ast =
        left("Must include relation on which to do induction for theorem " ++
             toString(name.lexeme)); }
| name::Qname_t ':' 'forall' binds::BindingList_c ',' body::ExtBody_c ','
  rest::TheoremStmts_c
  { top.ast =
        left("Must include relation on which to do induction for theorem " ++
              toString(name.lexeme) ++ "\n" ++
             case rest.ast of
             | left(msg) -> msg
             | right(_) -> ""
             end); }


concrete productions top::ExtBody_c
| conc::Metaterm_c
  { top.ast = bind(conc.ast, \ c::Metaterm -> right(endExtBody(c))); }
| label::Id_t ':' m::Metaterm_c '->' rest::ExtBody_c
  { top.ast =
        bind(m.ast,
             \ ma::Metaterm ->
               bind(rest.ast,
                    \ ra::ExtBody ->
                      right(addLabelExtBody(toString(label.lexeme),
                                            ma, ra)))); }
{-This is causing an ambiguity for parsing with Metaterm_c
| m::Metaterm_c '->' rest::ExtBody_c
  { top.ast =
        bind(m.ast,
             \ ma::Metaterm ->
               bind(rest.ast,
                    \ ra::ExtBody ->
                      right(addBasicExtBody(ma, ra)))); }-}


concrete productions top::ExtIndBodies_c
| e::ExtIndBody_c
  { top.ast = e.ast; }
| e::ExtIndBody_c ',' rest::ExtIndBodies_c
  { top.ast = branchExtIndBody(e.ast, rest.ast); }


concrete productions top::ExtIndBody_c
| rel::Id_t args::VarList_c 'with'
  '|{' ty::Id_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           nothingBindings(), emptyTermList(), toQName(ty.lexeme),
           o.lexeme, t.lexeme); }
| rel::Qname_t args::VarList_c 'with'
  '|{' ty::Id_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           nothingBindings(), emptyTermList(), toQName(ty.lexeme),
           o.lexeme, t.lexeme); }
| rel::Id_t args::VarList_c 'with'
  '|{' ty::Qname_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           nothingBindings(), emptyTermList(), toQName(ty.lexeme),
           o.lexeme, t.lexeme); }
| rel::Qname_t args::VarList_c 'with'
  '|{' ty::Qname_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           nothingBindings(), emptyTermList(), toQName(ty.lexeme),
           o.lexeme, t.lexeme); }
| rel::Id_t args::VarList_c 'with'
  targs::ExpList_c '|{' ty::Id_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           nothingBindings(), targs.ast,
           toQName(ty.lexeme), o.lexeme, t.lexeme); }
| rel::Qname_t args::VarList_c 'with'
  targs::ExpList_c '|{' ty::Id_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           nothingBindings(), targs.ast,
           toQName(ty.lexeme), o.lexeme, t.lexeme); }
| rel::Id_t args::VarList_c 'with'
  targs::ExpList_c '|{' ty::Qname_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           nothingBindings(), targs.ast,
           toQName(ty.lexeme), o.lexeme, t.lexeme); }
| rel::Qname_t args::VarList_c 'with'
  targs::ExpList_c '|{' ty::Qname_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           nothingBindings(), targs.ast,
           toQName(ty.lexeme), o.lexeme, t.lexeme); }
--
| rel::Id_t args::VarList_c 'with'
  'forall' b::BindingList_c ','
  '|{' ty::Id_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           justBindings(b.ast), emptyTermList(), toQName(ty.lexeme),
           o.lexeme, t.lexeme); }
| rel::Qname_t args::VarList_c 'with'
  'forall' b::BindingList_c ','
  '|{' ty::Id_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           justBindings(b.ast), emptyTermList(), toQName(ty.lexeme),
           o.lexeme, t.lexeme); }
| rel::Id_t args::VarList_c 'with'
  'forall' b::BindingList_c ','
  '|{' ty::Qname_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           justBindings(b.ast), emptyTermList(), toQName(ty.lexeme),
           o.lexeme, t.lexeme); }
| rel::Qname_t args::VarList_c 'with'
  'forall' b::BindingList_c ','
  ',' '|{' ty::Qname_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme),  args.ast,
           justBindings(b.ast), emptyTermList(), toQName(ty.lexeme),
           o.lexeme, t.lexeme); }
| rel::Id_t args::VarList_c 'with'
  'forall' b::BindingList_c ','
  targs::ExpList_c '|{' ty::Id_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           justBindings(b.ast), targs.ast,
           toQName(ty.lexeme), o.lexeme, t.lexeme); }
| rel::Qname_t args::VarList_c 'with'
  'forall' b::BindingList_c ','
  targs::ExpList_c '|{' ty::Id_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           justBindings(b.ast), targs.ast,
           toQName(ty.lexeme), o.lexeme, t.lexeme); }
| rel::Id_t args::VarList_c 'with'
  'forall' b::BindingList_c ','
  targs::ExpList_c '|{' ty::Qname_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           justBindings(b.ast), targs.ast,
           toQName(ty.lexeme), o.lexeme, t.lexeme); }
| rel::Qname_t args::VarList_c 'with'
  'forall' b::BindingList_c ','
  targs::ExpList_c '|{' ty::Qname_t '}-' o::Id_t '~~>' t::Id_t
  { top.ast =
        oneExtIndBody(toQName(rel.lexeme), args.ast,
           justBindings(b.ast), targs.ast,
           toQName(ty.lexeme), o.lexeme, t.lexeme); }


concrete productions top::QnameList_c
| i::Id_t
  { top.ast = [toQName(i.lexeme)]; }
| q::Qname_t
  { top.ast = [toQName(q.lexeme)]; }
| i::Id_t ',' rest::QnameList_c
  { top.ast = toQName(i.lexeme)::rest.ast; }
| q::Qname_t ',' rest::QnameList_c
  { top.ast = toQName(q.lexeme)::rest.ast; }


concrete productions top::CommonCommand_c
| 'Set' opt::Id_t value::Id_t '.'
  { top.ast = setCommand(opt.lexeme, value.lexeme); }
| 'Set' opt::Id_t value::Number_t '.'
  { top.ast = setCommand(opt.lexeme, value.lexeme); }
| 'Set' opt::Id_t value::QString_t '.'
  { top.ast = setCommand(opt.lexeme, value.lexeme); }
| 'Set' opt::Id_t 'on' '.'
  { top.ast = setCommand(opt.lexeme, "on"); }
| 'Show' name::Id_t '.'
  { top.ast = showCommand(toQName(name.lexeme)); }
| 'Show' name::Qname_t '.'
  { top.ast = showCommand(toQName(name.lexeme)); }
| 'Quit' '.'
  { top.ast = quitCommand(); }
| b::Backs_c
  { top.ast = backCommand(b.ast); }
| '#reset' '.'
  { top.ast = resetCommand(); }
| 'Show $$current.'
  { top.ast = showCurrentCommand(); }


closed nonterminal Backs_c with ast<Integer>;

concrete productions top::Backs_c
| b::Backs_t
  { top.ast = countOctothorpeOccurrences(b.lexeme); }

function countOctothorpeOccurrences
Integer ::= str::String
{
  local index::Integer = indexOf("#", str);
  local rest::String = substring(index + 1, length(str), str);
  return
     if index > -1
     then 1 + countOctothorpeOccurrences(rest)
     else 0;
}





concrete productions top::Exp_c
--This doesn't work with fromAbella, so we put it here instead
| i::Number_t
  { top.ast = intTerm(toInteger(i.lexeme)); }





closed nonterminal Knd_c with ast<Kind>;
closed nonterminal UTy_c with ast<Type>;
closed nonterminal UTyList_c with ast<TypeList>;
closed nonterminal ATyList_c with ast<TypeList>;


concrete productions top::Knd_c
| 'type'
  { top.ast = typeKind(); }
| 'type' '->' k::Knd_c
  { top.ast = arrowKind(k.ast); }


concrete productions top::UTy_c
| t::Ty_c
  { top.ast = t.ast; }


concrete productions top::UTyList_c
| u::UTy_c
  { top.ast = addTypeList(u.ast, emptyTypeList()); }
| u::UTy_c ',' rest::UTyList_c
  { top.ast = addTypeList(u.ast, rest.ast); }


concrete productions top::ATyList_c
| a::ATy_c
  { top.ast = addTypeList(a.ast, emptyTypeList()); }
| a::ATy_c ',' rest::ATyList_c
  { top.ast = addTypeList(a.ast, rest.ast); }





closed nonterminal Defs_c with ast<Either<String Defs>>;
closed nonterminal Def_c with ast<Either<String Def>>;


concrete productions top::Defs_c
| d::Def_c ';' rest::Defs_c
  { top.ast =
        bind(d.ast,
             \ da::Def ->
               bind(rest.ast,
                    \ ra::Defs -> right(consDefs(da, ra)))); }
| d::Def_c
  { top.ast = bind(d.ast, \ da::Def -> right(singleDefs(da))); }


concrete productions top::Def_c
| rel::Id_t args::ExpList_c
  { top.ast = right(factDef(toQName(rel.lexeme), args.ast)); }
| rel::Qname_t args::ExpList_c
  { top.ast = right(factDef(toQName(rel.lexeme), args.ast)); }
| rel::Id_t args::ExpList_c ':=' b::Metaterm_c
  { top.ast =
        bind(b.ast,
           \ ba::Metaterm ->
             right(ruleDef(toQName(rel.lexeme), args.ast, ba))); }
| rel::Qname_t args::ExpList_c ':=' b::Metaterm_c
  { top.ast =
        bind(b.ast,
           \ ba::Metaterm ->
             right(ruleDef(toQName(rel.lexeme), args.ast, ba))); }





closed nonterminal Perm_c with ast<[String]>;
closed nonterminal PermIds_c with ast<[String]>;


concrete productions top::Perm_c
| '(' p::PermIds_c ')'
  { top.ast = p.ast; }


concrete productions top::PermIds_c
| i::Id_t rest::PermIds_c
  { top.ast = i.lexeme::rest.ast; }
| i::Id_t
  { top.ast = [i.lexeme]; }





closed nonterminal SearchWitness_c with ast<SearchWitness>;
closed nonterminal SearchWitnessList_c with ast<[SearchWitness]>;


concrete productions top::SearchWitness_c
| 'true'
  { top.ast = trueSearchWitness(); }
| 'apply' i::Id_t
  { top.ast = applySearchWitness(i.lexeme); }
| 'left' sw::SearchWitness_c
  { top.ast = leftSearchWitness(sw.ast); }
| 'right' sw::SearchWitness_c
  { top.ast = rightSearchWitness(sw.ast); }
| 'split' '(' sw1::SearchWitness_c ',' sw2::SearchWitness_c ')'
  { top.ast = splitSearchWitness(sw1.ast, sw2.ast); }
| 'intros' '[' il::IdList_c ']' sw::SearchWitness_c
  { top.ast = introsSearchWitness(il.ast, sw.ast); }
| 'forall' '[' il::IdList_c ']' sw::SearchWitness_c
  { top.ast = forallSearchWitness(il.ast, sw.ast); }
| 'exists' '[' eb::ExistsBinds_c ']' sw::SearchWitness_c
  { top.ast = existsSearchWitness(eb.ast, sw.ast); }
| 'unfold' '(' i::Id_t ',' n::Number_t swl::SearchWitnessList_c ')'
  { top.ast = unfoldSearchWitness(i.lexeme, toInteger(n.lexeme), swl.ast); }
| '*'
  { top.ast = starSearchWitness(); }
| '='
  { top.ast = eqSearchWitness(); }
| '(' sw::SearchWitness_c ')'
  { top.ast = sw.ast; }


concrete productions top::SearchWitnessList_c
|
  { top.ast = []; }
| ',' sw::SearchWitness_c swl::SearchWitnessList_c
  { top.ast = sw.ast::swl.ast; }





closed nonterminal EWitnesses_c with ast<EWitnesses>;
closed nonterminal EWitness_c with ast<EWitness>;


concrete productions top::EWitnesses_c
| ew::EWitness_c ',' rest::EWitnesses_c
  { top.ast = addEWitnesses(ew.ast, rest.ast); }
| ew::EWitness_c
  { top.ast = oneEWitnesses(ew.ast); }


concrete productions top::EWitness_c
| name::Id_t '=' t::Term_c
  { top.ast = nameEWitness(name.lexeme, t.ast); }
| t::Term_c
  { top.ast = termEWitness(t.ast); }





closed nonterminal ApplyArgs_c with ast<ApplyArgs>;
closed nonterminal ApplyArg_c with ast<ApplyArg>;


concrete productions top::ApplyArgs_c
| a::ApplyArg_c rest::ApplyArgs_c
  { top.ast = addApplyArgs(a.ast, rest.ast); }
| a::ApplyArg_c
  { top.ast = addApplyArgs(a.ast, endApplyArgs()); }


concrete productions top::ApplyArg_c
| h::Hyp_c m::MaybeInst_c
  { top.ast = hypApplyArg(h.ast, m.ast); }
| '*' i::Id_t m::MaybeInst_c
  { top.ast = starApplyArg(i.lexeme, m.ast); }





closed nonterminal ExistsBinds_c with ast<Withs>;


concrete productions top::ExistsBinds_c
|
  { top.ast = endWiths(); }
| w::Withs_c
  { top.ast = w.ast; }





closed nonterminal IdList_c with ast<[String]>;
closed nonterminal IdTy_c with ast<(QName, Type)>;
closed nonterminal IdTys_c with ast<[(QName, Type)]>;
closed nonterminal HHint_c with ast<HHint>;
closed nonterminal Clearable_c with ast<Clearable>;
closed nonterminal Withs_c with ast<Withs>;


concrete productions top::IdList_c
| l::Id_t
  { top.ast = [l.lexeme]; }
| l::Id_t ',' rest::IdList_c
  { top.ast = l.lexeme::rest.ast; }


concrete productions top::IdTy_c
| i::Id_t ':' t::Ty_c
  { top.ast = (toQName(i.lexeme), t.ast); }
| i::Qname_t ':' t::Ty_c
  { top.ast = (toQName(i.lexeme), t.ast); }


concrete productions top::IdTys_c
| i::IdTy_c ',' rest::IdTys_c
  { top.ast = i.ast::rest.ast;}
| i::IdTy_c
  { top.ast = [i.ast]; }


concrete productions top::HHint_c
| name::Id_t ':'
  { top.ast = nameHint(name.lexeme); }
|
  { top.ast = noHint(); }


concrete productions top::Clearable_c
| h::Hyp_c m::MaybeInst_c
  { top.ast = clearable(false, toQName(h.ast), m.ast); }
| '*' h::Hyp_c m::MaybeInst_c
  { top.ast = clearable(true, toQName(h.ast), m.ast); }
| name::Qname_t m::MaybeInst_c
  { top.ast = clearable(false, toQName(name.lexeme), m.ast); }
| '*' name::Qname_t m::MaybeInst_c
  { top.ast = clearable(true, toQName(name.lexeme), m.ast); }


concrete productions top::Withs_c
| i::Id_t '=' t::Term_c ',' rest::Withs_c
  { top.ast = addWiths(i.lexeme, t.ast, rest.ast); }
| i::Id_t '=' t::Term_c
  { top.ast = addWiths(i.lexeme, t.ast, endWiths()); }





closed nonterminal Hyp_c with ast<String>;
closed nonterminal HypList_c with ast<[String]>;


concrete productions top::Hyp_c
| name::Id_t
  { top.ast = name.lexeme; }
| '_'
  { top.ast = "_"; }


concrete productions top::HypList_c
| h::Hyp_c l::HypList_c
  { top.ast = h.ast::l.ast; }
| h::Hyp_c
  { top.ast = [h.ast]; }





closed nonterminal MaybeInst_c with ast<TypeList>;
closed nonterminal MaybeDepth_c with ast<Maybe<Integer>>;


concrete productions top::MaybeInst_c
|
  { top.ast = emptyTypeList(); }
| '[' u::UTyList_c ']'
  { top.ast = u.ast; }


concrete productions top::MaybeDepth_c
| d::Depth_c
  { top.ast = just(d.ast); }
|
  { top.ast = nothing(); }

--this is solely a helper to fix a parsing error with MaybeDepth
closed nonterminal Depth_c with ast<Integer>;
concrete productions top::Depth_c
| n::Number_t
  { top.ast = toInteger(n.lexeme); }





closed nonterminal NumList_c with ast<[Integer]>;


concrete productions top::NumList_c
| n::Number_t rest::NumList_c
  { top.ast = toInteger(n.lexeme)::rest.ast; }
| n::Number_t
  { top.ast = [toInteger(n.lexeme)]; }





closed nonterminal ClauseSel_c with ast<(ProofCommand ::= Boolean)>;
closed nonterminal SolSel_c with ast<Boolean>;


concrete productions top::ClauseSel_c
|
  { top.ast = unfoldTactic(_); }
| n::Number_t
  { top.ast = unfoldStepsTactic(toInteger(n.lexeme), _); }
| si::Id_t
  { top.ast = unfoldIdentifierTactic(toQName(si.lexeme), _); }


concrete productions top::SolSel_c
|
  { top.ast = false; }
| '(' 'all' ')'
  { top.ast = true; }





closed nonterminal TheoremTyparams_c with ast<[String]>;


concrete productions top::TheoremTyparams_c
|
  { top.ast = []; }
| '[' il::IdList_c ']'
  { top.ast = il.ast; }





function removeQuotes
String ::= qstring::String
{
  return substring(1, length(qstring) - 1, qstring);
}

