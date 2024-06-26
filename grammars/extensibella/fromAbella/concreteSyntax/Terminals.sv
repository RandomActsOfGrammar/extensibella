grammar extensibella:fromAbella:concreteSyntax;


imports extensibella:fromAbella:abstractSyntax;
imports extensibella:common:abstractSyntax;
imports extensibella:common:concreteSyntax;


lexer class DISPLAY   dominates Id_t;
lexer class ERROR;


terminal Subgoal_t      'Subgoal'            lexer classes {DISPLAY};
terminal Is_t           'is'                 lexer classes {DISPLAY};
terminal Variables_t    'Variables'          lexer classes {DISPLAY};
terminal GoalLine_t     /===+/               lexer classes {DISPLAY};
terminal ProofDone_t    'Proof completed'    lexer classes {DISPLAY};
terminal ProofDoneDot_t 'Proof completed.'   lexer classes {DISPLAY};
terminal UsingSkip_t    '*** USING skip ***' lexer classes {DISPLAY};
terminal ProofQuit_t    'Proof ABORTED.'     lexer classes {DISPLAY};
terminal ImportFrom_t   'Importing from'     lexer classes {DISPLAY};
terminal OtherSubs_t    'other subgoals.'    lexer classes {DISPLAY};
terminal OtherSub_t     'other subgoal.'     lexer classes {DISPLAY};
terminal Theorem_t      'Theorem'            lexer classes {DISPLAY};

terminal SyntaxError_t       'Syntax error.'                                                        lexer classes {DISPLAY, ERROR};
terminal Error_t             'Error:'                                                               lexer classes {DISPLAY, ERROR};
terminal SearchFail_t        'Search failed'                                                        lexer classes {ERROR};
terminal VarUndetermined_t   'Types of variables are not fully determined'                          lexer classes {ERROR};
terminal UnknownHyp_t        'Could not find hypothesis or lemma'                                   lexer classes {ERROR};
terminal UnknownConst_t      'Unknown constant:'                                                    lexer classes {ERROR};
terminal TypingErr_t         'Typing error.'                                                        lexer classes {ERROR};
terminal ExprHasType_t       'Expression has type'                                                  lexer classes {ERROR};
terminal ButIsUsed_t         'but is used here with type'                                           lexer classes {ERROR};
terminal ExprTooManyArgs_t   'Expression is applied to too many arguments'                          lexer classes {ERROR};
terminal ImportUnknownTy_t   'Imported file makes reference to unknown types:'                      lexer classes {ERROR};
terminal IgnoreImport_t      'Ignoring import:'                                                     lexer classes {DISPLAY, ERROR};
terminal AlreadyImported_t   'has already been imported.'                                           lexer classes {DISPLAY, ERROR};
terminal InvalidFormula_t    'Invalid formula:'                                                     lexer classes {ERROR};
terminal NoSizeRestrict_t    'Cannot use size restrictions (*, @, #, or +)'                         lexer classes {ERROR};
terminal Warning_t           'Warning:'                                                             lexer classes {DISPLAY, ERROR};
terminal NotStrat_t          'Definition might not be stratified'                                   lexer classes {ERROR};
terminal OccursLeft_t        'occurs to the left of ->)'                                            lexer classes {ERROR};
terminal DefeatStrat_t       'Definition can be used to defeat stratification'                      lexer classes {ERROR};
terminal HOArgument_t        '(higher-order argument'                                               lexer classes {ERROR};
terminal UnboundedTyVars_t   'Some type variables in the theorem is not bounded'                    lexer classes {ERROR};
terminal PredOrConst_t       'Predicate or constant'                                                lexer classes {ERROR};
terminal AlreadyExists_t     'already exists'                                                       lexer classes {ERROR};
terminal InvalidDefName_t    'Invalid defined predicate name'                                       lexer classes {ERROR};
terminal NoCapPred_t         'Defined predicates may not begin with a capital letter.'              lexer classes {ERROR};
terminal NoCapConst_t        'Constants may not begin with a capital letter:'                       lexer classes {ERROR};
terminal StrayClause_t       'Found stray clause for'                                               lexer classes {ERROR};
terminal InvalidHead_t       'Invalid head in definition:'                                          lexer classes {ERROR};
terminal NonatomicHead_t     'Definitional clause head not atomic:'                                 lexer classes {ERROR};
terminal CaseUndefined_t     'Cannot perform case-analysis on undefined atom'                       lexer classes {ERROR};
terminal CaseThisKind_t      'Cannot perform case-analysis on this kind of formula'                 lexer classes {ERROR};
terminal UnknownHypVar_t     'Unknown hypothesis or variable'                                       lexer classes {ERROR};
terminal OverrideName_t      'overriding existing lemma named'                                      lexer classes {ERROR};
terminal UnknownTheorem_t    'Could not find theorem named'                                         lexer classes {ERROR};
terminal UnknownVar_t        'Unknown variable'                                                     lexer classes {ERROR};
terminal InductPredJudg_t    'Can only induct on predicates and judgments'                          lexer classes {ERROR};
terminal CannotInductOn_t    'Cannot induct on'                                                     lexer classes {ERROR};
terminal SinceNotDefined_t   'since it has not been defined'                                        lexer classes {ERROR};
terminal Expecting_t         'Expecting'                                                            lexer classes {DISPLAY, ERROR};
terminal InductionArgs_t     'induction arguments but got'                                          lexer classes {ERROR};
terminal NeedlessSplit_t     'Needless use of split'                                                lexer classes {ERROR};
terminal CannotSplit_t       'Cannot split this type of theorem'                                    lexer classes {ERROR};
terminal ExistingHyp_t       'already refers to an existing hypothesis'                             lexer classes {ERROR};
terminal ExistingLemma_t     'already refers to a lemma'                                            lexer classes {ERROR};
terminal ExistingVar_t       'already refers to an existing variable'                               lexer classes {ERROR};
terminal UnknownLabel_t      'Unknown variable or hypothesis label'                                 lexer classes {ERROR};
terminal CannotGoBack_t      'Cannot go that far back!'                                             lexer classes {ERROR};
terminal WhileMatch_t        'While matching argument #'                                            lexer classes {ERROR};
terminal UnifFailConst_t     'Unification failure (constant clash between'                          lexer classes {ERROR};
terminal UnifFail_t          'Unification failure'                                                  lexer classes {ERROR};
terminal AndErrText_t        'and'                                                                  lexer classes {ERROR};
terminal TyConstr_t          'Type constructor'                                                     lexer classes {ERROR};
terminal InconsKinds_t       'has inconsistent kind declarations'                                   lexer classes {ERROR};
terminal TyNoCaps_t          'Types may not begin with a capital letter:'                           lexer classes {ERROR};
terminal UnknownTyConstr_t   'Unknown type constructor:'                                            lexer classes {ERROR};
terminal Expects_t           'expects'                                                              lexer classes {ERROR};
terminal ArgsButHas_t        'arguments but has'                                                    lexer classes {ERROR};
terminal NoQuantProp_t       'Cannot quantify over type prop'                                       lexer classes {ERROR};
terminal Unknownkey_t        'Unknown key'                                                          lexer classes {ERROR};
terminal UnknownValue_t      'Unknown value'                                                        lexer classes {ERROR};
terminal ForKey_t            'for key'                                                              lexer classes {ERROR};
terminal ExpectInt_t         'expected non-negative integer'                                        lexer classes {ERROR};
terminal ExpectOnOff_t       /expected 'on' or 'off'/                                               lexer classes {ERROR};
terminal ExpectMany_t        /expected 'on', 'off', non-negative integer, or depth specification/   lexer classes {ERROR};
terminal NotEnoughArgs_t     'Not enough arguments to apply'                                        lexer classes {ERROR};
terminal TooManyArgs_t       'Too many arguments to apply'                                          lexer classes {ERROR};
terminal Expected_t          'Expected'                                                             lexer classes {ERROR};
terminal ButGot_t            'but got'                                                              lexer classes {ERROR};
terminal LogicVarTopLev_t    'Found logic variable at toplevel'                                     lexer classes {ERROR};
terminal StructureApp_t      'Structure of applied term must be a substructure of the following.'   lexer classes {ERROR};
terminal ApplyType_t         'forall A1 ... Ai, nabla z1 ... zj, H1 -> ... -> Hk -> C'              lexer classes {ERROR};
terminal IndRViolated_t      'Inductive restriction violated'                                       lexer classes {ERROR};
terminal LongFoundLogic1_t   'Found logic variable at toplevel.'                                    lexer classes {ERROR};
terminal LongFoundLogic2_t   'This usually means that the `search` tactic could not fully solve a goal.'
                                                                                                    lexer classes {ERROR};
terminal LongFoundLogic3_t   'Note: the `search` tactic may have been invoked implicitly by `apply`,'
                                                                                                    lexer classes {ERROR};
terminal LongFoundLogic4_t   '`backchain`, etc. with unknown arguments.'                            lexer classes {ERROR};
terminal NoMatching_t        'No matching clauses'                                                  lexer classes {ERROR};
terminal StrictSubterms_t    'Inductive restrictions must not occur in strict subterms'             lexer classes {ERROR};


terminal Type_t         'type'         lexer classes {LOGIC};


terminal Period_t      '.'       lexer classes {TOKEN};
terminal Semicolon_t   ';'       lexer classes {TOKEN};
terminal Backslash_t   '\'       lexer classes {TOKEN}, precedence=7;
terminal OptSemi_t     /;?/      lexer classes {TOKEN};


terminal QString_t  /"[^"]*"/;


--To fix parsing problems, since it is computer-generated output
terminal IdColon_t  /[-A-Za-z^=`'?$][-A-Za-z^=`'?$0-9_*@+#!~\/]* : /;
terminal IdComma_t  /[-A-Za-z^=`'?$][-A-Za-z^=`'?$0-9_*@+#!~\/]*,/;


--For hypotheses which have been abbreviated to non-whitespace names
--I'm having parsing problems if I try to handle whitespace names
--terminal Abbreviated_t  /[^"\r\n[-a-zA-Z0-9_?\/=+!@#$%^&*<>,.;:][^"\r\n]*/   submits to {Id_t, TOKEN, LOGIC};
terminal Abbreviated_t  /[^\ \t\n\r].*/  submits to
        {Id_t, TOKEN, LOGIC};


--For import errors
--Since we're reading computer-generated stuff, we can assume it is
--   actually a filepath and have such a general regex work
terminal FilePath_t  /[^\ \t\n\r]+/;
--For some error messages
terminal SingleQString_t  /'[^']*'/;
--To include nil for error messages
terminal ErrorId_t   /[-A-Za-z^=`'?$][-A-Za-z^=`'?$0-9_*@+#!~\/]*/;

