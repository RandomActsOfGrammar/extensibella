grammar extensibella:common:concreteSyntax;


lexer class LOGIC   dominates Id_t;
lexer class TOKEN   dominates Id_t;
lexer class TACTIC  dominates Id_t;
lexer class COMMENT;


terminal Exists_t       'exists'       lexer classes {TACTIC, LOGIC};
terminal False_t        'false'        lexer classes {LOGIC};
terminal Forall_t       'forall'       lexer classes {LOGIC};
terminal Nabla_t        'nabla'        lexer classes {LOGIC};
terminal True_t         'true'         lexer classes {LOGIC};


terminal Colon_t       ':'       lexer classes {TOKEN};
terminal Comma_t       ','       lexer classes {TOKEN}, precedence=3;
terminal LParen_t      '('       lexer classes {TOKEN};
terminal RParen_t      ')'       lexer classes {TOKEN};
terminal Eq_t          '='       lexer classes {TOKEN};
terminal RightArrow_t  '->'      lexer classes {TOKEN}, precedence=4, association=right;
terminal At_t          '@'       lexer classes {TOKEN};
terminal Octothorpe_t  '#'       lexer classes {TOKEN};
terminal Or_t          '\/'      lexer classes {TOKEN}, precedence=5, association=left;
terminal And_t         '/\'      lexer classes {TOKEN}, precedence=6, association=left;
terminal LBracket_t    '['       lexer classes {TOKEN};
terminal RBracket_t    ']'       lexer classes {TOKEN};
terminal Underscore_t  '_'       lexer classes {TOKEN};
terminal Cons_t        '::'      lexer classes {TOKEN}, precedence=11, association=right;
terminal Nil_t         'nil'     lexer classes {TOKEN};
--These two have Abella uses with no precedence or associativity
--   and language uses with precedence and associativity (arithmetic)
terminal Plus_t        '+'       lexer classes {TOKEN}, precedence=9, association=left;
terminal Star_t        '*'       lexer classes {TOKEN}, precedence=10, association=left;


--The string type needs to be treated specially as a built-in type
terminal StringTy_t   'string'   dominates {Id_t};


--Qname_t is a qualified name as in Silver/Sterling
terminal Qname_t  /([A-Za-z0-9_]+:)+[-A-Za-z^=`'?$][-A-Za-z^=`'?$0-9_*@+#!~\/]*/;
terminal Id_t  /[-A-Za-z^=`'?$][-A-Za-z^=`'?$0-9_*@+#!~\/]*/;
terminal Number_t  /[0-9]+/;


--These are the things which we are adding to Abella
terminal QuotedString_t  /"([^"]|(\\"))*"/;
terminal NegativeInteger_t  /-[0-9]+/ dominates Id_t;

terminal Minus_t      '-'    lexer classes {TOKEN}, precedence=9, association=left;
terminal Divide_t     '/'    lexer classes {TOKEN}, precedence=10, association=left;
--We use 'mod' instead of '%' because of Abella comments
--Alternatively, we could change comments for the interface, but I'd
--   like to leave the syntax the same as much as possible.
terminal Modulus_t    'mod'  lexer classes {TOKEN}, precedence=10, association=left;
terminal Less_t       '<'    lexer classes {TOKEN}, precedence=7, association=left;
terminal LessEq_t     '<='   lexer classes {TOKEN}, precedence=7, association=left;
terminal Greater_t    '>'    lexer classes {TOKEN}, precedence=7, association=left;
terminal GreaterEq_t  '>='   lexer classes {TOKEN}, precedence=7, association=left;
terminal Append_t     '++'   lexer classes {TOKEN}, precedence=8, association=left;
terminal BoolOr_t     '||'   lexer classes {TOKEN}, precedence=3, association=left;
terminal BoolAnd_t    '&&'   lexer classes {TOKEN}, precedence=4, association=left;
terminal BoolNot_t    '!'    lexer classes {TOKEN}, precedence=5;
terminal Tilde_t      '~'    lexer classes {TOKEN};

terminal ProjTurnstyleStart_t   '|{'    lexer classes {TOKEN};
terminal ProjTurnstyleEnd_t     '}-'    lexer classes {TOKEN};
terminal ProjArrow_t            '~~>'   lexer classes {TOKEN};


--For extension size and translation version of a relation
terminal ExtSize_t    'ES';
terminal ProjRel_t    'P';
terminal LCurly_t     '{'    lexer classes {TOKEN};
terminal RCurly_t     '}'    lexer classes {TOKEN};


ignore terminal Whitespace_t /[\ \t\n\r]+/;
-- Allows (one level of) nested comments.  Based on Silver comments.
ignore terminal BlockComment_t /\/\*(\/\*([^\*]|\*+[^\/\*])*\*+\/|[^\*]|\*+[^\/\*])*\*+\// lexer classes {COMMENT};
ignore terminal OneLineComment_t /(%.*)/ lexer classes {COMMENT};

