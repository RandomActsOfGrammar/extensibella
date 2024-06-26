grammar extensibella:fromAbella:abstractSyntax;

{-
  This file contains the terms which only show up in the translated
  output.  These are to make the output look nicer and hide the
  details of what we do in the encoding.

  Some of these are actually Metaterms, but we are translating a Term,
  so we can't handle it like that.
-}


aspect production projectionMetaterm
top::Metaterm ::= args::TermList ty::QName orig::Term proj::Term
{
  top.fromAbella = error("Should never be translating a projectionMetaterm");
}


{-
  INTEGER OPERATIONS
-}

aspect production plusMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.fromAbella = error("Should never be translating a plusMetaterm");
}


aspect production minusMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.fromAbella = error("Should never be translating a minusMetaterm");
}


aspect production multiplyMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.fromAbella = error("Should never be translating a multiplyMetaterm");
}


aspect production divideMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.fromAbella = error("Should never be translating a divideMetaterm");
}


aspect production modulusMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.fromAbella = error("Should never be translating a modulusMetaterm");
}


aspect production lessMetaterm
top::Metaterm ::= arg1::Term arg2::Term
{
  top.fromAbella = error("Should never be translating a lessMetaterm");
}


aspect production lessEqMetaterm
top::Metaterm ::= arg1::Term arg2::Term
{
  top.fromAbella = error("Should never be translating a lessEqMetaterm");
}


aspect production greaterMetaterm
top::Metaterm ::= arg1::Term arg2::Term
{
  top.fromAbella = error("Should never be translating a greaterMetaterm");
}


aspect production greaterEqMetaterm
top::Metaterm ::= arg1::Term arg2::Term
{
  top.fromAbella = error("Should never be translating a greaterEqMetaterm");
}


aspect production negateMetaterm
top::Metaterm ::= arg::Term result::Term
{
  top.fromAbella = error("Should never be translating a negateMetaterm");
}




{-
  APPEND
-}

aspect production appendMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term r::Restriction
{
  top.fromAbella = error("Should never be translating an appendMetaterm");
}




{-
  BOOLEAN OPERATIONS
-}

aspect production orBoolMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.fromAbella = error("Should never be translating an orBoolMetaterm");
}


aspect production andBoolMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.fromAbella = error("Should never be translating an andBoolMetaterm");
}


aspect production notBoolMetaterm
top::Metaterm ::= arg::Term result::Term
{
  top.fromAbella = error("Should never be translating a notBoolMetaterm");
}




{-
  EXTENSION SIZE AND PROJECTION VERSION OF RELATIONS
-}

aspect production extSizeMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.fromAbella = error("Should never be translating an extSizeMetaterm");
}


aspect production projRelMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.fromAbella = error("Should never be translating a projRelMetaterm");
}




{-
  BOOLEAN CONSTANTS
-}

aspect production trueTerm
top::Term ::=
{
  top.fromAbella = error("Should never be translatiing a trueTerm");
}


aspect production falseTerm
top::Term ::=
{
  top.fromAbella = error("Should never be translatiing a falseTerm");
}




{-
  UNKNOWN TERMS
-}

aspect production unknownITerm
top::Term ::= ty::QName
{
  top.fromAbella = error("Should never be translating unknownITerm");
}


aspect production unknownKTerm
top::Term ::= ty::QName
{
  top.fromAbella = error("Should never be translating unknownKTerm");
}




{-
  INTEGER CONSTANTS
-}

--We're going to use this for nats to facilitate translation,
--since the user should never have bare nats there anyway
aspect production intTerm
top::Term ::= i::Integer
{
  top.fromAbella = error("Should never be translating an intTerm");
}




{-
  LIST SYNTAX
-}

aspect production listTerm
top::Term ::= contents::ListContents
{
  top.fromAbella = error("Should never be translating a listTerm");
}




{-
  PAIR SYNTAX
-}

aspect production pairTerm
top::Term ::= contents::PairContents
{
  top.fromAbella = error("Should never be translating a pairTerm");
}




{-
  STRING CONSTANTS
-}

aspect production stringTerm
top::Term ::= contents::String
{
  top.fromAbella = error("Should never be translating a stringTerm");
}


--This is just for getting strings vs. lists of strings correct
aspect production charTerm
top::Term ::= char::String
{
  top.fromAbella = error("Should never be translating a charTerm");
}

