grammar extensibella:common:abstractSyntax;

{-
  This file provides some common functions for name translation and
  checking, such as translating between Abella and user-facing names
  and checking if names have these forms.
-}


--To make a consistent separator for names, I'm going to set it here
global name_sep::String = "-$-";


--module for standard library
global extensibellaStdLib::QName = toQName("extensibella:stdLib");


{-
  When we're translating things, we're going to end up needing the
  names of some constants that will be defined in Abella.  We will
  have those as globals here.
-}

global natSuccName::String = "$succ";
global natZeroName::String = "$zero";

global integerType::Type =
       nameType(toQName("$lib__integer"));
global posIntegerName::String = "$posInt";
global negIntegerName::String = "$negSuccInt";
global integerAdditionName::String = "$plus_integer";
global integerSubtractionName::String = "$minus_integer";
global integerMultiplicationName::String = "$multiply_integer";
global integerDivisionName::String = "$divide_integer";
global integerModulusName::String = "$modulus_integer";
global integerNegateName::String = "$negate_integer";
global integerLessName::String = "$less_integer";
global integerLessEqName::String = "$lesseq_integer";
global integerGreaterName::String = "$greater_integer";
global integerGreaterEqName::String = "$greatereq_integer";

global is_string::QName = toQName("is_string");

global appendName::String = "$append";

global pairTypeName::String = "$lib__pair";
global pairConstructorName::String = "$pair_c";

global boolType::Type = nameType(toQName("$lib__bool"));
global orName::String = "$or_bool";
global andName::String = "$and_bool";
global notName::String = "$not_bool";
global trueName::String = "$btrue";
global falseName::String = "$bfalse";

global propType::Type = nameType(toQName("prop"));

function listType
Type ::= ty::Type
{
  return functorType(nameType(toQName("list")), ty);
}

function pairType
Type ::= a::Type b::Type
{
  return functorType(
           functorType(nameType(toQName(pairTypeName)),
                       a), b);
}



function ordinalToCharConstructor
String ::= ord::Integer
{
  return "$c_" ++ toString(ord);
}

function integerToIntegerTerm
Term ::= i::Integer
{
  return
     if i >= 0
     then buildApplication(basicNameTerm(posIntegerName),
                           [integerToNatTerm(i)])
     else buildApplication(basicNameTerm(negIntegerName),
                           [integerToNatTerm((i * -1) - 1)]);
}

function integerToNatTerm
Term ::= i::Integer
{
  return
     if i == 0
     then basicNameTerm(natZeroName)
     else buildApplication(basicNameTerm(natSuccName),
                           [integerToNatTerm(i-1)]);
}



function transName
QName ::= ty::QName
{
  --need to add "$trans__" to first module portion
  return case ty of
         | basicQName(s) -> transQName(s)
         | tyQName(s) -> transQName(s)
         | _ -> error("Translating types cannot have other prefixes")
         end;
}




-- ~99% of the time, this is what we want
function basicNameTerm
Term ::= name::String
{
  return nameTerm(toQName(name), nothingType());
}
