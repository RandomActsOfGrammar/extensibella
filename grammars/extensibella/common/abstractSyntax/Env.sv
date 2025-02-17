grammar extensibella:common:abstractSyntax;


type Env<a> = [a];


--Get all the entries for the name from the environment
function lookupEnv
attribute name {} occurs on a => [a] ::= name::QName env::Env<a>
{
  return
     findAllEnv(
        if name.isQualified
        then \ item::a -> item.name == ^name
        else \ item::a -> item.name.shortName == name.shortName,
        env);
}


--Why have these?  In case we change the definition of Env
function buildEnv
attribute name {} occurs on a => Env<a> ::= l::[a]
{
  return l;
}

function addEnv
Env<a> ::= base::Env<a> add::[a]
{
  return base ++ add;
}


--Find all the items in the Env for which f is true
function findAllEnv
[a] ::= f::(Boolean ::= a) e::Env<a>
{
  return filter(f, e);
}


--Print an environment, for debugging purposes
function printEnv
attribute name {} occurs on a => String ::= e::Env<a>
{
  return "[" ++ implode(", ", map(\ a::a -> justShow(a.name.pp), e)) ++ "]";
}





data nonterminal TypeEnvItem with
   name, type, projTypes, isLangType, isProofType, isLibType, kind,
   unknownConstrI, clauseModules;

synthesized attribute isLangType::Boolean;
synthesized attribute isProofType::Boolean;
synthesized attribute isLibType::Boolean;
synthesized attribute projTypes::TypeList;
synthesized attribute kind::Integer; --number of args to type
synthesized attribute unknownConstrI::QName;

--the modules for the PC of the clauses, in clause order
synthesized attribute clauseModules::[QName];

--types defined in the language encoding
abstract production langTypeEnvItem
top::TypeEnvItem ::= name::QName kind::Integer args::TypeList
                     clauseModules::[QName]
{
  top.name = ^name;
  top.type = nameType(^name);

  top.isLangType = true;
  top.isProofType = false;
  top.isLibType = false;

  top.kind = kind;

  top.projTypes = ^args;

  top.unknownConstrI = unknownIQName(^name);

  top.clauseModules = clauseModules;
}


--types defined in the standard library
abstract production libTypeEnvItem
top::TypeEnvItem ::= name::QName kind::Integer
{
  top.name = ^name;
  top.type = nameType(^name);

  top.isLangType = false;
  top.isProofType = false;
  top.isLibType = true;

  top.kind = kind;

  top.projTypes =
      error("Should not access projTypes on libTypeEnvItem");

  top.unknownConstrI =
      error("Should not access unknownConstrI on libTypeEnvItem");

  top.clauseModules =
      error("Should not access clauseModules on libTypeEnvItem");
}


--types defined in the proof files somewhere (current or imported)
abstract production proofTypeEnvItem
top::TypeEnvItem ::= name::QName kind::Integer
{
  top.name = ^name;
  top.type = nameType(^name);

  top.isLangType = false;
  top.isProofType = true;
  top.isLibType = false;

  top.kind = kind;

  top.projTypes =
      error("Should not access projTypes on proofTypeEnvItem");

  top.unknownConstrI =
      error("Should not access unknownConstrI on proofTypeEnvItem");

  top.clauseModules =
      error("Should not access clauseModules on proofTypeEnvItem");
}


--variable type in a theorem or definition
abstract production typeVarEnvItem
top::TypeEnvItem ::= name::String
{
  top.name = basicQName(baseName(name));
  top.type = varType(name);

  top.isLangType = false;
  top.isProofType = false;
  top.isLibType = false;

  top.kind = 0;

  top.projTypes =
      error("Should not access projTypes on typeVarEnvItem");

  top.unknownConstrI =
      error("Should not access unknownConstrI on typeVarEnvItem");

  top.clauseModules =
      error("Should not access clauseModules on typeVarEnvItem");
}




-- .type is built type
-- .types is arguments
data nonterminal ConstructorEnvItem with name, type, types;

abstract production constructorEnvItem
top::ConstructorEnvItem ::= name::QName builtType::Type args::TypeList
{
  top.name = ^name;

  top.type = ^builtType;
  top.types = ^args;
}





data nonterminal RelationEnvItem with
   name, types, isExtensible, pcIndex, pcType, clauseModules,
   defsList, unknownConstrK;

synthesized attribute pcIndex::Integer;
synthesized attribute pcType::Type;
synthesized attribute defsList::[([Term], Maybe<Metaterm>)];
synthesized attribute unknownConstrK::QName;

abstract production extRelationEnvItem
top::RelationEnvItem ::= name::QName args::TypeList pcIndex::Integer
          clauseModules::[QName] defsList::[([Term], Maybe<Metaterm>)]
{
  top.name = ^name;

  top.types = ^args;

  top.isExtensible = true;

  top.pcIndex = pcIndex;
  top.pcType = head(drop(pcIndex, args.toList));

  top.clauseModules = clauseModules;

  top.defsList = defsList;

  top.unknownConstrK = unknownKQName(^name);
}


abstract production fixedRelationEnvItem
top::RelationEnvItem ::= name::QName args::TypeList
{
  top.name = ^name;

  top.types = ^args;

  top.isExtensible = false;

  top.pcIndex = error("Should not access on non-extensible relation");
  top.pcType = error("Should not access on non-extensible relation");
  top.clauseModules =
      error("Should not access on non-extensible relation");

  top.defsList =
      error("Should not access defsList on non-extensible relation");

  top.unknownConstrK =
      error("Should not access unknownConstrK on non-extensible relation");
}
