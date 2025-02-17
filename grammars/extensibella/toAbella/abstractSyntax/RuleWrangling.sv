grammar extensibella:toAbella:abstractSyntax;

{-
  This file contains some useful functions for dealing with parts of
  definitional clauses in proving.
-}

--Split the body of a rule into separate premises, dropping exists if
--   it is present
function splitRulePrems
[Metaterm] ::= body::Maybe<Metaterm>
{
  return case body of
         | nothing() -> []
         | just(bindingMetaterm(existsBinder(), _, m)) ->
           m.splitConjunctions
         | just(m) -> m.splitConjunctions
         end;
}


--Create pairs of premises to check whether the rule is applicable by
--   checking if it unifies
--If we produce ([a, b], [c, d]), that means we want to unify the set
--   {(a, c), (b, d)}; we produce it as two lists because that is what
--   our unification function takes
--We create an ununifiable pair if we encounter false because that
--   means the rule is not applicable, and this is an easy way to
--   catch that situation
function premiseUnificationPairs
([Term], [Term]) ::= prems::[Metaterm]
{
  return foldr(\ m::Metaterm rest::([Term], [Term]) ->
                 case m of
                 | eqMetaterm(a, b) -> (^a::rest.1, ^b::rest.2)
                 | falseMetaterm() ->
                   (intTerm(1)::rest.1, intTerm(0)::rest.2)
                 | _ -> rest
                 end,
               ([], []), prems);
}


--Get the primary component term of a rule with key relation keyRel
function rulePrimaryComponent
Term ::= ruleDef::([Term], Maybe<Metaterm>) keyRel::RelationEnvItem
{
  return elemAtIndex(ruleDef.1, keyRel.pcIndex);
}
