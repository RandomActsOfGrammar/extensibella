grammar extensibella:toAbella:abstractSyntax;


nonterminal SearchWitness with
   pp, abella_pp,
   boundNames,
   toAbella<SearchWitness>, toAbellaMsgs,
   typeEnv, relationEnv, constructorEnv, currentModule, proverState;
propagate typeEnv, relationEnv, constructorEnv, proverState,
          currentModule, boundNames, toAbellaMsgs on SearchWitness;

abstract production trueSearchWitness
top::SearchWitness ::=
{
  top.pp = text("true");
  top.abella_pp = "true";

  top.toAbella = ^top;
}


abstract production applySearchWitness
top::SearchWitness ::= name::String
{
  top.pp = text("apply " ++ name);
  top.abella_pp = "apply " ++ name;

  top.toAbella = ^top;
}


abstract production leftSearchWitness
top::SearchWitness ::= sub::SearchWitness
{
  top.pp = ppConcat([text("left ("), sub.pp, text(")")]);
  top.abella_pp = "left (" ++ sub.abella_pp ++ ")";

  top.toAbella = leftSearchWitness(sub.toAbella);
}


abstract production rightSearchWitness
top::SearchWitness ::= sub::SearchWitness
{
  top.pp = ppConcat([text("right ("), sub.pp, text(")")]);
  top.abella_pp = "right (" ++ sub.abella_pp ++ ")";

  top.toAbella = rightSearchWitness(sub.toAbella);
}


abstract production splitSearchWitness
top::SearchWitness ::= l::SearchWitness r::SearchWitness
{
  top.pp = ppConcat([text("split("), l.pp, text(", "), r.pp, text(")")]);
  top.abella_pp =
      "split(" ++l.abella_pp ++ ", " ++ r.abella_pp ++ ")";

  top.toAbella = splitSearchWitness(l.toAbella, r.toAbella);
}


abstract production introsSearchWitness
top::SearchWitness ::= names::[String] sub::SearchWitness
{
  top.pp = ppConcat([text("intros ["),
              ppImplode(cat(text(","), line()), map(text, names)),
              text("]"), line(), text("("), sub.pp, text(")")]);
  top.abella_pp =
     "intros [" ++ foldr1(\a::String b::String -> a ++ ", " ++ b, names) ++
     "] (" ++ sub.abella_pp ++ ")";

  top.toAbella = introsSearchWitness(names, sub.toAbella);
}


abstract production forallSearchWitness
top::SearchWitness ::= names::[String] sub::SearchWitness
{
  top.pp = ppConcat([text("forall ["),
              ppImplode(cat(text(","), line()), map(text, names)),
              text("]"), line(), text("("), sub.pp, text(")")]);
  top.abella_pp =
     "forall [" ++ foldr1(\a::String b::String -> a ++ ", " ++ b, names) ++
     "] (" ++ sub.abella_pp ++ ")";

  top.toAbella = forallSearchWitness(names, sub.toAbella);
}


abstract production existsSearchWitness
top::SearchWitness ::= withs::Withs sub::SearchWitness
{
  top.pp = ppConcat([text("exists ["),
              if withs.len == 0 then text("")
               else cat(text(" with "), ppImplode(line(), withs.pps)),
              text("]"), line(), text("("), sub.pp, text(")")]);
  local withsString_abella::String =
     if withs.len == 0
     then ""
     else " with " ++ withs.abella_pp;
  top.abella_pp = "exists [" ++ withsString_abella ++ "] (" ++
                  sub.abella_pp ++ ")";

  top.toAbella = existsSearchWitness(withs.toAbella, sub.toAbella);
}


abstract production unfoldSearchWitness
top::SearchWitness ::= name::String n::Integer swl::[SearchWitness]
{
  top.pp = ppConcat([text("unfold("), text(name), text(", "),
                     text(toString(n)),
                     if null(swl) then text("")
                      else ppImplode(cat(text(","), line()),
                              map((.pp), swl)), text(")")]);
  local swlString_abella::String =
     if null(swl)
     then ""
     else foldr1(\a::String b::String -> a ++ ", " ++ b,
                 map(\x::SearchWitness -> x.abella_pp, swl));
  top.abella_pp = "unfold(" ++ name ++ ", " ++ toString(n) ++
                  swlString_abella ++ ")";

  top.toAbella = error("unfoldSearchWitness.toAbella");
}


abstract production starSearchWitness
top::SearchWitness ::=
{
  top.pp = text("*");
  top.abella_pp = "*";

  top.toAbella = ^top;
}


abstract production eqSearchWitness
top::SearchWitness ::=
{
  top.pp = text("=");
  top.abella_pp = "=";

  top.toAbella = ^top;
}

