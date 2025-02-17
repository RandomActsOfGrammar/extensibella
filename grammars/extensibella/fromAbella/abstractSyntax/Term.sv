grammar extensibella:fromAbella:abstractSyntax;


attribute
   fromAbella<Metaterm>
occurs on Metaterm;

aspect production relationMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.fromAbella =
      case rel, args.fromAbella.toList of
      --projection
      | _, projArgs when rel.isProjection ->
        projectionMetaterm(
           foldr(consTermList, emptyTermList(),
                 take(length(projArgs) - 2, projArgs)),
           rel.projFromAbella,
           head(drop(length(projArgs) - 2, projArgs)),
           head(drop(length(projArgs) - 1, projArgs)))
      --special relations with three arguments
      | basicQName(baseName(relName)), [a, b, c] ->
        if relName == integerAdditionName
        then plusMetaterm(a, b, c)
        else if relName == integerSubtractionName
        then minusMetaterm(a, b, c)
        else if relName == integerMultiplicationName
        then multiplyMetaterm(a, b, c)
        else if relName == integerDivisionName
        then divideMetaterm(a, b, c)
        else if relName == integerModulusName
        then modulusMetaterm(a, b, c)
        else if relName == appendName
        then appendMetaterm(a, b, c, ^r)
        else if relName == orName
        then orBoolMetaterm(a, b, c)
        else if relName == andName
        then andBoolMetaterm(a, b, c)
        else relationMetaterm(rel.relFromAbella, args.fromAbella, ^r)
      --special relations/terms with two arguments
      | basicQName(baseName(relName)), [a, b] ->
        if relName == integerNegateName
        then negateMetaterm(a, b)
        else if relName == integerLessName
        then lessMetaterm(a, b)
        else if relName == integerLessEqName
        then lessEqMetaterm(a, b)
        else if relName == integerGreaterName
        then greaterMetaterm(a, b)
        else if relName == integerGreaterEqName
        then greaterEqMetaterm(a, b)
        else if relName == notName
        then notBoolMetaterm(a, b)
        else relationMetaterm(rel.relFromAbella, args.fromAbella, ^r)
      --extSize and projRel relations
      | extSizeQName(_), _ ->
        extSizeMetaterm(rel.relFromAbella, args.fromAbella, ^r)
      | projRelQName(_), _ ->
        projRelMetaterm(rel.relFromAbella, args.fromAbella, ^r)
      --nothing special
      | _, _ ->
        relationMetaterm(rel.relFromAbella, args.fromAbella, ^r)
      end;
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.fromAbella = trueMetaterm();
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.fromAbella = falseMetaterm();
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.fromAbella = eqMetaterm(t1.fromAbella, t2.fromAbella);
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.fromAbella = impliesMetaterm(t1.fromAbella, t2.fromAbella);
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.fromAbella = orMetaterm(t1.fromAbella, t2.fromAbella);
}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.fromAbella = andMetaterm(t1.fromAbella, t2.fromAbella);
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder nameBindings::Bindings body::Metaterm
{
  top.fromAbella =
      bindingMetaterm(^b, nameBindings.fromAbella, body.fromAbella);
}





attribute
   fromAbella<Bindings>
occurs on Bindings;

aspect production oneBinding
top::Bindings ::= name::String mty::MaybeType
{
  top.fromAbella = oneBinding(name, mty.fromAbella);
}


aspect production addBindings
top::Bindings ::= name::String mty::MaybeType rest::Bindings
{
  top.fromAbella = addBindings(name, mty.fromAbella, rest.fromAbella);
}





attribute
   fromAbella<Term>
occurs on Term;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.fromAbella =
      case f.fromAbella, args.fromAbella.toList of
      --pair
      | nameTerm(basicQName(baseName(relName)), _), [a, b]
        when relName == pairConstructorName ->
        pairTerm(addPairContents(a, singlePairContents(b)))
      --integer constants
      | nameTerm(basicQName(baseName("$posInt")), _), [intTerm(i)] ->
        intTerm(i)
      | nameTerm(basicQName(baseName("$negSuccInt")), _), [intTerm(i)] ->
        intTerm(-i - 1)
      | nameTerm(basicQName(baseName("$succ")), _), [intTerm(i)] ->
        intTerm(i + 1)
      --nothing special
      | _, _ ->
        applicationTerm(f.fromAbella, args.fromAbella)
      end;
}


aspect production nameTerm
top::Term ::= name::QName ty::MaybeType
{
  top.fromAbella =
      case name of
      --Booleans
      | basicQName(baseName("$btrue")) -> trueTerm()
      | basicQName(baseName("$bfalse")) -> falseTerm()
      --Integers
      | basicQName(baseName("$zero")) -> intTerm(0)
      --Characters
      | basicQName(baseName(x)) when startsWith("$c_", x) ->
        charTerm(charsToString(
                 [toInteger(substring(3, length(x), x))]))
      --Unknown terms
      | unknownIQName(ty) -> unknownITerm(name.tyFromAbella)
      | unknownKQName(rel) -> unknownKTerm(name.relFromAbella)
      --Other
      | _ -> nameTerm(name.constrFromAbella, ^ty)
      end;
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  top.fromAbella =
      case t1.fromAbella, t2.fromAbella of
      | charTerm(char), stringTerm(contents) ->
        stringTerm(char ++ contents)
      --don't know the list is a string until we see the char
      | charTerm(char), listTerm(emptyListContents()) ->
        stringTerm(char)
      | tm, listTerm(contents) ->
        listTerm(addListContents(tm, ^contents))
      | tm1, tm2 -> consTerm(tm1, tm2)
      end;
}


aspect production nilTerm
top::Term ::=
{
  top.fromAbella = listTerm(emptyListContents());
}


aspect production underscoreTerm
top::Term ::= ty::MaybeType
{
  top.fromAbella = error("Should not translate underscoreTerm");
}





attribute
   fromAbella<TermList>
occurs on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  top.fromAbella = singleTermList(t.fromAbella);
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.fromAbella = consTermList(t.fromAbella, rest.fromAbella);
}


aspect production emptyTermList
top::TermList ::=
{
  top.fromAbella = emptyTermList();
}

