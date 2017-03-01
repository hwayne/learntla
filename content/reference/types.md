+++
title = "Data Types"
weight = 1
+++

## Primitives

### Boolean

TRUE, FALSE.

```
BOOLEAN = {TRUE, FALSE}
```

### Numbers

1, -1, -2, etc. You need to `EXTENDS Integers` to perform arithmetic operations.

### Strings

"a", "b", "ab", etc.

### Model Values

Defined in the model options. Only assignable to constants. A model value is unequal to anything but itself.

## Sets

```tla
{"a", "bc"} = {"a", "bc"}

S == {1, 2, 3}

3 \in S = TRUE; 4 \in S = FALSE;
{2, 3} \subseteq S = TRUE; {2, 4} \subseteq S = FALSE

S \union {3, 4} = {1, 2, 3, 4}
S \intersect {3, 4} = {3}
S \ {3, 4} = {1, 2}

UNION {{1}, {2}} = {1, 2}
SUBSET {1, 2} = {{}, {1}, {2}, {1, 2}}

EXTENDS Integers
1..3 = S

{x*x : x \in S} = {1, 4, 9}
{x*y : x \in S, y \in S} = {1, 2, 3, 4, 6, 9}

{x \in S : x >= 2} = {3}
{<<x, y>> \in S \X S : x + y > 4} = {<<2, 3>>, <<3, 2>> <<3, 3>>}

EXTENDS FiniteSets
IsFiniteSet(S) = TRUE
Cardinality(S) = 3
```

## Functions

```tla
S == {1, 2, 3}

F(S) == [x \in S |-> x + 1]
F(1..10)[4] = 5

F(S) == [x \in S, y \in S |-> x + y]
F(1..10)[2, 3] = 5
F(1..10)[<<2, 3>>] = 5

F[x \in 1..10] == x + 1
F[2] = 3

DOMAIN [x \in S |-> P(x)] = S

[{1, 2} -> BOOLEAN] = {
                        <<FALSE, FALSE>>, <<TRUE, TRUE>>,
                        <<FALSE, TRUE>>, <<TRUE, FALSE>> 
                      }
```

## Tuples

All function operations also apply to tuples. A tuple has domain 1..N, where N is the length of the tuple.

```tla
T == <<"a", "b">>

DOMAIN T = 1..2
<<"a", "b">>[1] = "a"

{1, 2} \X T = { 
                <<1, "a">>, <<1, "b">>,
                <<2, "a">>, <<2, "b">>
              }

EXTENDS Sequences
T == <<"a", "b", "c", "d">>

Len(T) = 4
Head(T) = "a"
Tail(T) = <<"b", "c", "d">>

<<"e">> \o T = <<"e", "a", "b", "c", "d">>
Append(T, "e") = <<"a", "b", "c", "d", "e">>
Subset(T, 2, 3) = <<"b", "c">>
SelectSeq(T, lambda x: x \in {"a", "d"}) = <<"a", "d">>
```

## Structures

All function operations also apply to structures. The domain is the set of strings corresponding to the structure's keys.

```tla
S == [a |-> 1, b |-> 2]
DOMAIN S = {"a", "b"}
S['a'] = 1
S.b    = 2

[a: {1, 2}, b: {"x", "y"}] =
  {
    [a |-> 1, b |-> "x"], [a |-> 1, b |-> "y"],
    [a |-> 2, b |-> "x"], [a |-> 2, b |-> "y"]
  }
```

## Bags

See _Specifying Systems_.
