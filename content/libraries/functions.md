+++
title = "Functions"
weight = 5
+++

All of these assume finite functions.

### Range of a function

```
Range(f) == {f[x] : x \in DOMAIN f}
```

Just a fairly simple application of mapping over a set. This also gives us a way to get the set of elements in a tuple/sequence/structure.

### Functions with a given property

For a given domain D and range R, satisfying property P:
```
{ f \in [D -> R] : P(f) }
```

#### Automorphic

```
IsAutomorphic(f) == DOMAIN f = Range(f)
```

#### Invertible

```
IsInvertible(f) == \A x \in DOMAIN f, y \in DOMAIN f:
                      f[x] = f[y] => x = y

IsInvertible(f) == 
  Cardinality(DOMAIN f) = Cardinality(Range(f)) \* finite functions only
```

### Invert a function

```
Invert(f) == [y \in Range(f) |-> CHOOSE x \in DOMAIN f : f[x] = y]
```

Note that this assumes you _can_ invert it: `CHOOSE` will return an arbitrary element otherwise, which you don't want.
