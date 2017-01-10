+++
title = "Model Values"
weight = 10
+++

Up until now we've used three basic types of values: strings ("a"), numbers, and booleans. While these work, it doesn't scale very well. For example, if your spec has both students and teachers, you may want to enforce that no students are teaching other students. If you represent every student and teacher with a number, enforcing this becomes unweildy very quickly.

To resolve this, we have a fourth basic type: the model value. The only way to use it is to define a constant and then assign it such a value in the model overview. A constant with an "ordinary model value" is only equal to itself.

```
CONSTANT NULL
```

[screenshot]

We can also define a set of model values:

[[ TODO SCREENSHOT THIS ]]
```
Apps <- [ model value ] {facebook, twitter, espark}
Users <- [ model value ] {user1, user2}
```

Once we define a set of model values, we can then use the elements of the set as part of other constants:

```
StartingApp == facebook
```

### Symmetry Sets

[[ TODO ]]
