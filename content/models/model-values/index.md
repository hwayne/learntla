+++
title = "Model Values"
weight = 10
draft = true
+++

Up until now we've used three basic types of values: strings ("a"), numbers, and booleans. While these work, it doesn't scale very well. For example, if your spec has both students and teachers, you may want to enforce that no students are teaching other students. If you represent every student and teacher with a number, enforcing this becomes unweildy very quickly.

To resolve this, we have a fourth basic type: the model value. The only way to use it is to define a constant and then assign it such a value in the model overview. A constant with an "ordinary model value" is only equal to itself.

[example]
[why you care]

### Set of Model Values

[[We can also assign a constant to a _set_ of model values.

```
Apps <- {facebook, twitter, instagram}
Users <- {user1, user2}
```

Then if we write `CHOOSE user \in Users`, we know that user will be either `user1` or `user2`. We can also use these model values in ordinary assignment:

[[more]]

]]
