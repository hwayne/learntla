+++
title = "[After Concurrency Example]"
weight = 7
draft = true
+++

We now have all of the pieces we need, so let's put it all into practice.

## The Problem

As part of your project, you need to scrape BryceTech's API for Widget results. Because nothing can be easy, the API has two restrictions you know about:

1. The results are paginated. If you have more than N results, you will get the first N and a `next` token. You need to get all of the results.
1. The API is ratelimited. Any query can return a `PAST_LIMIT` error instead of the results you need.

As part of your requirements, you don't want to make any requests until the limit expires. (more stuff)

### Initial Design

We'll start by building an extremely simple skeleton of the pagination and rate limiting logic.

```
==== MODULE asdasd ==== 
(* --algorithm
variables next = TRUE; past_limit = FALSE;

begin Request:
  while next = TRUE do
    CheckTimeout:
      if past_limit then
        past_limit := FALSE;
      else
        MakeRequest:
          either
            next := TRUE;
          or
            next := FALSE;
          or
            past_limit := TRUE;
          end either;
      end if;
  end while;
end algorithm; *)
----
```

Note how we've completely abstracted out the timer; either we wait for the limit to expire (`Request -> CheckTimeout -> Request`) or make a request (`Request -> CheckTimeout -> MakeRequest`) that either returns data with a `next` flag, returns the last data, or returns that we've exceeded the rate limit.

We can test this by adding the following invariant to our model:

`ENABLED MakeRequest => next /\ ~past_limit`

In other words, we can only run the MakeRequest step if the next flag is there and we are not past limit

{{% notice info %}}
Something about knowing logic here, if not, maybe something about ENABLED?
{{% /notice %}}

The model should pass.

### Making Things More Complicated

TODO
