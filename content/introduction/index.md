+++
title = "Introduction"
weight = 0
+++


Programming is hard. There's a lot of keep track of, and a lot of ways things can go horribly wrong. To clamp down on the number of ways things can go horribly wrong, we use a variety of tools: unit tests, static analysis, code reviews, etc. All of these help make sure that the code works as intended.

But they do **not** help make sure that what you intended is what you actually want. They help with the code, but what if there's a bug in the design itself? That happens far more often than we'd like to admit. Think of all the times where you said "That'll never happen" and it happened. How can we make sure we're not making mistakes in our flowcharts?

Turns out we've known how to do this for decades: build a blueprint in a _specification language_, then run a model checker on it. By rigorously describing your high-level design in a concrete, analyzable language, you can test the design itself. We call this _formal methods_, and studies estimate fixing a bug takes only 1% as long when caught in the specification than in the actual code.

If formal methods are so powerful, why isn't everybody using them? They have a reputation of being difficult, time-consuming processes that often aren't worth the time. The general industry consensus is that formal methods can be used to prove abstract algorithms and keep space shuttles from exploding, but aren't worth the years of investment outside of those niches.  

At eSpark Learning, though, we found that this was completely wrong. Our modeling tool of choice, TLA+, can be taught in a few days and a model that finds critical bugs can be written in under an hour. It turns out the problem isn't how hard formal methods are, it's that everybody just thinks they're hard. Everybody assumes they're only for critical systems, so people don't try to apply them to anything simpler.

This is intended to be a guide to TLA+, aimed at making it practical for day-to-day startup work.

NOTE: This is still being worked on. **Most of the content is here but there's still a lot of editing to be done.** If you see something that doesn't make sense or is explained badly, please contact me at hwayne+tla@gmail.com.
