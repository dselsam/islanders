# Islanders

This repository represents an ongoing effort at formalizing the infamous [blue-eyed islanders puzzle](https://xkcd.com/blue_eyes.html) in [The Lean Theorem Prover](https://github.com/leanprover/lean).

## Status

We currently have a [draft axiomization](https://github.com/dselsam/islanders/blob/master/knows.lean) of dynamic knowledge among a collection of agents, a [representation](https://github.com/dselsam/islanders/blob/master/problem.lean) of a simple variant of the islanders puzzle, and a [proof](https://github.com/dselsam/islanders/blob/master/islanders_n2.lean) of the solution to the puzzle for the simple case where there are only two people on the island. We also have a proof sketch for the general case, with [a sorry-filled instantiation for n=3](https://github.com/dselsam/islanders/blob/master/islanders_n3.lean).

## Challenges

To formalize the full puzzle for an arbitrary number of people, we will likely need to add additional axioms that permit the agents to perform more sophisticated reasoning. We will also need to develop tactics that automate certain types of repetitive reasoning.

## Contributions

Contributions extremely welcome!
