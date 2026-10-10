<# Formal Flying Machines
The goal of this repository is to mathematically formalize Minecraft flying machines to ultimately prove that push limit 1 flying machines do not exist.

The project was originally inspired by a slimestone challange proposed by **KK**: is a push limit 2 flying machine possible?
KK later managed to design one such machine, thus completely solving the problem: [Flying Machine but Pistons Can Only Move 2 Blocks | Minecraft JE 1.11+](https://youtu.be/22UL5d4G3mY)

This, however, motivates the search for the exact push limit bound that guarantees the existence of flying machines.



# Push Limit 1

An approach tested at the moment is to create a simplified logic of Minecraft mechanics required for flying machines, and try to prove that no flying machines are possible within these simplified logic, called `Reductions`, see `main.pdf` for detailled information.
If any valid engine in Minecraft has a representation in this Reduction, a proof that no flying machine exists in the Reduction implies that no flying machine with Push Limit 1 exists in Minecraft.


## GoP1 reduction

`GoP1_counter_example.lean` affirms statements about a game `GoP1` described in section `Reductions` of `main.pdf`. This reduction has a known counter example (https://claude.ai/artifact/KAtdtahmKoTCsagzpbo1TP).
**Note: This counter-example is not a valid vanilla Minecraft Push Limit 1 flying machine !**
This counter-example only shows that the `GoP1` reduction allows Push Limit 1 engines.

The Lean files sets the rules, builds a decider, checks the example works, builds some simple lemmas.
Lean entirely made by Claude Sonnet 5.5 medium on 10/10/2026 in 15 mins (https://claude.ai/share/feb03dc3-64e1-4846-b6c4-3af80b7fd70b).