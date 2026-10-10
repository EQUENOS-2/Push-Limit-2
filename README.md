# Formal Flying Machines
The goal of this repository is to mathematically formalize Minecraft flying machines to ultimately prove that push limit 1 flying machines do not exist.

The project was originally inspired by a slimestone challange proposed by **KK**: is a push limit 2 flying machine possible?
KK later managed to design one such machine, thus completely solving the problem: [Flying Machine but Pistons Can Only Move 2 Blocks | Minecraft JE 1.11+](https://youtu.be/22UL5d4G3mY)

This, however, motivates the search for the exact push limit bound that guarantees the existence of flying machines.



# Push Limit 1

PistonFlyingMachine.lean sets the rules for an older version of the game with a known counter example (https://claude.ai/artifact/KAtdtahmKoTCsagzpbo1TP).
The Lean files sets the rules, builds a decider, checks the example works, builds some simple lemmas.
Lean entirely made by Claude Sonnet 5.5 medium on 10/10/2026 in 15 mins (https://claude.ai/share/feb03dc3-64e1-4846-b6c4-3af80b7fd70b).