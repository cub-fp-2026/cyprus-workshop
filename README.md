# Cyprus Lean workshop

This project is a two-day Lean workshop with lecture scaffolds and seminar practice.

- Day 1 is logic. `Cyprus.Day1Lecture` covers the connectives, tactic mode, classical reasoning, quantifiers, and knights-and-knaves puzzles, with islanders as values and their roles as a two-valued type. `Cyprus.Day1Seminar` provides practice, ending with the puzzle collection.
- Day 2 is types, functions, and induction, told through the natural numbers. `Cyprus.Day2Lecture` builds `MyNat` and compares it with `Nat`, covers equality and the Nat constructors, defines `double` and `half` by recursion to study injective and surjective functions, introduces the predicate `MyEven` as the image of `double` and the relation `MyLe`, decides `MyEven` with a Boolean function, and ends with optional Collatz. `Cyprus.Day2Seminar` provides practice.
- `Cyprus.Islanders` is the support module for the puzzles. Do not modify it.

## Setup

Install Lean with VS Code and the Lean extension, or install `elan` from https://lean-lang.org. Open this folder in VS Code; `elan` selects the version recorded in `lean-toolchain`. In a terminal in this folder, download the pinned dependencies and build:

```sh
lake exe cache get
lake build
```

## Teaching and exercises

Lecture files are live-teaching scaffolds. They may contain authored `sorry` placeholders that the instructor fills during a session; published updates retain those files unchanged.

Seminar files contain exercises. Replace each `sorry` with your own proof and run `lake build`, or watch the editor, to check it. A puzzle comes in two parts: an `Answer`, which you fill in with `impossible` or a `verdict (A is-a knight, B is-a knave)`, and a theorem whose goal `claim% answer [A, B]` unfolds to whatever your answer claims. Fill in the answer first; the theorem then tells you what to prove. `Cyprus.lean` imports all workshop modules.
