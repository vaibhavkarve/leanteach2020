# LeanTeach2020 #
Interactive theorem proving in Lean : teaching mathematics to a computer

*Summer 2020 Illinois Geometry Lab + Uni-High research project*


Wiki: [IllioisWiki for LeanTeach](https://wiki.illinois.edu/wiki/display/LT2020) 


## Project Goals: ##

Goal 0 : Teach Lean to Humans.

Goal 1 : Teach Math to a Computer.

## Goal 0 ##

Humans involved : **Alex Dolcos, Edward Kong, Lawrence Zhao, Nicholas
Phillips, Vaibhav Karve**.

We meet 9 hours per week to discuss math, philosophy and programming
as it relates to formalizing mathematics in a theorem prover. We will
be using Microsoft Research's Lean Theorem Prover and its Mathematical
Library (mathlib) as our proof assistant for this. Each of us has
experience programming in Python before this. We will explore how
things work differently in a purely functional language. We will also
learn about tactics in Lean. We will use Slack for text-based
communication, Zoom for video meetings and CoCalc for sharing and
collaboratively editing code.

## Goal 1 ##

The idea is that we can take a piece of familiar mathematics and
translate it into code that is acceptable to Lean. Lean already
understands basic logic and does not accept incorrect mathematics as
input.

We wanted to choose a topic in mathematics that,

- is known to us with a high degree of familiarity – because intuition
  comes in handy when we are stuck in a Math → Lean translation,
- is preferably already in an axiomatized form – we wanted to follow
  the workflow of Definitions → Axioms/Postulates →
  Propositions/Theorems,
- is not already in mathlib – this ruled out group theory, number
  theory, category theory ...

We settled on formalizing Axiomatic Geometry of three types:

- Euclid's axioms
- Hilbert's axioms
- Tarski's axioms
