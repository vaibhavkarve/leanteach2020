import tactic

noncomputable theory
open_locale classical

-- # Propositions as Types
--------------------------

/-  How should we interpret (a : A)

a is a term
A is a Type (a collection of terms)
analogous to a ∈ A (in set theory)

If A is a Proposition
then a : A means that we have a proof of A

h : p1 ≠ p2

p1 ≠ p2 is a Proposition but it is itself a Type
h is a term (and also a proof) of Type p1 ≠ p2


Curry-Howard Isomorphism : CS ∩ Math
-------------------------------------
Propositions ↔ Types
Proofs ↔ Terms
Algorithms ↔ Proofs ↔ Programs
Definitions (of CS functions) ↔ Theorem statements 

Curry -> Function currying && Haskell
Howard : Prof. at University of Illinois -- Chicago

def f  : A × B → C    (uncurry-ied function)
def f' : A → B → C   (curry-ied function)

***Lambda Calculus***  This is the underlying math behind any higher-order programming language



f (a, b) : C
f a    ----- Type error

f' : A → B → C
f' a : B → C
f' a b : C



Proof-irrelevance:  (works only for Prop type)
---------------------------------------------
It doesn't matter which proof we pick
h : p1 ≠ p2
We cannot break h into smaller parts.
In other words, if h' : p1 ≠ p2
Then h and h' are the same.

h h' : p1 ≠ p2 (here they are irrelevant)
5 8  : ℕ 
5 ≠ 8 (here the terms are not! irrelevant)

-/
