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

/-
# Admin stuff :
---------------
- We can meet MTW both orning and afternoon sessions.
- That gives us 5 workdays.

- Friday : Show project to Zulip community. (https://leanprover.zulipchat.com/)
  -- Definitely always have zero errors.
  -- Make the github public
  -- Share our code and ask for feedback.
  -- Ask if we can submit some of our code to Mathlib as PRs. (Code rot)

- How many propositions can we get done by the end of this week?
  -- Euclid  : 
  -- Hilbert :

- Final presentation video/submission.
  -- Presentation and Poster are due June 24th.
  -- June 23rd: it needs to be ready.
  -- June 22nd: I can review it.
  -- June 21st: Submit a draftversion to me for review.
  -- June 18,19,20 : Work on presentation and poster. (90% of the content can be picked up from the wiki).
  -- Presentation should  convey:
  1. Goal: learn Lean & formalize geometry.
  2. Why is it important?
  3. What does working with lean look/feel like.
  4. The math involved -- type theory, Euclid, Hilbert. (maybe mention Tarski).
  5. How far did we get, what more needs to be formalized.


# Lambdas :
-----------
μ : to denote distance (it is a "measure")
There is an entire theory about "measures" called Measure Theory (leangths, areas, integral calculus, propobility theory etc.)

λ : is a reserved symbol. Used for lambda expressions (Lambda Calculus?).


mlist : is a python list
  >>> sorted(mylist, key=lambda value : str(value))

Theory of Computers/Computation
- Alan Turing (Turing machines)   : underlying theory for languages like C, C++, Sql
- Alonzo Church (Lambda Calculus) : more higher-level. All functional languages are based on this -- Haskell, Scala, Lea, Agda, Coq etc.
- Church-Turing Thesis
  => Turing machines == Lambda calculus == Every computer every possible == Human brains

Lambda calculus depends on the concept of functions as first-class objects.
Lambda operator is used for defining functions easily.

def f (n : ℕ) := n + 1 

f = λ (n : ℕ) (s : string) , n + 1 + len(s)

Think of λ as a function-factory.



# Mathematical Trust :
---------------------

Things that were proved by computer but not by hand:
- Four Color Theorem: Haken and Appel's proof.
  They used a computer.
  

Things that were proved by  hand but not by computer:
- ABC conjecture -- Mochizuki proposed a proof.


Things that were verified both ways:
- Fermat's last theorem : Andrew Wiles' proof


Traditionally, we don't trust the author of the proof but we do trust
a review committee (consisting of other mathematicians).

Now, we can formalize math into a Theorem Prover.  But then, the
problem shifts to trusting the Language itself.  The solution is to
minimize the size of the "Language kernel" ~ 1000 lines of codes.

MetaMath project is a meta project for verifying the verifier.
MetaMath's kernel is even smaller ~ 100 lines of code.

This idea is so popular that it is gaining traction in the form of
Software and Hardware verification.

Paper → Journal → Peer review → Published
Paper + Coputer-checked Proof → Journal → Publish
Software + Software verification certificate → Ubuntu/Windows/Apple store 

-/
