-- We try and formalize the Axioms for the area method.
-- Based on a writeup present here: https://hal.archives-ouvertes.fr/hal-00426563v2
-- due to Chou, Gao and Zhang.

import data.real.basic tactic
noncomputable theory
open_locale classical



-- Points are a fixed type and Segments are pairs of points
constant Point : Type

-- Binary function on points that gives the signed length of a segment.
constant dist : Point → Point → ℝ
local infix  `⬝`: 100 := dist
-- Ternary function on points denoting the signed area of a triangle.
constant S : Point → Point → Point → ℝ

-- Shorthand for the Pythagoream measure
def P (a b c : Point) : ℝ := (a⬝b)^2 + (b⬝c)^2 - (a⬝c)^2
-- Shorthand for parallellism

def parallel (a b c d : Point) : Prop := S a c d = S b c d
def perp     (a b c d : Point) : Prop := P a c d = P b c d

def S' (a b c d : Point) : ℝ := S a b c + S a c d
def P' (a b c d : Point) : ℝ := P a b d - P c b d


/-- Axioms
    ====== -/

variables (a b c d e f p₁ p₂ p : Point) (r : ℝ)

axiom one      : a⬝b = 0 ↔ a = b
axiom two      : S a b c = S c a b
axiom three    : S a b c = - S b a c
axiom four     : S a b c = 0 → a⬝b + b⬝c = a⬝c
axiom five     : ∃ (a b c : Point), S a b c ≠ 0
axiom six      : S a b c = S d b c + S a d c + S a b d
axiom seven    : ∃ (p : Point), S a b p = 0 ∧ a⬝p = r*a⬝b
axiom eight    : a ≠ b → S a b p₁ = 0 → a⬝p₁ = r*a⬝b → S a b p₂ = 0 → a⬝p₂ = r*a⬝b → p₁ = p₂
axiom nine     : parallel p₁ p₂ c d → p₁⬝p₂/c⬝d = 1 → parallel d p₂ p₁ c
axiom ten      : S p a c ≠ 0 → S a b c = 0 → a⬝b/a⬝c = S p a b / S p a c
axiom eleven   : c ≠ d → perp a b c d → perp e f c d → parallel a b e f
axiom twelve   : a ≠ b → perp a b c d → parallel a b e f → perp e f c d
axiom thirteen : perp f a b c → S f b c = 0 → 4*(S a b c)^2 = a⬝f^2 * b⬝c^2

/- Elementary Construction Steps
   ============================= -/

inductive Line : Type
| mk : Point → Point → Line

axiom ecs1 : infinite Point
axiom ecs2 (uv pq : Line) : ¬ parallel u v p q → u ≠ v → p ≠ q → ∃ y, S u v y = 0 ∧ S p q y = 0
axiom ecs3 (p u v : Point) : u ≠ v → ∃ y, perp p y u v ∧ S u v y = 0
axiom ecs4 (w u v : Point) (r : ℝ) : u ≠ v → ∃ y, parallel w y u v ∧ (w⬝y/u⬝v = r)
axiom ecs5 (u v : Point) (r : ℝ) : u ≠ v → ∃ y, perp u y u v ∧ (4*S u v y / P u v u = r)
