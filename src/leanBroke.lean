/- Formalizing Euclid's Axioms.-/
import tactic
import data.real.basic  -- imports ℝ
noncomputable theory
open_locale classical


-- # Postulated types and relations
----------------------------------
constant Point : Type
constant Line : Type
constant lies_on : Point → Line → Prop
constant between : Point → Point → Point → Prop  -- (between a b c) means "b is in between a and c"
constant congruent {A : Type} : A → A → Prop  -- variable A is implicit. Lean will figure it out.
-- Missing definition that Euclid needed but did not include:
constant distance : Point → Point → ℝ


-- Notation
-----------
local infix ` ≃ `:55 := congruent  -- typed as \ equiv


-- Missing Axiom(s)
-------------------
axiom distance_not_neg (p1 p2 : Point) : distance p1 p2 >= 0
axiom distance_is_symm_op : is_symm_op Point ℝ distance

@[simp] lemma distance_is_symm : ∀ (p1 p2 : Point), distance p1 p2 = distance p2 p1 := distance_is_symm_op.symm_op


@[simp, refl] axiom cong_refl {A : Type} (a : A) : congruent a a
@[symm] axiom cong_symm {A : Type} (a b: A) : congruent a b → congruent b a
@[trans] axiom cong_trans {A : Type} (a b c: A) : congruent a b → congruent b c → congruent a c

@[simp] lemma cong_equiv {A : Type} : equivalence (@congruent A) := mk_equivalence congruent cong_refl cong_symm cong_trans  -- The @ makes implicit arguments explicit.
--instance cong_is_equiv (A : Type) : is_equiv A (≃):= {symm := cong_symm, refl := cong_refl, trans := cong_trans}
@[refl, symm, simp] axiom cong_is_equiv (A : Type) : is_equiv A (≃)


-- Postulate I
--------------
-- Given two distinct Points, we can construct a unique Line passing through them.
constant line_of_points (p₁ p₂ : Point) : p₁ ≠ p₂ → Line
axiom line_exists (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
  let l : Line := line_of_points p₁ p₂ h in
  lies_on p₁ l ∧ lies_on p₂ l


structure Segment: Type :=
(p1 p2 : Point)


-- # Helper functions
---------------------
-- condition for 3 terms being distict.
def distinct {A : Type} (a b c : A) := a ≠ b ∧ b ≠ c ∧ c ≠ a

-- Missing axiom:
-----------------
local infix `⬝`:56 := Segment.mk  -- typed as \ cdot
@[symm] axiom segment_symm (p1 p2 : Point) : p1 ⬝ p2 ≃ p2 ⬝ p1


def line_of_segment (s : Segment) : s.p1 ≠ s.p2 → Line := line_of_points s.p1 s.p2
def points_of_segment (s : Segment) : set Point := {c : Point | between s.p1 c s.p2}


-- Postulate II
---------------
-- Given two segments, we can find a Point to extend the first Segment
-- by the lenth of the Second.
constant extended_segment (ab cd : Segment) : ab.p1 ≠ ab.p2 → Point
axiom extend (ab cd : Segment) (h : ab.p1 ≠ ab.p2) :
    let p : Point := extended_segment ab cd h in
    lies_on p (line_of_segment ab h)
    ∧ between ab.p1 ab.p2 p
    ∧ cd ≃ ⟨ab.p2, p⟩


-- A Circle is constructed by specifying two Points.
-- Note: Euclid says that the two points should be distinct. But we choose not to make this
-- a strict requirement for defining a Circle.
structure Circle: Type :=
(center outer : Point)


def radius_segment (c : Circle) : Segment := {p1 := c.center, p2 := c.outer}
def radius (c : Circle) : ℝ :=
  let r := radius_segment c in distance r.1 r.2
def circumference (c : Circle) : set Point := {x : Point | radius_segment c ≃ ⟨c.center, x⟩}


-- A Ray is constructed by specifying two Points.
structure Ray: Type :=
(base ext : Point)

def line_of_ray (r : Ray) : r.base ≠ r.ext → Line := line_of_points r.base r.ext
def points_of_ray (r : Ray) (ne : r.base ≠ r.ext) : set Point :=
     points_of_segment ⟨r.base, r.ext⟩ ∪ {c | lies_on c (line_of_ray r ne) ∧ between r.base r.ext c}

-- lemma ray_circle_intersect (AB : Ray) (ne : AB.base ≠ AB.ext) (C : Circle) (center : C.center = AB.base): 
-- ∃ (p : Point), (p ∈ circumference C) ∧ (p ∈ points_of_ray AB ne) :=
-- begin
-- have h := extend (Segment.mk AB.base AB.ext Segment.mk AB.ext ) CD? ne,
-- end