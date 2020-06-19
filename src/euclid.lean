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
axiom distance_not_neg (p1 p2 : Point) : 0 ≤ distance p1 p2
axiom distance_pos (p1 p2 : Point) : p1 ≠ p2 → 0 < distance p1 p2
axiom distance_is_symm_op : is_symm_op Point ℝ distance
@[simp] axiom distance_zero_segment (p : Point) : distance p p = 0

@[simp, symm] lemma distance_is_symm : ∀ (p1 p2 : Point),
  distance p1 p2 = distance p2 p1 := distance_is_symm_op.symm_op


-- Congruence is an equivalence relation.
axiom cong_is_equiv (A : Type) : is_equiv A (≃)

-- TODO: The proof for the following lemmas follows from cong_is_equiv.
@[refl] lemma cong_refl {A : Type} (a : A) : a ≃ a :=
  sorry
@[symm] lemma cong_symm {A : Type} (a b: A) : a ≃ b → b ≃ a :=
  sorry
@[trans] lemma cong_trans {A : Type} (a b c: A) : a ≃ b → b ≃ c → a ≃ c :=
  sorry
lemma cong_equiv {A : Type} : equivalence (@congruent A) :=
  -- The @ makes implicit arguments explicit.
  mk_equivalence congruent cong_refl cong_symm cong_trans


-- #Postulate I
---------------
-- Given two distinct Points, we can construct a unique Line passing
-- through them.
constant line_of_points (p₁ p₂ : Point) : p₁ ≠ p₂ → Line
axiom line_exists (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
  let l : Line := line_of_points p₁ p₂ h in
  lies_on p₁ l ∧ lies_on p₂ l


structure Segment: Type :=
(p1 p2 : Point)

local infix `⬝`:56 := Segment.mk  -- typed as \ cdot

-- # Helper functions
---------------------
-- condition for 3 terms being distict.
def distinct {A : Type} (a b c : A) := a ≠ b ∧ b ≠ c ∧ c ≠ a


-- length of a segment
def length (a : Segment) := distance a.p1 a.p2
@[simp] lemma distinct_shift (a b c : Point) : distinct a b c → distinct b c a := sorry

-- Missing axiom:
-----------------
@[symm] axiom segment_symm (p1 p2 : Point) : p1 ⬝ p2 ≃ p2 ⬝ p1
axiom zero_segment (s : Segment) (p : Point) : s ≃ p⬝p → s.p1 = s.p2


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

-- Two Rays are opposite if they are distict, have the same base Point and the same Line.
def opposite_rays (r1 r2 : Ray) (h1 : r1.base ≠ r1.ext) (h2 : r2.base ≠ r2.ext) : Prop :=
  (r1.base = r2.base) ∧ (r1 ≠ r2) ∧ (line_of_ray r1 h1 = line_of_ray r2 h2)


-- An Angle is constructed by specifying two Rays based at a common Point and a proof that
-- the Rays are not opposite.
structure Angle: Type :=
(r1 r2 : Ray)
(eq_base : r1.base = r2.base)
(not_opposite (h1 : r1.base ≠ r1.ext) (h2 : r2.base ≠ r2.ext) : ¬ opposite_rays r1 r2 h1 h2)

-- A Triangle is constructed by specifying three Points.
structure Triangle: Type :=
(p1 p2 p3 : Point)

def angle_of_points (a b c : Point) (diffrent : distinct a b c) : Angle :=
  let r1 := Ray.mk b a in
  let r2 := Ray.mk b a in
  let same_base : r1.base = r2.base := begin refl, end in
  let not_opposite : ∀ (h1 : r1.base ≠ r1.ext) (h2 : r2.base ≠ r2.ext), ¬opposite_rays r1 r2 h1 h2 := sorry in
  Angle.mk r1 r2 same_base not_opposite

-- For every triangle, we get can define three Segments (its sides).
def sides_of_triangle (t : Triangle): Segment × Segment × Segment :=
  (⟨t.p1, t.p2⟩, ⟨t.p2, t.p3⟩, ⟨t.p3, t.p1⟩)
-- Note that elements of a vector v can be accessed as v.nth 0 etc.
-- Also note that if a vector has lenth n, then asking for element m
-- where m ≥ n returns element (m mod n)


def angles_of_triangle (t : Triangle) (diffrent : distinct t.p1 t.p2 t.p3): vector Angle 3 :=
  let a123 := angle_of_points t.p1 t.p2 t.p3 diffrent in
  let dif2 : distinct t.p2 t.p3 t.p1 :=
    begin apply distinct_shift, exact diffrent, end in
  let a231 := angle_of_points t.p2 t.p3 t.p1 dif2 in
  let dif3 : distinct t.p3 t.p1 t.p2 :=
    begin apply distinct_shift, exact dif2, end in
  let a312 := angle_of_points t.p3 t.p1 t.p2 dif3 in
  ⟨[a123, a231, a312], rfl⟩ 


def is_equilateral (t : Triangle) : Prop :=
  let sides := sides_of_triangle t in
  sides.1 ≃ sides.2.1 ∧ sides.2.1 ≃ sides.2.2


lemma equilateral_triangle_all_sides_equal (t : Triangle) :
  let sides := sides_of_triangle t in
  is_equilateral t → sides.1 ≃ sides.2.2 :=
begin
  intros,
  cases a with h₁ h₂,
  transitivity,
    repeat {assumption},
end


-- this is a predicate on Type Angle
constant is_right_angle : Angle → Prop
constant make_angle : Line → Line → Angle
constant add_angle : Angle → Angle → Angle
constant less_than_angle : Angle → Angle → Prop
constant equal_angle : Angle → Angle → Prop
constant in_circle : Point → Circle → Prop


constant exists_intersection: Line → Line → Prop
constant intersection (l1 l2 : Line) (is_inter : exists_intersection l1 l2): Point
constant is_parallel : Line → Line → Prop
constant rAngle : Angle
axiom constant_rAngle : is_right_angle rAngle


def reorder_between (x z y : Point) := between x y z
def neg_equal (r1 r2 : Ray) := ¬(r1 = r2) → r1 ≠ r2
def not_equal_point (p1 p2 : Point) := ¬(p1 = p2) → (p1 ≠ p2)
def construct_ray (a b : Point) (ne : a ≠ b) (points : set Point):= Ray.mk a b


-- axiom type_equiv : congruent → equivalence
@[symm] axiom between_symm (x y z : Point) : between x y z → between z y x


axiom straight_line (p1 p2 : Point) (not_equal : Prop → (p1 ≠ p2)): Line
axiom right_angle (a1 a2 : Angle) : is_right_angle a1 ∧ is_right_angle a2 → a1 ≃ a2
axiom parallel (l1 l2 : Line) : ¬ exists_intersection l1 l2 → is_parallel l1 l2
-- does not mean equadistant
-- constant lies_on : Point → Line → Prop

--Propositions moded to euclidProps.lean


-- axiom intersect (l1 l2 l3: Line) : ((make_angle l1 l3) + (make_angle l2 l3)) < (rAngle + rAngle) → on_side (Sides_of_line l3).2 (intersection l1 l2)
-- if the angle beteween two lines is less than 2 right angles, the lines meet on that side

-- # Euclid's missing axiom(s)
------------------------------

--If the sum of the radii of two circles is greater than the line joining their centers, then the two circles intersect
--https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI1.html
-- TODO: Find a reference for this. Or find a justification using Coordinate geometry.
constant circles_intersect (c₁ c₂ : Circle) :
  (radius c₁ + radius c₂ >= distance c₁.center c₂.center)

→ (abs (radius c₁ - radius c₂) <= distance c₁.center c₂.center)
  → Point

axiom circles_intersect' (c₁ c₂ : Circle)
  (h₁ : radius c₁ + radius c₂ >= distance c₁.center c₂.center)
  (h₂ : (abs (radius c₁ - radius c₂) <= distance c₁.center c₂.center)) :
  let p : Point := circles_intersect c₁ c₂ h₁ h₂ in
  p ∈ circumference c₁ ∧ p ∈ circumference c₂


def circle_interior (p : Point) (c : Circle) : Prop :=
  distance c.center p < radius c
