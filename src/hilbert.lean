-- Hilbert's Axioms Formalized
import data.real.basic tactic
noncomputable theory
open_locale classical

/- Hilbert uses three undefined types: Points, Lines and Planes.

   We define Point as a constant. Lines we define as Structures
   instead of Constants.  We do not define Planes since here, we
   restrict our attention to planar geometry, ignoring solid
   geometry.-/

constant Point : Type

/- A Segment is constructed by specifying two points. The subscripts
   are written as \1 and \2. -/

structure Segment: Type := (p₁ p₂ : Point)


/- This is the Betweenness relation.  It says the Point "y" is in
   between Point "x" and "z".-/

constant B (x y z : Point) : Prop

/- Polymorphism ⇒ make it work for multiple types at the same time.
   For every type A, we assume there is a congruence relation C.
   Here, "A" is an implicit argument. Lean will figure it out by
   reading the type signatures of other arguments.  In other languages
   this is called over-loading.-/

constant C {A : Type} : A → A → Prop   
                                       
/- We define our own operators here. \equiv is used to denote
   equivalence/congruence.  \cdot is used for making Segments.-/

local infix ` ≃ `:55 := C
local infix  `⬝`: 56 := Segment.mk


/- # I. Incidence Axioms
   =====================

   I.1 and I.2
   -----------

   Hilbert declares that Line is an independent type and then in
   Axioms I.1 and I.2 he provides a necessary and sufficient condition
   for constructing a Line from two Points.  We believe it is more
   efficient to directly define Line as a structure that requires two
   distint Points. -/

structure Line : Type :=
(p₁ p₂ : Point)
(ne : p₁ ≠ p₂)

/- There are two "lies-on" relations.  We specify lies_on_line here as
   a constant.  lies_on_segment is defined later.-/

constant lies_on_line (p : Point) (l : Line) : Prop

/- I.1, I.2 is implicit in the following axiom. -/
axiom line_exists (p₁ p₂ : Point) (ne : p₁ ≠ p₂) (l : Line) :
     lies_on_line p₁ l ∧ lies_on_line p₂ l ↔ l = ⟨p₁, p₂, ne⟩


-- I.3 (part 1)
-- This axiom is implicit in the definition of Line as a structure.
-- We do not need to formalize this separately.
-- I.3 (part 2)
axiom no_line_on_three_points: ∃ (a b c : Point), ¬ ∃ (l : Line),
  (lies_on_line a l) ∧ (lies_on_line b l) ∧ (lies_on_line c l)

-- A Ray is constructed by specifying two Points.
structure Ray : Type :=
(base ext : Point)

-- For each Ray, we can define a corresponding Line.
def line_of_ray (r : Ray) (ne : r.base ≠ r.ext) : Line :=
  ⟨r.base, r.ext, ne⟩


-- An Angle is constructed by specifying three Points.
-- Angle ⟨a, b, c, _, _⟩ reperesents the angle ∠abc.
structure Angle : Type :=
(ext₁ base ext₂ : Point)


-- For each Angle, we can define two corresponding Rays.
def rays_of_angle (α : Angle) : Ray × Ray :=
  (⟨α.base, α.ext₁⟩, ⟨α.base, α.ext₂⟩)


-- A Triangle is constructed by specifying three Points.
structure Triangle : Type :=
(p₁ p₂ p₃ : Point)


-- For every Triangle, we get three Segments (its sides).
def sides_of_triangle (t : Triangle) : vector Segment 3 :=
  ⟨[t.p₁⬝t.p₂, t.p₂⬝t.p₃, t.p₁⬝t.p₃], rfl⟩

-- For every Triangle, we can define get three Segment Angles.
def angles_of_triangle (t : Triangle) : vector Angle 3 :=
⟨[⟨t.p₂, t.p₁, t.p₃⟩, ⟨t.p₁, t.p₂, t.p₃⟩, ⟨t.p₂, t.p₃, t.p₁⟩], rfl⟩
-- Note that elements of a vector v can be accessed as v.nth 0 etc.
-- Also note that if a vector has lenth n, then asking for element m
-- where m ≥ n returns element (m mod n)


def equilateral (abc : Triangle) : Prop :=
  let sides := sides_of_triangle abc in
  let ab := sides.nth 0 in
  let bc := sides.nth 1 in
  let ac := sides.nth 2 in
  ab ≃ bc ∧ bc ≃ ac

-- # II. Order Axioms
---------------------
def collinear_points (a b c : Point) : Prop :=
  ∃ (l : Line), lies_on_line a l ∧ lies_on_line b l ∧ lies_on_line c l

/- Note:
   ----- I.1 and I.2 guarantee that a Line exists between each pair of
   points, but it does not guarantee that the Lines corresponding to
   ab, ac, and bc are all the same. For that, we need another axiom
   (II.1).  -/

-- II.1 (part 1)
@[symm] axiom B_symm (a b c : Point) : B a b c → B c b a
-- II.1 (part 2)
axiom B_implies_collinear (a b c : Point): B a b c → collinear_points a b c

-- II.2
axiom line_continuity (a c : Point) (ne : a ≠ c):
  let l : Line := ⟨a, c, ne⟩ in
  ∃ (b : Point), lies_on_line b l ∧ B a b c

-- II.3
axiom max_one_between (a b c : Point):
  collinear_points a b c →  xor (B a b c) (xor (B a c b) (B c a b))

-- ## Helpful definitions
-------------------------

-- Lies-on relation between Point and Segment.
def lies_on_segment (x : Point) (s : Segment) (ne : s.p₁ ≠ s.p₂) : Prop :=
  B s.p₁ x s.p₂ ∧ lies_on_line x ⟨s.p₁, s.p₂, ne⟩

-- Criterion for two Segments intersecting at a Point.
def intersect_segment (s₁ s₂ : Segment) (ne1 : s₁.p₁ ≠ s₁.p₂) (ne2 : s₂.p₁ ≠ s₂.p₂) : Prop :=
  ∃ x : Point, lies_on_segment x s₁ ne1 ∧ lies_on_segment x s₂ ne2

-- Criterion for two Lines intersecting at a Point.
def intersect_line (l₁ l₂ : Line) : Prop :=
  ∃ x : Point, lies_on_line x l₁ ∧ lies_on_line x l₂

-- Criterion for a Segment intersecting with a Line.
def intersect_line_segment (l: Line) (s : Segment) (ne : s.p₁ ≠ s.p₂) : Prop :=
  ∃ x : Point, lies_on_line x l ∧ lies_on_segment x s ne

-- Condition for a Segment to be a part of a given Line.
def segment_of_line (s : Segment) (l : Line) : Prop :=
  lies_on_line s.p₁ l ∧ lies_on_line s.p₂ l

-- Condition for two segments to have only one point in common.  We
-- can think of these segments as being end-to-end (forming an angle).
def segments_hinge (s₁ s₂ : Segment) (ne₁ : s₁.p₁ ≠ s₁.p₂) (ne₂ : s₂.p₁ ≠ s₂.p₂) : Prop :=
  ∀ x : Point, lies_on_segment x s₁ ne₁ ∧ lies_on_segment x s₂ ne₂ → x = s₁.p₂ ∧ x = s₂.p₁

-- Dinifinition of parallel Lines.
def parallel_lines (l₁ l₂ : Line) : Prop :=
  ¬∃ (a : Point), lies_on_line a l₁ ∧ lies_on_line a l₂

-- Condition for two Points to lie on the same side of a Line.
def lie_on_same_side (a b : Point) (l : Line) : Prop :=
  decidable.by_cases (λ eq : a = b, true) (λ ne, ¬ intersect_line_segment l (a⬝b) ne)

-- Condition for two Points to lie on opposite sides of a Line.
def lie_on_opposite_sides (a b : Point) (l : Line) : Prop :=
   ¬ lie_on_same_side a b l

-- Define a particular side of a Line (using a Point `marker` to mark
-- our choice of side).
def side_of_line (l : Line) (marker : Point) (x : Point) : Prop :=
  lie_on_same_side x marker l

-- Define a particular side of a Point `p` on a Line `⟨p, marker, ne⟩`
-- (using a Point `marker` to mark our choice of side).
def side_of_point (p marker : Point) (ne : p ≠ marker) : set Point :=
  {x : Point | B p marker x ∨ B p x marker}

-- Interior points of an Angle
def is_in_interior_of_angle (α : Angle) (p : Point) (ne1 : α.base ≠ α.ext₁) (ne2 : α.base ≠ α.ext₂) : Prop :=
    side_of_line ⟨α.base, α.ext₁, ne1⟩ α.ext₂ p
  ∧ side_of_line ⟨α.base, α.ext₂, ne2⟩ α.ext₁ p

-- II.4 Pasch's axiom
-- This can be interpreted as saying "a line that enters a triangle
-- from one side, must leave the triangle from one of the reamining
-- two sides."
axiom pasch (a b c : Point) (l : Line) (ne_ab : a ≠ b) (ne_bc : b ≠ c) (ne_ac : a ≠ c) :
     ¬ collinear_points a b c
  → ¬ lies_on_line a l
  → ¬ lies_on_line b l
  → ¬ lies_on_line c l
  → intersect_line_segment l (a⬝b) ne_ab
  → intersect_line_segment l (a⬝c) ne_ac ∨ intersect_line_segment l (b⬝c) ne_bc

-- # III. Congruence Axioms
---------------------------
-- III.1 Part 1 This says that we can extend a given Segment `a⬝b` in
-- only two ways: one for each side of `p`.
constant segment_copy {a b p marker : Point} : a ≠ b → p ≠ marker → Point

axiom segment_copy' (a b p marker : Point) (ne_a_b : a ≠ b) (ne_p_mark : p ≠ marker) :
  let q : Point :=  segment_copy ne_a_b ne_p_mark in
  let pm : Line := ⟨p, marker, ne_p_mark⟩ in
    lies_on_line q pm ∧ a⬝b ≃ p⬝q

-- III.1 Part 2
@[symm] axiom C_segment_symm (s₁ s₂ : Segment) : s₁ ≃ s₂ → s₂ ≃ s₁
axiom segment_swap (x y : Point) : x⬝y ≃ y⬝x


-- III.2
@[trans] axiom C_segment_trans (u v w x y z : Point) : (u⬝v ≃ z⬝w) → (u⬝v ≃ x⬝y) → z⬝w ≃ x⬝y


-- Congruence of segments is reflexive
@[refl] lemma C_segment_refl (a b : Point) : a⬝b ≃ a⬝b :=
begin
  transitivity,
  repeat {apply segment_swap},
end



-- III.3
axiom C_segment_add_trans (a b c a' b' c' : Point) (l l' : Line)
  (hab : a ≠ b) (hbc : b ≠ c) (ha'b' : a' ≠ b') (hb'c' : b' ≠ c') :
     segment_of_line (a⬝b) l
  → segment_of_line (b⬝c) l
  → segments_end_to_end (a⬝b) (b⬝c) hab hbc
  → segment_of_line (a'⬝b') l'
  → segment_of_line (b'⬝c') l'
  → segments_end_to_end (a'⬝b') (b'⬝c') ha'b' hb'c'
  → a⬝b ≃ a'⬝b'
  → b⬝c ≃ b'⬝c'
  → a⬝c ≃ a'⬝c'


-- III.4
-- This axiom says that a given angle can be copied over to a
-- new location (the point base) in a unique manner (unique as long as we
-- keep track of which side of the line we are on).
constant angle_congruent (α : Angle) (base ext : Point) : Point × Point

axiom angle_congruent' (α : Angle) (base ext : Point) :
  let exts := angle_congruent α base ext in
  let r₁ : Ray := ⟨base, exts.1⟩ in
  let r₂ : Ray := ⟨base, exts.2⟩ in  
    r₁ ≠ r₂
  ∧ α ≃ ⟨r₁.ext, base, ext⟩
  ∧ α ≃ ⟨r₂.ext, base, ext⟩


-- III.5 (wikipedia)
@[trans] axiom C_angle_trans (α β γ : Angle) : α ≃ β → α ≃ γ → β ≃ γ
@[symm] axiom angle_symm (a b c : Point) : (⟨a, b, c⟩ : Angle) ≃ ⟨c, b, a⟩


--- III.5 (from Paper) / III.6 (from wikipedia)
axiom congruent_triangle_SAS (a b c x y z : Point) :
  let abc : Triangle := ⟨a, b, c⟩ in
  let xyz : Triangle := ⟨x, y, z⟩ in
  let ang_abc := angles_of_triangle abc in
  let ang_xyz := angles_of_triangle xyz in
     a⬝b ≃ x⬝y
  → a⬝c ≃ x⬝z
  → ang_abc.nth 0 ≃ ang_xyz.nth 0
  → ang_abc.nth 1 ≃ ang_xyz.nth 1 ∧ ang_abc.nth 2 ≃ ang_xyz.nth 2


-- Definition of Congruent Triangles. All sides must be congruent.
def congruent_triangle (a b c x y z : Point) : Prop :=
    a⬝b ≃ x⬝y
  ∧ b⬝c ≃ y⬝z
  ∧ a⬝c ≃ x⬝z
  ∧ (⟨b, a, c⟩ : Angle) ≃ ⟨y, x, z⟩
  ∧ (⟨a, b, c⟩ : Angle) ≃ ⟨x, y, z⟩
  ∧ (⟨b, c, a⟩ : Angle) ≃ ⟨y, z, x⟩


-- First theorem of congruence for triangles. If, for the two
-- triangles ABC and A′B′C′, the congruences AB≡A′B′, AC≡A′C′, ∠A≡∠A′
-- hold, then the two triangles are congruent to each other.
lemma first_congruence (a b c x y z : Point) :
     a⬝b ≃ x⬝y
  → a⬝c ≃ x⬝z
  → (⟨b, a, c⟩ : Angle) ≃ ⟨y, x, z⟩
  → congruent_triangle a b c x y z :=
begin
  intros,
  unfold congruent_triangle,
  intros,
  have ne_b_c : b ≠ c, sorry,
  have ne_y_z : y ≠ z, sorry,
  set bc : Line := ⟨b, c, ne_b_c⟩,
  set yz : Line := ⟨y, z, ne_y_z⟩,
  have b_on_bc : lies_on_line b bc, sorry,
  have c_on_bc : lies_on_line c bc, sorry,
  have y_on_yz : lies_on_line y yz, sorry,
  
  repeat {split}; try {assumption},
    { by_contradiction,
      have sc' := segment_copy' _ _ _ _ _ b_on_bc c_on_bc y_on_yz,
      simp at sc',
      set sc := segment_copy _ _ _ _ _ b_on_bc c_on_bc y_on_yz,
      rcases sc' with ⟨h₁, h₂, h₃, h₄, h₅⟩,
      set z₁ : Point := sc.1,
      set z₂ : Point := sc.2,
      have SAS := (congruent_triangle_SAS b a c y x z₁ _ h₃ _).1,
      have h₆ : (⟨y, x, z⟩ : Angle) ≃ ⟨y, x, z₁⟩,
        transitivity,
        exact a_3,
        assumption,
      have angle_congruent := angle_congruent,
    sorry},
  have SAS := congruent_triangle_SAS a b c x y z a_1 a_2 a_3,
    { exact SAS.1},
    { exact SAS.2},
end


-- # IV. Parallel Axiom
-----------------------

-- Euclid's parallel postulate. This axioms puts us in a Euclidean geometry
-- and rules out Elliptical/Spherical/Hyperbolic geometry.
constant mk_parallel (p : Point) (l : Line): ¬lies_on_line p l → Line

axiom parallel_postulate (a : Point) (l : Line) (h: ¬lies_on_line a l):
  let l' : Line := mk_parallel a l h in
  parallel_lines l l' ∧ lies_on_line a l'

-- # V. Angles
--------------
-- Two angles having the same vertex and one side in common, whilethe
-- sides not common form a straight line, are called supplementary
-- angles. Two angleshaving a common vertex and whose sides form
-- straight lines are calledvertical angles.  An angle which is
-- congruent to its supplementary angle is called a right angle.

def supplementary_angles (α₁ α₂ : Angle)
  (h₁ : α₁.base ≠ α₁.ext₁) (h₂ : α₂.base ≠ α₂.ext₁) : Prop :=
  α₁.base = α₂.base
  ∧ (⟨α₁.base, α₁.ext₁, h₁⟩ : Line) = ⟨α₂.base, α₂.ext₁, h₂⟩
  ∧ collinear_points α₁.base α₁.ext₂ α₂.ext₂

-- LZ,AD : How to define this rigorously when the point can basically be
-- anywhere?
-- VK : use *segment_copy*.
  
def mk_supplementary_angle (α : Angle) (h: α.base ≠ α.ext₂): Angle :=
 let l : Line := Line.mk α.base α.ext₂ h in
 let bl : lies_on_line α.base l := (line_exists α.base α.ext₂ h).1 in
 let el : lies_on_line α.ext₂ l := (line_exists α.base α.ext₂ h).2 in
 let thing := segment_copy α.base α.ext₂ α.base l l bl el bl in
 let P : Point := thing.1 in
 ⟨α.ext₁, α.base, P⟩

lemma mk_supp_angle_condition (α : Angle) (h : α.base ≠ α.ext₂) :
  (mk_supplementary_angle α h).base ≠ (mk_supplementary_angle α h).ext₁ :=
begin
  unfold mk_supplementary_angle,
  simp,
  sorry
end

lemma mk_supplementary_angle_is_supplementary (α : Angle) (h : α.base ≠ α.ext₁):
  supplementary_angles α (mk_supplementary_angle α) h (mk_supp_angle_condition α) := sorry

-- This specifies a Predicate on the type Angle
def is_right (α : Angle) : Prop := α ≃ mk_supplementary_angle α


structure Circle: Type :=
(center outer : Point)


def radius_segment (c : Circle) : Segment := ⟨c.center, c.outer⟩
def circumference (c : Circle) : set Point := {x : Point | radius_segment c ≃ ⟨c.center, x⟩}


-- # Notion of Distance in Hilbert
----------------------------------
-- may be necessary to properly state and prove pythagorean theorem in
-- Lean).  We start by defining a `measure` on Segments.
def Measure : Type := Segment → ℝ
-- Next, we define some axioms for working with distance.
axiom distance_nonzero (μ : Measure) (s : Segment) :
  s.p₁ ≠ s.p₂ ↔ μ s > 0
axiom distance_congruent (μ : Measure) (s₁ s₂ : Segment) :
  s₁ ≃ s₂ ↔ μ s₁ = μ s₂
axiom distance_between (μ : Measure) (a b c : Point) :
  B a b c → μ (a⬝b) + μ (b⬝c) = μ (a⬝c)


-- Theorems that can be proved in "Foundations of geometry" by Borsuk
-- and Szmielew.
theorem distance_scale (μ₁ μ₂ : Measure) (s : Segment) :
  ∃ k : ℝ, k > 0 ∧ μ₁ s = k * μ₂ s :=
begin
  sorry
end

theorem exists_measure (s : Segment) (x : ℝ) : ∃ (μ : Measure), μ s = x :=
begin
  sorry
end



-- # Continuity Axioms

----------------------

-- Using a combo of the version here and Wikipedia :
-- https://www.math.ust.hk/~mabfchen/Math4221/Hilbert%20Axioms.pdf

axiom Archimedes (s₁ s₂ : Segment) (μ : Measure) :
  ∃ (n : nat) (q : Point), μ (s₁.p₁ ⬝ q) = n * μ s₂ ∧ B s₁.p₁ s₁.p₂ q

-- Continuity axiom 2
---------------------
-- Axiom of Completeness (Vollständigkeit) : To a system of points,
-- straight lines,and planes, it is impossible to add other elements
-- in such a manner that the systemthus generalized shall form a new
-- geometry obeying all of the five groups of axioms.In other words,
-- the elements of geometry form a system which is not susceptible
-- ofextension, if we regard the five groups of axioms as valid.

-- This axiom talks about completeness in a way that we are unsure can
-- be actually implemented.

-- axiom line_completeness (l : Line) (X : set Point) : ¬ ∃ l' : Line,
--   order_preserved X l l' ∧ cong_preserved X l l'
