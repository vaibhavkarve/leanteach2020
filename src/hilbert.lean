-- Hilbert's Axioms Formalized
import data.real.basic tactic
noncomputable theory
open_locale classical

-- Two undefined types
constant Point : Type
-- constant Line : Type -- We difine it as a structure instead of a constant.
--constant Plane : Type -- We restrict our attention to planar geometry, ignoring solid geometry.

-- a Segment is constructed by specifying two points.
structure Segment: Type := (p₁ p₂ : Point)  -- the  subscripts are written as \ 1 and \ 2.

-- This is the Betweenness relation.
-- It says "y" is in between "x" and "z".
constant B (x y z : Point) : Prop

-- Polymorphism => make it work for multiple types at the same time
-- For every type A, there is a congruence relation C.
constant C {A : Type} : A → A → Prop   -- Here, "A" is an implicit argument. Lean figures it out.
                                       -- In other languages this is called overloading.

-- We are defining our own operators here
local infix ` ≃ `:55 := C           -- \ equiv == equivalence/congruence
local infix  `⬝`: 56  := Segment.mk  -- \ cdot == center-dot


-- # I. Incidence Axioms
------------------------
-- I.1 and I.2

-- Hilbert declares that Line is an independent type and then in
-- Axioms I.1 and I.2 he provides a necessary and sufficient condition
-- for constructing a Line from two Points.  We believe it is more
-- efficient to directly define Line as a structure that requires two
-- distint Points.
structure Line : Type :=
(p₁ p₂ : Point)
(ne : p₁ ≠ p₂)

-- There are two "lies-on" relations.
-- We specify lies_on_line here as a constant.
-- lies_on_segment is defined later.
constant lies_on_line (x : Point) (y : Line) : Prop


-- I.1, I.2 is implicit in constant
axiom line_exists (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
  let l : Line := ⟨p₁, p₂, h⟩ in
  lies_on_line p₁ l ∧ lies_on_line p₂ l

axiom line_unique (p₁ p₂ : Point) (h : p₁ ≠ p₂) (l : Line) :
     lies_on_line p₁ l
  → lies_on_line p₂ l
  → l = ⟨p₁, p₂, h⟩


-- I.3 (part 1)
axiom two_points_on_line (l : Line):
  ∃ (a b : Point), a ≠ b ∧ lies_on_line a l ∧ lies_on_line b l
-- I.3 (part 2)
axiom no_line_on_three_points:
  ∃ (a b c : Point), ¬∃ (l : Line), (lies_on_line a l) ∧ (lies_on_line b l) ∧ (lies_on_line c l)


-- A Ray is constructed by specifying two Points.
structure Ray : Type :=
(base ext : Point)

-- For each Ray, we can define a corresponding Line.
def line_of_ray (r : Ray) : r.base ≠ r.ext → Line :=
  Line.mk r.base r.ext


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


-- For every Triangle, we can define get three Segments (its sides).
def sides_of_triangle (t : Triangle) : vector Segment 3 :=
  ⟨[t.p₁⬝t.p₂, t.p₂⬝t.p₃, t.p₁⬝t.p₃], rfl⟩
-- For every Triangle, we can define get three Segment Angles.
def angles_of_triangle (t : Triangle) : vector Angle 3 :=
⟨[⟨t.p₂, t.p₁, t.p₃⟩, ⟨t.p₁, t.p₂, t.p₃⟩, ⟨t.p₂, t.p₃, t.p₁⟩], rfl⟩
-- Note that elements of a vector v can be accessed as v.nth 0 etc.
-- Also note that if a vector has lenth n, then asking for element m
-- where m ≥ n returns element (m mod n)


def equilateral (t: Triangle) : Prop :=
  let sides := sides_of_triangle t in
  sides.nth 0 ≃ sides.nth 1 ∧ sides.nth 1 ≃ sides.nth 2

-- # II. Order Axioms (Good)
---------------------
def collinear_points (a b c : Point) : Prop :=
  ∃ (l : Line), lies_on_line a l ∧ lies_on_line b l ∧ lies_on_line c l

/- Note:
   -----
   I.1 and I.2 guarantee that a Line exists between each pair of points,
   but it does not guarantee that the Lines corresponding to ab, ac, and bc are all
   the same. For that, we need another axiom (II.1).
-/

-- II.1 (part 1)
@[symm] axiom B_symm (a b c : Point) : B a b c → B c b a
-- II.1 (part 2)
axiom B_implies_collinear (a b c : Point): B a b c → collinear_points a b c

-- II.2
axiom line_continuity (a c : Point) (h : a ≠ c):
  let l : Line := ⟨a, c, h⟩ in
  ∃ (b : Point), lies_on_line b l ∧ B a b c

-- II.3
axiom max_one_between (a b c : Point):
  collinear_points a b c →  xor (B a b c) (xor (B a c b) (B c a b))

-- ## Helpful definitions
-------------------------
-- Lies-on relation between Point and Segment.
def lies_on_segment (x : Point) (s : Segment) (h : s.p₁ ≠ s.p₂) : Prop :=
  B s.p₁ x s.p₂ ∧ lies_on_line x ⟨s.p₁, s.p₂, h⟩
-- Criterion for two Segments intersecting at a Point.
def intersect_segment (s₁ s₂ : Segment) (h1 : s₁.p₁ ≠ s₁.p₂) (h2 : s₂.p₁ ≠ s₂.p₂) : Prop :=
  ∃ x : Point, lies_on_segment x s₁ h1 ∧ lies_on_segment x s₂ h2
-- Criterion for two Lines intersecting at a Point.
def intersect_line (l₁ l₂ : Line) : Prop :=
  ∃ x : Point, lies_on_line x l₁ ∧ lies_on_line x l₂
-- Criterion for a Segment intersecting with a Line.
def intersect_line_segment (l: Line) (s : Segment) (H : s.p₁ ≠ s.p₂) : Prop :=
  ∃ x : Point, lies_on_line x l ∧ lies_on_segment x s H
-- Condition for a Segment to be a part of a given Line.
def segment_of_line (s : Segment) (l : Line) : Prop :=
  lies_on_line s.p₁ l ∧ lies_on_line s.p₂ l
-- Condition for two segments being on the same line end-to-end.
def segments_end_to_end (s₁ s₂ : Segment) (h₁ : s₁.p₁ ≠ s₁.p₂) (h₂ : s₂.p₁ ≠ s₂.p₂) : Prop :=
  (s₁.p₂ = s₂.p₁) ∧ (∀ x : Point, lies_on_segment x s₁ h₁ ∧ lies_on_segment x s₂ h₂ → x = s₁.p₂)
-- Relationship between two parallel lines
def parallel_lines (l₁ l₂ : Line) : Prop :=
  ¬∃ (a : Point), lies_on_line a l₁ ∧ lies_on_line a l₂

-- II.4 Pasch's axiom
-- This can be interpreted as saying "a line that enters a triangle
-- from one side, must leave the triangle from one of the reamining
-- two sides."
axiom pasch (a b c: Point) (l : Line) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c):
  (¬collinear_points a b c)
  → ¬(lies_on_line a l)
  → ¬(lies_on_line b l)
  → ¬(lies_on_line c l)
  → intersect_line_segment l (a⬝b) hab
  → intersect_line_segment l (a⬝c) hac ∨ intersect_line_segment l (b⬝c) hbc

-- # III. Congruence Axioms
---------------------------
-- III.1 Part 1
-- This says that we can extend a given Segment in only two ways --
-- one for each side of l.
constant segment_copy (a b a' : Point) (l l' : Line) :
    lies_on_line a l
  → lies_on_line b l
  → lies_on_line a' l'
  → Point × Point

axiom segment_copy' (a b a' : Point) (l l' : Line)
  (hal : lies_on_line a l) (hbl: lies_on_line b l) (ha'l' : lies_on_line a' l') :
  let points :=  segment_copy a b a' l l' hal hbl ha'l' in
  let x : Point := points.1 in
  let y : Point := points.2 in
      x ≠ y
    ∧ lies_on_line x l'
    ∧ a⬝b ≃ a'⬝x
    ∧ lies_on_line y l'
    ∧ a⬝b ≃ a'⬝y


-- III.1 Part 2
@[symm] axiom C_segment_symm (s₁ s₂ : Segment) : s₁ ≃ s₂ → s₂ ≃ s₁
@[symm] axiom C_segment_swap (x y : Point) : x⬝y ≃ y⬝x

-- III.2
@[trans] axiom C_segment_trans (u v w x y z : Point) : (u⬝v ≃ z⬝w) → (u⬝v ≃ x⬝y) → z⬝w ≃ x⬝y

-- Congruence of segments is reflexive
@[refl] lemma C_segment_refl (a b : Point) : a⬝b ≃ a⬝b :=
begin
  fapply C_segment_trans,
    use b,
    use a,
      symmetry,
      symmetry,
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
-- new location (the point o) in a unique manner (unique as long as we
-- keep track of which side of the line we are on).
axiom angle_congruent (α : Angle) (o : Point) (r : Ray) (h : r.base = o) :
  ∃! (r₁ r₂ : Ray), r₁ ≠ r₂
                    ∧ r₁.base = o
                    ∧ r₂.base = o
                    ∧ α ≃ ⟨r.ext, o, r₁.ext⟩
                    ∧ α ≃ ⟨r.ext, o, r₂.ext⟩


-- Definition of Congruent Triangles. All sides must be congruent.
def congruent_triangle (t₁ t₂ : Triangle) : Prop :=
  let sides1 := sides_of_triangle t₁ in
  let sides2 := sides_of_triangle t₂ in
  sides1.nth 0 ≃ sides2.nth 0
  ∧ sides1.nth 1 ≃ sides2.nth 1
  ∧ sides1.nth 2 ≃ sides2.nth 2

-- TODO: Maybe this should be a Theorem?
-- Corresponding angles in congruent triangles must be congruent
-- ∧ t₁.α₁ ≃ t₂.α₁
-- ∧ t₁.α₂ ≃ t₂.α₂
-- ∧ t₁.α₃ ≃ t₂.α₃


--- III.5 (from Paper) / III.6 (from wikipedia)
axiom congruent_triangle_SAS (a b c a' b' c' : Point) :
    a⬝b ≃ a'⬝b'
  → a⬝c ≃ a'⬝c'
  → (⟨b, a, c⟩ : Angle) ≃ ⟨b', a', c'⟩
  → (⟨a, b, c⟩ : Angle) ≃ ⟨a', b', c'⟩


-- III.5 (wikipedia)
axiom C_angle_trans (α β γ : Angle) : α ≃ β → α ≃ γ → β ≃ γ

-- TODO : Not sure if the following is an axiom or a lemma?
axiom angle_symm (a b c : Point) : (⟨a, b, c⟩ : Angle) ≃ ⟨c, b, a⟩



-- # IV. Parallel Axiom
-----------------------

-- Euclid's parallel postulate. This axioms puts us in a Euclidean geometry
-- and rules out Elliptical/Spherical/Hyperbolic geometry.

-- Idk if this works lmao
constant p_line (p : Point) (l: Line): ¬ lies_on_line p l → Line

axiom parallel_postulate (a : Point) (l : Line) (h: ¬lies_on_line a l): let l' : Line := p_line a l h in parallel_lines l l' ∧ lies_on_line a l'

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

def mk_supplementary_angle (α : Angle) : Angle := ⟨α.ext₁, α.base, sorry⟩

lemma mk_supp_angle_condition (α : Angle):
 (mk_supplementary_angle α).base ≠ (mk_supplementary_angle α).ext₁ := sorry

lemma mk_supplementary_angle_is_supplementary (α : Angle) (h : α.base ≠ α.ext₁):
  supplementary_angles α (mk_supplementary_angle α) h (mk_supp_angle_condition α) := sorry

-- This specifies a Predicate on the type Angle
def is_right (α : Angle) : Prop := α ≃ mk_supplementary_angle α

-- A : Type
-- A → Prop      -- this is a predicate
-- A → A → Prop  -- this a relation


structure Circle: Type :=
(center outer : Point)

def radius_segment (c : Circle) : Segment := ⟨c.center, c.outer⟩
def circumference (c : Circle) : set Point := {x : Point | radius_segment c ≃ ⟨c.center, x⟩}


axiom segment_construct (x y z a b : Point) :
  ∃ z : Point, (B x y z) ∧ (y⬝z ≃ a⬝b)


-- # Notion of Distance in Hilbert
----------------------------------
-- may be necessary to properly state and prove pythagorean theorem in
-- Lean).  We start by defining a `measure` on Segments.
def Measure : Type := Segment → ℝ
-- Next, we define some axioms for working with distance.
axiom distance_nonzero (μ : Measure) (s : Segment) :
  s.p₁ ≠ s.p₂ → μ s > 0
axiom distance_congruent (μ : Measure) (s₁ s₂ : Segment) :
  s₁ ≃ s₂ → μ s₁ ≃ μ s₂
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


constant θ : Angle → ℝ
-- Next we define some axioms to work with angles.
axiom equalAngles (α₁ α₂ : Angle) : θ α₁ = θ α₂ ↔ α₁ ≃ α₂

def is_right_2 (α : Angle) : Prop := θ α = 90


-- VK : I am not sure what you are trying to say here.

