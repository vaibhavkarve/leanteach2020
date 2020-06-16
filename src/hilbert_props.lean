import tactic
import .hilbert

noncomputable theory
open_locale classical

local infix ` ≃ `:55 := C        -- \ equiv == equivalence/congruence
local infix `⬝`:56   := Segment.mk  -- \ cdot == center-dot

-------------------------------
-- |#Instructions For Hilbert# |
-------------------------------

-- Alex: I copied the instructions from the propositions.lean document
-- and deleted the ones that didn't pertain to the Hilbert group

/-
0. Read these instructions carefully.
1. I have tried my best to translate statements of the propositions into Lean.
2. In place of proofs, I have placed sorry's.
3. Do NOT add your proofs to this file. Create a new file called
   euclid_props.lean (and hilbert_props.lean) on CoCalc. Copy the statements there
   and add your proofs to it.
4. You might have to make minor changes to the statement to make it compatible with
   your syntax.  Don't make too many changes though.
5. If you do make a change to the statement, then don't forget to add a note
   in your hilbert_props.lean file.
6. I am also mentioning missing definitions in this file. You need to define these
   in your hilbert.lean / euclid.lean source file so that the propositions given
   here make sense.
7. If you spot some obvious mistakes in the statement of the propositions given
   below then let me know.  You can also ask me for clarifications.
8. This is still an incomplete list and I will keep adding more propositions in
   this file.

-- VK
-/


-- If two distinct lines intersect, then they do so in exactly one point.
lemma single_intersection (l₁ l₂ : Line) :
     l₁ ≠ l₂
  → intersect_line l₁ l₂
  → ∃! x : Point, lies_on_line x l₁ ∧ lies_on_line x l₂ :=
begin
  intros h₁ h₂,
  rw intersect_line at h₂,
  choose x h₂ using h₂,
  use x,
  tidy,
  symmetry,
  by_contradiction,
  have line_exists := line_exists x y a_2,
    tidy,
  have h₃ : l₁ = ⟨x, y, a_2⟩,
    { apply line_unique, assumption, assumption},
  have h₄ : l₂ = ⟨x, y, a_2⟩,
    { apply line_unique, assumption, assumption},
  cc,
end


-- Through any point there exists at least two lines.
lemma two_lines (p : Point) : ∃ l₁ l₂ : Line,
  l₁ ≠ l₂ ∧ lies_on_line p l₁ ∧ lies_on_line p l₂ :=
begin
  choose a b c h using no_line_on_three_points,
  by_cases ha : p ≠ a,
  by_cases hb : p ≠ b,
  by_cases hc : p ≠ c,
  set la : Line := ⟨p, a, ha⟩,
  set lb : Line := ⟨p, b, hb⟩,
  set lc : Line := ⟨p, c, hc⟩,
  by_cases hab : la ≠ lb,
  use la,
  use lb,
  have le := line_exists p a ha,
  split,
    assumption,
    split,
      exact le.1,
  have le := line_exists p b hb,
  exact le.1,
  simp at hab,
  by_cases hbc : lb ≠ lc,
  
  repeat {sorry},
end


-- # Euclid's Proposition 1
---------------------------
-- To construct an equilateral triangle on a given
-- finite straight line.
theorem prop1 (s : Segment) :
  ∃ t : Triangle, t.p₁ = s.p₁ ∧ t.p₂ = s.p₂ ∧ equilateral t :=
begin
    let a : Point := s.p₁,
    let b : Point := s.p₂,
    -- let c : Point := s.p₁ ⬝ c ≃ s.p₂ ⬝ c,
    -- ,
    sorry,
end

-- # Euclid's Proposition 2
---------------------------
-- To place a straight line equal to a given straight
-- line with one end at a given point.
theorem prop2 (s : Segment) (h : s.p₁ ≠ s.p₂):
  ∃ s' : Segment, s ≃ s' ∧ s'.p₁ = s.p₁ :=
begin
    sorry,
    --let l : Line := line_of_points s.p₁ s.p₂ h,
    --let y : Line := lies_on_line s.p₁ y,
    --fapply segment_copy' s.p₁ s.p₂ l s.p₁ y,
end


-- Proposition 3.  To cut off from the greater of two given unequal
-- straight lines a straight line equal to the less.
-- Assume s₂ < s₁
--theorem prop3 (s₁ s₂ : Segment) (h : s₁.p1 ≠ s₁.p2):
--  ∃ x : Point, lies_on_segment x s₁ h ∧ s₁.p1⬝x ≃ s₂ := sorry


-- Proposition 4.  If two triangles have two sides equal to two sides
-- respectively, and have the angles contained by the equal straight
-- lines equal, then they also have the base equal to the base, the
-- triangle equals the triangle, and the remaining angles equal the
-- remaining angles respectively, namely those opposite the equal
-- sides.

--theorem prop4 (t₁ t₂ : Triangle) :
--  t₁.a⬝t₁.b ≃ t₂.a⬝t₂.b
--  → t₁.a⬝t₁.c ≃ t₂.a⬝t₂.c
--  → (Angle.mk t₁.a {Ray . base:=t₁.a, extension:=t₁.b} {Ray . base:=t₁.a, extension:=t₁.b} rfl rfl) ≃ Angle.mk t₁.a {Ray . base:=t₁.a, extension:=t₁.b} {Ray . base:=t₁.a, extension:=t₁.b} rfl rfl
--  → congruent_triangles t₁ t₂
--  := sorry


-- Proposition 5.  In isosceles triangles the angles at the base equal
-- one another, and, if the equal straight lines are produced further,
-- then the angles under the base equal one another.
theorem prop5_part1 (t : Triangle) :
  let sides := sides_of_triangle t in
  let angles := angles_of_triangle t in
  side1_of_triangle t ≃ side2_of_triangle t
  → angle1_of_triangle t ≃ angle3_of_triangle t :=
-- If t := abc
-- ab = bc
-- bac ≃ acb
-- angles.nth 1 ↔ bac ∈ angles
begin
  set a := t.p₁,
  set b := t.p₂,
  set c := t.p₃,
  intros sides angles h,
  have h' := congruent_triangle_SAS b a c b c a,
  unfold angle1_of_triangle angle3_of_triangle,
  unfold side1_of_triangle side2_of_triangle at h,
  set a := t.p₁,
  set b := t.p₂,
  set c := t.p₃,
  apply h',
    { have x : b⬝a ≃ a⬝b, symmetry,
      transitivity, symmetry, assumption},
    { transitivity, exact h, symmetry},
    { apply angle_symm}
end


-- Proposition 6.
--     If in a triangle two angles equal one another, then the sides opposite the equal angles also equal one another.


#exit
theorem prop_6 (t : Triangle): (angles_of_triangle t).1 ≃ (angles_of_triangle t).2.1 → (sides_of_triangle t).2.1 ≃ (sides_of_triangle t).2.2

-- Proposition 7.
-- --     Given two straight lines constructed from the ends of a straight line and meeting in a point, there cannot be constructed from the ends of the same straight line, and on the same side of it, two other straight lines meeting in another point and equal to the former two respectively, namely each equal to that from the same end.

-- Proposition 8.
--     If two triangles have the two sides equal to two sides respectively, and also have the base equal to the base, then they also have the angles equal which are contained by the equal straight lines.


-- Proposition 9.
--     To bisect a given rectilinear angle.

theorem prop_9 (a : Angle): ∃ (p : Point), Angle.mk a.ext₁ a.base p ≃ Angle.mk p a.base a.ext₂

-- Proposition 10.
--     To bisect a given finite straight line.

theorem prop_10 (s : Segment) : ∃ (p : Point), B s.p₁ p s.p₂ ∧ p₁⬝p ≃ p⬝p₂

-- Proposition 11.
--     To draw a straight line at right angles to a given straight line from a given point on it.

-- Proposition 12.
--     To draw a straight line perpendicular to a given infinite straight line from a given point not on it.

-- Proposition 13.
--     If a straight line stands on a straight line, then it makes either two right angles or angles whose sum equals two right angles.

-- Proposition 14.
--     If with any straight line, and at a point on it, two straight lines not lying on the same side make the sum of the adjacent angles equal to two right angles, then the two straight lines are in a straight line with one another.

-- Proposition 15.
--     If two straight lines cut one another, then they make the vertical angles equal to one another.

--     Corollary. If two straight lines cut one another, then they will make the angles at the point of section equal to four right angles.
-- 
/-
Proposition 16.
    In any triangle, if one of the sides is produced, then the exterior angle is greater than either of the interior and opposite angles.

Proposition 17.
    In any triangle the sum of any two angles is less than two right angles.

Proposition 18.
    In any triangle the angle opposite the greater side is greater.

Proposition 19.
    In any triangle the side opposite the greater angle is greater.

Proposition 20.
    In any triangle the sum of any two sides is greater than the remaining one.

Proposition 21.
    If from the ends of one of the sides of a triangle two straight lines are constructed meeting within the triangle, then the sum of the straight lines so constructed is less than the sum of the remaining two sides of the triangle, but the constructed straight lines contain a greater angle than the angle contained by the remaining two sides.

Proposition 22.
    To construct a triangle out of three straight lines which equal three given straight lines: thus it is necessary that the sum of any two of the straight lines should be greater than the remaining one.

Proposition 23.
    To construct a rectilinear angle equal to a given rectilinear angle on a given straight line and at a point on it.

Proposition 24.
    If two triangles have two sides equal to two sides respectively, but have one of the angles contained by the equal straight lines greater than the other, then they also have the base greater than the base.

Proposition 25.
    If two triangles have two sides equal to two sides respectively, but have the base greater than the base, then they also have the one of the angles contained by the equal straight lines greater than the other.


Proposition 26.
    If two triangles have two angles equal to two angles respectively, and one side equal to one side, namely, either the side adjoining the equal angles, or that opposite one of the equal angles, then the remaining sides equal the remaining sides and the remaining angle equals the remaining angle. -/

theorem prop26_part1 (t₁ t₂ : Triangle): t₁.α₁ ≃ t₂.α₁ → t₁.α₂ ≃ t₂.α₂ → t₁.s₁₂ ≃ t₂.s₁₂ → congruent t₁ t₂ :=
begin
    let G : Point :=
    sorry
end


/-
Proposition 27.
    If a straight line falling on two straight lines makes the alternate angles equal to one another, then the straight lines are parallel to one another.

Proposition 28.
    If a straight line falling on two straight lines makes the exterior angle equal to the interior and opposite angle on the same side, or the sum of the interior angles on the same side equal to two right angles, then the straight lines are parallel to one another.

Proposition 29.
    A straight line falling on parallel straight lines makes the alternate angles equal to one another, the exterior angle equal to the interior and opposite angle, and the sum of the interior angles on the same side equal to two right angles.

Proposition 30.
    Straight lines parallel to the same straight line are also parallel to one another. -/

theorem prop30 (l₁ l₂ l₃ : Line): parallel_lines l₁ l₂ → parallel_lines l₁ l₃ → parallel_lines l₂ l₃

/-Proposition 31.
    To draw a straight line through a given point parallel to a given straight line. -/

theorem prop31 (l : Line) (p: Point) (h: ¬lies_on_line p l): ∃ (l' : Line), lies_on_line p l' ∧ parallel_lines l l' :=
begin
    /-split,
    split,
    let l' := Line,
    use l',
    choose l' using parallel_postulate,-/
    
    sorry,
end


/-Proposition 32.
    In any triangle, if one of the sides is produced, then the exterior angle equals the sum of the two interior and opposite angles, and the sum of the three interior angles of the triangle equals two right angles.

Proposition 33.
    Straight lines which join the ends of equal and parallel straight lines in the same directions are themselves equal and parallel.

Proposition 34.
    In parallelogrammic areas the opposite sides and angles equal one another, and the diameter bisects the areas.

Proposition 35.
    Parallelograms which are on the same base and in the same parallels equal one another.

Proposition 36.
    Parallelograms which are on equal bases and in the same parallels equal one another.

Proposition 37.
    Triangles which are on the same base and in the same parallels equal one another.

Proposition 38.
    Triangles which are on equal bases and in the same parallels equal one another.

Proposition 39.
    Equal triangles which are on the same base and on the same side are also in the same parallels.

Proposition 40.
    Equal triangles which are on equal bases and on the same side are also in the same parallels.

Proposition 41.
    If a parallelogram has the same base with a triangle and is in the same parallels, then the parallelogram is double the triangle.

Proposition 42.
    To construct a parallelogram equal to a given triangle in a given rectilinear angle.

Proposition 43.
    In any parallelogram the complements of the parallelograms about the diameter equal one another.

Proposition 44.
    To a given straight line in a given rectilinear angle, to apply a parallelogram equal to a given triangle.

Proposition 45.
    To construct a parallelogram equal to a given rectilinear figure in a given rectilinear angle.

Proposition 46.
    To describe a square on a given straight line.

Proposition 47.
    In right-angled triangles the square on the side opposite the right angle equals the sum of the squares on the sides containing the right angle.

Proposition 48.
    If in a triangle the square on one of the sides equals the sum of the squares on the remaining two sides of the triangle, then the angle contained by the remaining two sides of the triangle is right. 
-/
