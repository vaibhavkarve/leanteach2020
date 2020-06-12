import .hilbert
import tactic

noncomputable theory
open_locale classical

local infix ` ≃ `:55 := C        -- \ equiv == equivalence/congruence
local infix `⬝`:56   := Segment.mk  -- \ cdot == center-dot


--------------------
-- |#Instructions# |
--------------------
/-
0. Read these instructions carefully.
1. I have tried my best to translate statements of the propositions into Lean.
2. In place of proofs, I have placed sorry's.
3. Do NOT add your proofs to this file. Create a new file called
   euclid_props.lean (and hilbert_props.lean) on CoCalc. Copy the statements there
   and add your proofs to it.
4. The Euclid group can change the import in the first line to read
   "import euclid" instead.
5. You might have to make minor changes to the statement to make it copatible with
   your syntax.  Don't make too many changes though.
6. If you do make a change to the statement, then don't forget to add a note
   in your hilbert_props.lean file.
7. I am also mentioning missing definitions in this file. You need to define these
   in your hilbert.lean / euclid.lean source file so that the propositions given
   here make sense.
8. If you spot some obvious mistakes in the statement of the propositions given
   below then let me know.  You can also ask me for clarifications.
9. This is still an incomplete list and I will keep adding more propositions in
   this file.

-- VK
-/





--------------------
-- |#Propositions# |
--------------------

-- Proposition 1.  To construct an equilateral triangle on a given
-- finite straight line.
theorem prop1 (s : Segment) :
  ∃ t : Triangle, t.p₁ = s.p₁ ∧ t.p₂ = s.p₂ ∧ equilateral t := sorry

-- Proposition 2.  To place a straight line equal to a given straight
-- line with one end at a given point.
theorem prop2 (s : Segment) :
  ∃ s' : Segment, s ≃ s' ∧ s'.p₁ = s.p₂ := sorry

-- Proposition 3.  To cut off from the greater of two given unequal
-- straight lines a straight line equal to the less.
-- Assume s₂ < s₁
theorem prop3 (s₁ s₂ : Segment) (h : s₁.p₁ ≠ s₁.p₂):
  ∃ x : Point, lies_on_segment x s₁ h ∧ s₁.p₁⬝x ≃ s₂ := sorry


-- Proposition 4.  If two triangles have two sides equal to two sides
-- respectively, and have the angles contained by the equal straight
-- lines equal, then they also have the base equal to the base, the
-- triangle equals the triangle, and the remaining angles equal the
-- remaining angles respectively, namely those opposite the equal
-- sides.
theorem prop4 (t₁ t₂ : Triangle) :
  t₁.s₁₂ ≃ t₂.s₁₂
  → t₁.s₁₃ ≃ t₂.s₁₃
  → t₁.α₁ ≃ t₂.α₁
  → congruent_triangle t₁ t₂ := sorry


-- Proposition 5.  In isosceles triangles the angles at the base equal
-- one another, and, if the equal straight lines are produced further,
-- then the angles under the base equal one another.
theorem prop5 (t : Triangle) :
  t.s₁₂ ≃ t.s₁₃ → t.α₂ ≃ t.α₃ :=  sorry


-- Proposition 6.  If in a triangle two angles equal one another, then
-- the sides opposite the equal angles also equal one another.
theorem prop6 (t : Triangle) :
  t.α₁ ≃ t.α₂ → t.s₂₃ ≃ t.s₁₃ := sorry


-- Proposition 7.  Given two straight lines constructed from the ends
-- of a straight line and meeting in a point, there cannot be
-- constructed from the ends of the same straight line, and on the
-- same side of it, two other straight lines meeting in another point
-- and equal to the former two respectively, namely each equal to that
-- from the same end.
theorem prop7 (t₁ t₂ : Triangle) :
  t₁.s₁₂ = t₂.s₁₂  -- note that this says equal, not congruent.
  → t₁.s₁₃ ≃ t₂.s₁₃
  → t₁.s₂₃ ≃ t₂.s₂₃
  → t₁.p₃ = t₂.p₃ := sorry


-- Proposition 8.  If two triangles have the two sides equal to two
-- sides respectively, and also have the base equal to the base, then
-- they also have the angles equal which are contained by the equal
-- straight lines.
theorem prop8 (t₁ t₂ : Triangle) :
  t₁.s₁₂ ≃ t₂.s₁₂
  → t₁.s₁₃ ≃ t₂.s₁₃
  → t₁.s₂₃ ≃ t₁.s₂₃
  


-- Proposition 9.
--     To bisect a given rectilinear angle.

-- Proposition 10.
--     To bisect a given finite straight line.

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
    If two triangles have two angles equal to two angles respectively, and one side equal to one side, namely, either the side adjoining the equal angles, or that opposite one of the equal angles, then the remaining sides equal the remaining sides and the remaining angle equals the remaining angle.

Proposition 27.
    If a straight line falling on two straight lines makes the alternate angles equal to one another, then the straight lines are parallel to one another.

Proposition 28.
    If a straight line falling on two straight lines makes the exterior angle equal to the interior and opposite angle on the same side, or the sum of the interior angles on the same side equal to two right angles, then the straight lines are parallel to one another.

Proposition 29.
    A straight line falling on parallel straight lines makes the alternate angles equal to one another, the exterior angle equal to the interior and opposite angle, and the sum of the interior angles on the same side equal to two right angles.

Proposition 30.
    Straight lines parallel to the same straight line are also parallel to one another.

Proposition 31.
    To draw a straight line through a given point parallel to a given straight line.

Proposition 32.
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
