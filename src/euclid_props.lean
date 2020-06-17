import .euclid
import tactic


-- Redo the local notation
--------------------------
local infix ` ≃ `:55 := congruent  -- typed as \ equiv
local infix `⬝`:56 := Segment.mk  -- typed as \ cdot


-- Lemma needed for Proposition 1
lemma hypothesis1_about_circles_radius (s : Segment) :
  let c₁ : Circle := ⟨s.p1, s.p2⟩ in
  let c₂ : Circle := ⟨s.p2, s.p1⟩ in
  radius c₁ + radius c₂ >= distance c₁.center c₂.center :=
begin
  intros,
  show distance s.p1 s.p2 ≤ radius c₁ + radius c₂,
    calc distance s.p1 s.p2 ≤ distance s.p1 s.p2 + distance s.p1 s.p2
                                              : by {simp, apply distance_not_neg}
         ... = radius c₁ + distance s.p1 s.p2 : by refl
         ... = radius c₁ + distance s.p2 s.p1 : by simp
         ... = radius c₁ + radius c₂ : by refl,
end


-- Another lemma needed for Proposition 1
lemma hypothesis2_about_circles_radius (s : Segment) :
  let c₁ : Circle := ⟨s.p1, s.p2⟩ in
  let c₂ : Circle := ⟨s.p2, s.p1⟩ in
  abs (radius c₁ - radius c₂) <= distance c₁.center c₂.center :=
  begin
    intros,
    show abs (radius c₁ - radius c₂) ≤ distance s.p1 s.p2,
    calc abs (radius c₁ - radius c₂) = abs (distance s.p1 s.p2 - radius c₂) : by refl
         ... = abs (distance s.p1 s.p2 - distance s.p2 s.p1) : by refl
         ... = abs (distance s.p1 s.p2 - distance s.p1 s.p2) : by simp
         ... = 0 : by simp
         ... ≤ distance s.p1 s.p2 : by apply distance_not_neg,
  end


-- # Proposition 1
------------------
lemma construct_equilateral (s : Segment) : ∃ (tri: Triangle),
  s.p1 = tri.p1 ∧ s.p2 = tri.p2 ∧ is_equilateral tri :=
begin
  set c₁ : Circle := ⟨s.p1, s.p2⟩,
  set c₂ : Circle := ⟨s.p2, s.p1⟩,
  have h₁ := (hypothesis1_about_circles_radius s),
  have h₂ := hypothesis2_about_circles_radius s,
  set p : Point := circles_intersect c₁ c₂ h₁ h₂,
  have hp₁ : p ∈ circumference c₁, from (circles_intersect' c₁ c₂ h₁ h₂).1,
  have hp₂ : p ∈ circumference c₂, from (circles_intersect' c₁ c₂ h₁ h₂).2,
  use ⟨s.p1, s.p2, p⟩,
  --- Cleaning up the context ---
    tidy;
    unfold circumference radius_segment at hp₁ hp₂;
    unfold sides_of_triangle;
    dsimp * at *,
  --- Cleaning done ---
    {calc s.p1 ⬝ s.p2 ≃ s.p2 ⬝ s.p1 : by symmetry
                  ... ≃ s.p2 ⬝ p    : by assumption},
    {calc s.p2 ⬝ p ≃ s.p2 ⬝ s.p1 : by {apply cong_symm, assumption}
               ... ≃ s.p1 ⬝ s.p2 : by apply segment_symm
               ... ≃ s.p1 ⬝ p    : by assumption
               ... ≃    p ⬝ s.p1 : by symmetry},
end



lemma ray_cut_length (r : Ray) (s : Segment) (h : r.base ≠ r.ext)
  : ∃ p : Point, p ∈ points_of_ray r h ∧ r.base ⬝ p ≃ s :=
begin
  sorry
end



-- lemma ray_circle_intersect (AB : Ray) (ne : AB.base ≠ AB.ext) (C : Circle) (center : C.center = AB.base): 
-- ∃ (p : Point), (p ∈ circumference C) ∧ (p ∈ points_of_ray AB ne) :=
-- begin
-- have h := extend (Segment.mk AB.base AB.ext Segment.mk AB.ext ) CD? ne,
-- end
-- Lemma needed for proposition 2
lemma ray_circle_intersect (AB : Ray) (ne : AB.base ≠ AB.ext) (C : Circle) (p : Point) :
  circle_interior p C
  → p ∈ points_of_ray AB ne
  → ∃ x : Point, x ∈ points_of_ray AB ne ∧ x ∈ circumference C :=
begin
  sorry,
end



--Proposition 2
lemma placeline (bc : Segment) (a : Point) :
     a ≠ bc.p1
  → bc.p1 ≠ bc.p2
  → ∃ (s : Segment), (bc.p1 = s.p1) ∧ bc ≃ s :=
begin
  intros ne_a_b ne_b_c,
  let ab : Segment := a⬝bc.p1,
  have construct_equilateral := construct_equilateral ab,
  choose abd h using construct_equilateral,
  rcases h with ⟨h₁, h₂, h₃⟩,
  let da : Ray := ⟨abd.p3, a⟩,
  let db : Ray := ⟨abd.p3, ab.p2⟩,
  let circ : Circle := ⟨bc.p1, bc.p2⟩,
  have ne_d_b : db.base ≠ db.ext,
    { simp,
      unfold is_equilateral at h₃,
      dsimp at h₃,
      rcases h₃ with ⟨h₄, h₅⟩,
      intros h,
      have side_eq_db : (sides_of_triangle abd).nth 1 = bc.p1 ⬝ abd.p3,
        exact (congr_fun (congr_arg Segment.mk h₂) abd.p3).symm,
      rw side_eq_db at h₄,
      simp at h₄,
      dsimp at *,
      have h₅ : (sides_of_triangle abd).head = a ⬝ bc.p1,
        { sorry},
      have eq_a_b : a = bc.p1,
        apply zero_segment (a ⬝ bc.p1) abd.p3,
        rw [h, ← h₅],
        rw h at h₄,
        tidy},
  have b_in_circ : circle_interior bc.p1 circ,
    { unfold circle_interior,
      simp,
      unfold radius,
      simp,
      apply distance_pos,
      --apply distance_not_neg,
      sorry},
  have ray_circle_intersect := ray_circle_intersect db ne_d_b circ bc.p1,
  sorry
end

-- # Proposition 3
lemma prop3 (AB C : Segment) (greater : length AB > length C):
  ∃ (s : Segment), (length s = length C) ∧ (s.p1 = AB.p1) ∧ (between AB.p1 s.p2 AB.p2) :=
begin
  sorry
end

-- # Proposition 4
------------------
-- If two triangles have two sides equal to two sides respectively,
-- and have the angles contained by the equal straight lines equal,
-- then they also have the base equal to the base, the triangle equals
-- the triangle, and the remaining angles equal the remaining angles
-- respectively, namely those opposite the equal sides.
-- SAS congruency.
lemma prop4 (t1 t2 : Triangle) (dif1 : distinct t1.p1 t1.p2 t1.p3) (dif2 : distinct t2.p1 t2.p2 t2.p3):
  let sides1 := (sides_of_triangle t1) in
  let sides2 := (sides_of_triangle t2) in
  let angles1 := (angles_of_triangle t1 dif1) in
  let angles2 := (angles_of_triangle t2 dif2) in
     (sides1.nth 0 = sides2.nth 0)
  → (sides1.nth 1 = sides2.nth 1)
  → (angles1.nth 0 ≃ angles2.nth 0)
  → (sides1.nth 2 = sides2.nth 2)
     ∧ (angles1.nth 1 = angles2.nth 1) ∧ (angles1.nth 2 = angles2.nth 2) :=
begin
  sorry
end



-- # Proposition 5
-- # Proposition 7
-- # Proposition 8
-- # Proposition 10
-- # Proposition 11
-- # Proposition 13
-- # Proposition 14
-- # Proposition 15
-- # Proposition 16
-- # Proposition 18
-- # Proposition 19
-- # Proposition 20
-- # Proposition 22
-- # Proposition 26
-- # Proposition 29
-- # Proposition 31
-- # Proposition 34
-- # Proposition 37
-- # Proposition 41
-- # Proposition 46
-- # Proposition 47
-- # Proposition 48
