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
  distance c₁.center c₂.center ≤ radius c₁ + radius c₂ := 
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
lemma construct_equilateral (a b : Point) :
  ∃ (c : Point),
  let abc : Triangle := ⟨a, b, c⟩ in
  is_equilateral abc :=
begin
  set c₁ : Circle := ⟨a, b⟩,
  set c₂ : Circle := ⟨b, a⟩,
  have h₁ := hypothesis1_about_circles_radius (a⬝b),
  have h₂ := hypothesis2_about_circles_radius (a⬝b),
  set c := circles_intersect c₁ c₂ h₁ h₂,
  use c,
  simp,
  have hp₁ : c ∈ circumference c₁, from (circles_intersect' c₁ c₂ h₁ h₂).1,
  have hp₂ : c ∈ circumference c₂, from (circles_intersect' c₁ c₂ h₁ h₂).2,
  --- Cleaning up the context ---
    tidy,
    unfold circumference radius_segment at hp₁ hp₂;
    unfold sides_of_triangle;
    dsimp * at *,
  --- Cleaning done ---
    {calc a⬝b ≃ b⬝a : by symmetry
          ... ≃ b⬝c : by assumption},
    {calc b⬝c ≃ b⬝a : by {apply cong_symm, assumption}
          ... ≃ a⬝b : by apply segment_symm
          ... ≃ a⬝c : by assumption
          ... ≃ c⬝a : by symmetry},
end



lemma ray_cut_length (r : Ray) (s : Segment) (h : r.base ≠ r.ext)
  : ∃ p : Point, p ∈ points_of_ray r h ∧ r.base ⬝ p ≃ s := sorry



-- Lemma needed for proposition 2
lemma line_circle_intersect (a b : Point) (ne : a ≠ b) (C : Circle) :
     circle_interior a C
  → ∃ x : Point, lies_on x (line_of_points a b ne)
                ∧ x ∈ circumference C
                ∧ between x a b := sorry


-- Use *have* for introducing new facts. Follow it up with a proof of
-- said fact.
-- have x_pos : x > 0, .....

-- Use *let* for introducing new terms (of a given type). Follow it up
-- with a definition of the term.
-- Ex: let x : ℕ := 5

-- Use *set* is similar to *let*, but it additionally replaces every term
-- in the context with the new definition.
-- Ex: set x : ℕ := 5, -> replace x with 5 everywhere

-- Lemma needed for Proposition 2
lemma equilateral_triangle_nonzero_side_1 (a b c : Point) :
     a ≠ b
  → is_equilateral ⟨a, b, c⟩
  → b ≠ c :=
begin
  set abc : Triangle := ⟨a, b, c⟩,
  rintros ne_a_b ⟨h₁, h₂⟩ eq_b_c,
  set sides := sides_of_triangle abc,
  change sides.fst with a⬝b at h₁ h₂,
  change sides.snd.fst with b⬝c at h₁ h₂,
  change sides.snd.snd with c⬝a at h₁ h₂,
  subst eq_b_c,
  have eq_a_b : a = b := zero_segment _ _ h₁,
  cc,
end


lemma equilateral_triangle_nonzero_side_2 (a b c : Point) :
     a ≠ b
  → is_equilateral ⟨a, b, c⟩
  → c ≠ a :=
begin
  set abc : Triangle := ⟨a, b, c⟩,
  rintros ne_a_b ⟨h₁, h₂⟩ eq_b_c,
  set sides := sides_of_triangle abc,
  change sides.fst with a⬝b at h₁ h₂,
  change sides.snd.fst with b⬝c at h₁ h₂,
  change sides.snd.snd with c⬝a at h₁ h₂,
  subst eq_b_c,
  have eq_b_c : b = c := zero_segment _ _ h₂,
  cc,
end


lemma radius_nonzero (c : Circle) : c.center ≠ c.outer → 0 < radius c :=
begin
  simp only [radius, radius_segment],
  rw ← distance_pos c.center c.outer,
  tauto,
end


lemma radii_equal (c : Circle) (a b : Point) :
     a ∈ circumference c
  → b ∈ circumference c
  → c.center⬝a ≃ c.center⬝b :=
begin
  intros h₁ h₂,
  simp [circumference] at *,
  apply cong_trans,
  replace h₁ := cong_symm _ _ h₁,
  repeat {assumption},
end


-- Proposition 2
lemma placeline (a b c : Point) :
     a ≠ b
  → b ≠ c
  → ∃ (s : Segment), (a = s.p1) ∧ (s ≃ b⬝c) :=
begin
  intros ne_a_b ne_b_c,
  choose d h using construct_equilateral a b,
  set c₁ : Circle := ⟨b, c⟩,

  have ne_d_b : d ≠ b,
    { symmetry,
      apply equilateral_triangle_nonzero_side_1 a b d _ _,
      repeat {assumption}},
  have b_in_c₁ : circle_interior b c₁,
    by simpa [circle_interior, radius, radius_segment, ← distance_pos],

  have db_intersect_c₁ := line_circle_intersect b d ne_d_b.symm c₁ b_in_c₁,
  rcases db_intersect_c₁ with ⟨g, g_on_bd, g_in_circum_c₁, bet_g_b_d⟩,

  set c₂ : Circle := ⟨d, g⟩,
  have ne_d_a : d ≠ a,
    { apply equilateral_triangle_nonzero_side_2 a b d _ _,
      repeat {assumption}},
  have ne_d_g : d ≠ g,
    { rw [distance_pos, distance_is_symm, ((distance_between g b d).1 bet_g_b_d).symm],
      have h₁ : distance b d > 0 := (distance_pos b d).1 ne_d_b.symm,
      have h₂ : distance g b ≥ 0 := distance_not_neg g b,
      linarith},
  have d_in_c₂ : circle_interior d c₂,
    { simpa [circle_interior, radius, radius_segment, ← distance_pos]},
  have c_in_circum_c₁ : c ∈ circumference c₁,
    by simp [circumference, radius_segment],
  have a_in_c₂ : circle_interior a c₂,
    { simp [circle_interior, radius, radius_segment],
      rw [distance_is_symm d g, ← (distance_between g b d).1 bet_g_b_d],
      rcases h with ⟨h₁, h₂⟩,
      have eq_ad_bd : a⬝d ≃ b⬝d,
        change (sides_of_triangle ⟨a, b, d⟩).snd.fst with b⬝d at h₂,
        change (sides_of_triangle ⟨a, b, d⟩).snd.snd with d⬝a at h₂,
        apply cong_symm,
        apply cong_trans,
        assumption,
        apply segment_symm,
        replace eq_ad_bd := (distance_congruent _ _).1 eq_ad_bd,
        simp [length] at eq_ad_bd,
        simp [eq_ad_bd],
        have re := radii_equal c₁ g c g_in_circum_c₁ c_in_circum_c₁,
        simp [distance_congruent, length] at re,
        rwa [re, ← distance_pos b c]},

  have da_intersect_c₂ := line_circle_intersect a d ne_d_a.symm c₂ a_in_c₂,
  rcases da_intersect_c₂ with ⟨l, l_on_ad, l_in_circum_c₂, bet_l_a_d⟩,

  have dl_eq_al_da : length (d⬝l) = length (d⬝a) + length (a⬝l),
    { simp [length],
      rw [distance_is_symm a l, add_comm, (distance_between l a d).1 bet_l_a_d],
      symmetry},
  have dg_eq_bd_bg : length (d⬝g) = length (b⬝d) + length (b⬝g),
    { simp [length],
      rw [distance_is_symm b g, add_comm, (distance_between g b d).1 bet_g_b_d],
      symmetry},

  have g_in_circum_c₂ : g ∈ circumference c₂,
    by simp [circumference, radius_segment],
  have c_in_circum_c₁ : c ∈ circumference c₁,
    by simp [circumference, radius_segment],

  use a⬝l,
  rcases h with ⟨h₁, h₂⟩,
  change (sides_of_triangle {p1 := a, p2 := b, p3 := d}).fst with a⬝ b at h₁ h₂,
  change (sides_of_triangle {p1 := a, p2 := b, p3 := d}).snd.fst with b⬝d at h₁ h₂,
  change (sides_of_triangle {p1 := a, p2 := b, p3 := d}).snd.snd with d⬝a at h₁ h₂,
  split,
    { refl},
    { show a⬝l ≃ b⬝c,
      rw distance_congruent,
      calc length (a⬝l) = length (d⬝l) - length (d⬝a) : by simp [dl_eq_al_da]
                    ... = length (d⬝l) - length (b⬝d) :
                          by rw (distance_congruent _ _).1 h₂
                    ... = length (d⬝g) - length (b⬝d) :
                          by rw (distance_congruent _ _).1
                                (radii_equal c₂ l g l_in_circum_c₂ g_in_circum_c₂)
                    ... = length (b⬝g) : by simp [dg_eq_bd_bg]
                    ... = length (b⬝c) : by rw (distance_congruent _ _).1
                                (radii_equal c₁ g c g_in_circum_c₁ c_in_circum_c₁)}
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
     (sides1.1 = sides2.1)
  → (sides1.2.1 = sides2.2.1)
  → (angles1.1 ≃ angles2.1)
  → (sides1.2.2 = sides2.2.2)
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
