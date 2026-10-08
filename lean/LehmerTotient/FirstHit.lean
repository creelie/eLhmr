import LehmerTotient.Imports

/-!
# The first-hit recursion (Lemma 4.3 of the paper)

For `0 ≤ a < M` and `0 < L ≤ R < M`, `Hits M a L R` is the set of `y ≥ 0` with
`L ≤ a y mod M ≤ R`.  The function `firstHit` is the recursion of Lemma 4.3, and
`firstHit_spec` shows that it returns the least element of `Hits M a L R`, or `none` when the
set is empty.
-/

namespace LehmerTotient

/-- The set of Lemma 4.3. -/
def Hits (M a L R : ℕ) : Set ℕ := {y | L ≤ a * y % M ∧ a * y % M ≤ R}

/-- The recursion of Lemma 4.3.  The ceiling `⌈x / a⌉` is written `(x + a - 1) / a`. -/
def firstHit (M a L R : ℕ) : Option ℕ :=
  if a = 0 then none
  else if a * ((L + a - 1) / a) ≤ R then some ((L + a - 1) / a)
  else
    match firstHit a (M % a) (a - R % a) (a - L % a) with
    | none => none
    | some z => some ((L + M * z + a - 1) / a)
termination_by a
decreasing_by exact Nat.mod_lt M (by omega)

/-- `⌈x / a⌉ ≤ y` if and only if `x ≤ a y`. -/
lemma ceil_le_iff {a x y : ℕ} (ha : 0 < a) : (x + a - 1) / a ≤ y ↔ x ≤ a * y := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have h1 : y + 1 ≤ (x + a - 1) / a := by
      rw [Nat.le_div_iff_mul_le ha]
      rw [Nat.add_mul, one_mul, mul_comm]
      omega
    omega
  · intro h
    by_contra hlt
    push Not at hlt
    have h1 : (y + 1) * a ≤ x + a - 1 := (Nat.le_div_iff_mul_le ha).mp hlt
    rw [Nat.add_mul, one_mul, mul_comm] at h1
    omega

/-- `x ≤ a ⌈x / a⌉`. -/
lemma le_mul_ceil {a x : ℕ} (ha : 0 < a) : x ≤ a * ((x + a - 1) / a) :=
  (ceil_le_iff ha).mp le_rfl

/-- If `R < M`, then `y` is a hit exactly when `L + M z ≤ a y ≤ R + M z` for some `z`, and then
`z = a y / M`. -/
lemma hit_iff {M a L R y : ℕ} (hRM : R < M) :
    y ∈ Hits M a L R ↔ ∃ z, L + M * z ≤ a * y ∧ a * y ≤ R + M * z := by
  have hM : 0 < M := by omega
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨a * y / M, ?_, ?_⟩
    · have := Nat.div_add_mod (a * y) M
      omega
    · have := Nat.div_add_mod (a * y) M
      omega
  · rintro ⟨z, h1, h2⟩
    have hx : a * y % M = a * y - M * z := by
      have e : a * y = (a * y - M * z) + M * z := by omega
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      omega
    constructor <;> omega

/-- The quotient `a y / M` of a hit `y`. -/
lemma hit_quot {M a L R y z : ℕ} (hRM : R < M) (h1 : L + M * z ≤ a * y)
    (h2 : a * y ≤ R + M * z) : a * y / M = z := by
  have hM : 0 < M := by omega
  have := Nat.div_add_mod (a * y) M
  have hlt := Nat.mod_lt (a * y) hM
  apply le_antisymm
  · by_contra hc
    push Not at hc
    have : M * (z + 1) ≤ M * (a * y / M) := Nat.mul_le_mul_left M hc
    rw [Nat.mul_add, mul_one] at this
    omega
  · by_contra hc
    push Not at hc
    have : M * (a * y / M + 1) ≤ M * z := Nat.mul_le_mul_left M hc
    rw [Nat.mul_add, mul_one] at this
    omega

lemma not_hits_zero {M L R y : ℕ} (hL : 0 < L) : y ∉ Hits M 0 L R := by
  simp only [Hits, zero_mul, Nat.zero_mod, Set.mem_ofPred_eq]
  omega

/-- The case `a ⌈L / a⌉ ≤ R`: the answer is `⌈L / a⌉`. -/
lemma first_case {M a L R : ℕ} (ha : 0 < a) (hRM : R < M) (hfit : a * ((L + a - 1) / a) ≤ R) :
    (L + a - 1) / a ∈ Hits M a L R ∧ ∀ y ∈ Hits M a L R, (L + a - 1) / a ≤ y := by
  have hL0 : L ≤ a * ((L + a - 1) / a) := le_mul_ceil ha
  constructor
  · have : a * ((L + a - 1) / a) % M = a * ((L + a - 1) / a) := Nat.mod_eq_of_lt (by omega)
    exact ⟨by omega, by omega⟩
  · intro y hy
    by_contra hlt
    push Not at hlt
    have h1 : a * y < L := by
      by_contra hc
      push Not at hc
      have := (ceil_le_iff ha).mpr hc
      omega
    have : a * y % M = a * y := Nat.mod_eq_of_lt (by omega)
    have := hy.1
    omega

/-- If no multiple of `a` lies in `[L, R]`, then `L` and `R` have the same quotient by `a`, and
`0 < L mod a ≤ R mod a`. -/
lemma no_multiple {a L R : ℕ} (ha : 0 < a) (hLR : L ≤ R) (hfit : R < a * ((L + a - 1) / a)) :
    a * (R / a) + L % a = L ∧ 0 < L % a ∧ L % a ≤ R % a := by
  have hnomul : ∀ m, L ≤ a * m → R < a * m := by
    intro m hm
    have h1 : (L + a - 1) / a ≤ m := (ceil_le_iff ha).mpr hm
    have : a * ((L + a - 1) / a) ≤ a * m := Nat.mul_le_mul_left a h1
    omega
  have hLd := Nat.div_add_mod L a
  have hRd := Nat.div_add_mod R a
  have hLm := Nat.mod_lt L ha
  have hqR : a * (R / a) < L := by
    by_contra hc
    push Not at hc
    have := hnomul _ hc
    omega
  have hq : L / a = R / a := by
    apply le_antisymm (Nat.div_le_div_right hLR)
    by_contra hc
    push Not at hc
    have : a * (L / a + 1) ≤ a * (R / a) := Nat.mul_le_mul_left a hc
    rw [Nat.mul_add, mul_one] at this
    omega
  rw [hq] at hLd
  refine ⟨hLd, ?_, ?_⟩ <;> omega

/-- A hit `y` of the original problem gives the hit `a y / M` of the reduced one. -/
lemma reduce_fwd {M a L R y : ℕ} (ha : 0 < a) (hRM : R < M)
    (hL : a * (R / a) + L % a = L) (hr : 0 < L % a) (hrr : L % a ≤ R % a)
    (hy : y ∈ Hits M a L R) : a * y / M ∈ Hits a (M % a) (a - R % a) (a - L % a) := by
  obtain ⟨z, h1, h2⟩ := (hit_iff hRM).mp hy
  rw [hit_quot hRM h1 h2]
  have hRd := Nat.div_add_mod R a
  have hRm := Nat.mod_lt R ha
  obtain ⟨q, hq⟩ : ∃ q, q = R / a := ⟨_, rfl⟩
  rw [← hq] at hL hRd
  obtain ⟨s, hs⟩ : ∃ s, a * y = M * z + a * q + s := ⟨a * y - M * z - a * q, by omega⟩
  have hs1 : L % a ≤ s := by omega
  have hs2 : s ≤ R % a := by omega
  have hyq : q + 1 ≤ y := by
    by_contra hc
    push Not at hc
    have : a * y ≤ a * q := Nat.mul_le_mul_left a (by omega)
    omega
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hyq
  have e : M * z = (a - s) + a * t := by
    have : a * (q + 1 + t) = a * q + a + a * t := by ring
    omega
  have hmod : M % a * z % a = a - s := by
    rw [Nat.mod_mul_mod, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  simp only [Hits, Set.mem_ofPred_eq]
  rw [hmod]
  omega

/-- A hit `z` of the reduced problem gives the hit `⌈(L + M z) / a⌉` of the original one. -/
lemma reduce_bwd {M a L R z : ℕ} (ha : 0 < a) (hRM : R < M)
    (hL : a * (R / a) + L % a = L) (hr : 0 < L % a) (hrr : L % a ≤ R % a)
    (hz : z ∈ Hits a (M % a) (a - R % a) (a - L % a)) :
    (L + M * z + a - 1) / a ∈ Hits M a L R ∧ a * ((L + M * z + a - 1) / a) / M = z := by
  have hRd := Nat.div_add_mod R a
  have hRm := Nat.mod_lt R ha
  obtain ⟨q, hq⟩ : ∃ q, q = R / a := ⟨_, rfl⟩
  rw [← hq] at hL hRd
  obtain ⟨hz1, hz2⟩ := hz
  rw [Nat.mod_mul_mod] at hz1 hz2
  have hsa := Nat.mod_lt (M * z) ha
  have hMz := Nat.div_add_mod (M * z) a
  obtain ⟨y', hy'def⟩ : ∃ y', y' = M * z / a + 1 + q := ⟨_, rfl⟩
  have hy' : a * y' = a * (M * z / a) + a + a * q := by rw [hy'def]; ring
  have hy'1 : L + M * z ≤ a * y' := by omega
  have hy'2 : a * y' ≤ R + M * z := by omega
  have hyy : (L + M * z + a - 1) / a = y' := by
    apply le_antisymm ((ceil_le_iff ha).mpr hy'1)
    by_contra hc
    push Not at hc
    have h3 : L + M * z ≤ a * ((L + M * z + a - 1) / a) := le_mul_ceil ha
    have : a * ((L + M * z + a - 1) / a + 1) ≤ a * y' := Nat.mul_le_mul_left a hc
    rw [Nat.mul_add, mul_one] at this
    omega
  rw [hyy]
  exact ⟨(hit_iff hRM).mpr ⟨z, hy'1, hy'2⟩, hit_quot hRM hy'1 hy'2⟩

/-- When `R - L < a`, a hit `y` is determined by `z = a y / M`: it is `⌈(L + M z) / a⌉`. -/
lemma hit_det {M a L R y : ℕ} (ha : 0 < a) (hRM : R < M) (hLRa : R < L + a)
    (hy : y ∈ Hits M a L R) : y = (L + M * (a * y / M) + a - 1) / a := by
  obtain ⟨z, h1, h2⟩ := (hit_iff hRM).mp hy
  rw [hit_quot hRM h1 h2]
  apply le_antisymm _ ((ceil_le_iff ha).mpr h1)
  by_contra hc
  push Not at hc
  have h3 : L + M * z ≤ a * ((L + M * z + a - 1) / a) := le_mul_ceil ha
  have : a * ((L + M * z + a - 1) / a + 1) ≤ a * y := Nat.mul_le_mul_left a hc
  rw [Nat.mul_add, mul_one] at this
  omega

/-- Lemma 4.3: for `a < M` and `0 < L ≤ R < M`, `firstHit M a L R` is the least `y ≥ 0` with
`L ≤ a y mod M ≤ R`, and it is `none` exactly when there is no such `y`. -/
theorem firstHit_spec (a : ℕ) : ∀ M L R : ℕ, a < M → 0 < L → L ≤ R → R < M →
    (∀ y, firstHit M a L R = some y → y ∈ Hits M a L R ∧ ∀ y' ∈ Hits M a L R, y ≤ y') ∧
      (firstHit M a L R = none → ∀ y, y ∉ Hits M a L R) := by
  refine Nat.strong_induction_on a ?_
  intro a ih M L R haM hL hLR hRM
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hnone : firstHit M 0 L R = none := by rw [firstHit]; simp
    exact ⟨fun y hy => by simp [hnone] at hy, fun _ _ => not_hits_zero hL⟩
  by_cases hfit : a * ((L + a - 1) / a) ≤ R
  · have heq : firstHit M a L R = some ((L + a - 1) / a) := by
      rw [firstHit]; simp [ha.ne', hfit]
    obtain ⟨hmem, hleast⟩ := first_case ha hRM hfit
    refine ⟨fun y hy => ?_, fun h => by simp [heq] at h⟩
    rw [heq] at hy
    cases hy
    exact ⟨hmem, hleast⟩
  · push Not at hfit
    obtain ⟨hLq, hr, hrr⟩ := no_multiple ha hLR hfit
    have hRd := Nat.div_add_mod R a
    have hRm := Nat.mod_lt R ha
    have hLRa : R < L + a := by omega
    have hrec := ih (M % a) (Nat.mod_lt M ha) a (a - R % a) (a - L % a) (Nat.mod_lt M ha)
      (by omega) (by omega) (by omega)
    rcases hz : firstHit a (M % a) (a - R % a) (a - L % a) with _ | z
    · have hnone : firstHit M a L R = none := by
        rw [firstHit]; simp [ha.ne', not_le.mpr hfit, hz]
      refine ⟨fun y hy => by simp [hnone] at hy, fun _ y hy => ?_⟩
      exact hrec.2 hz _ (reduce_fwd ha hRM hLq hr hrr hy)
    · have hsome : firstHit M a L R = some ((L + M * z + a - 1) / a) := by
        rw [firstHit]; simp [ha.ne', not_le.mpr hfit, hz]
      obtain ⟨hzmem, hzleast⟩ := hrec.1 z hz
      obtain ⟨hymem, hyq⟩ := reduce_bwd ha hRM hLq hr hrr hzmem
      refine ⟨fun y hy => ?_, fun h => by simp [hsome] at h⟩
      rw [hsome] at hy
      cases hy
      refine ⟨hymem, fun y' hy' => ?_⟩
      by_contra hlt
      push Not at hlt
      have hz' := hzleast _ (reduce_fwd ha hRM hLq hr hrr hy')
      have hle : a * y' / M ≤ a * ((L + M * z + a - 1) / a) / M :=
        Nat.div_le_div_right (Nat.mul_le_mul_left a hlt.le)
      rw [hyq] at hle
      have hzz : a * y' / M = z := le_antisymm hle hz'
      have := hit_det ha hRM hLRa hy'
      rw [hzz] at this
      omega

end LehmerTotient
