import LehmerTotient.Barrier

/-!
# Primality of the largest entry (Section 9.8)

A prefix with products `A = ∏ xᵢ` and `B = ∏ (xᵢ - 1)` and defect `C = 2B - A`.

* `largest_coprime_defect`: Lemma 9.9, first sentence: if `A` is odd and prime to `B`, then `C` is prime to `2AB`.
* `largest_sub_one`, `largest_coprime_entry`: Lemma 9.9 (i): if `C X = 2B + ε`, then `C (X - 1) = A + ε`, and `X` is
  prime to `2B` and `X - 1` prime to `A`.
* `largest_defect_one`: Lemma 9.9 (ii): if `C = 1`, then `X = A + 1 + ε`.
* `largest_three_dvd`, `largest_three_not_dvd`: Lemma 9.9 (iii) for Lehmer's sign, for pairwise coprime entries with
  `gcd(xᵢ, xₗ - 1) = 1` (which independent primes satisfy): if `3 ∣ A` then `3 ∣ X`, and otherwise `3 ∤ X`, `3 ∤ C`.
* `defect_pos_iff`, `defect_step`, `defect_rest_bounds`, `defect_dvd_iff`, `defect_completion`: Lemma 9.11, the
  defects of the children of a prefix.
-/

namespace LehmerTotient

open Finset

/-! ### Lemma 9.9 -/

/-- Lemma 9.9: for odd `A` prime to `B`, the defect `2B - A` is prime to `2AB`. -/
theorem largest_coprime_defect (A B : ℤ) (hA : Odd A) (hAB : IsCoprime A B) :
    IsCoprime (2 * B - A) (2 * A * B) := by
  have h2A : IsCoprime (2 : ℤ) A := by
    obtain ⟨k, hk⟩ := hA
    exact ⟨-k, 1, by rw [hk]; ring⟩
  -- `2B - A` is prime to `B`, to `A` and to `2`.
  have hB : IsCoprime (2 * B - A) B := by
    have : IsCoprime (-A + B * 2) B := (hAB.neg_left).add_mul_left_left 2
    convert this using 1; ring
  have hA' : IsCoprime (2 * B - A) A := by
    have h2BA : IsCoprime (2 * B) A := h2A.mul_left hAB.symm
    have : IsCoprime (2 * B + A * (-1)) A := h2BA.add_mul_left_left (-1)
    convert this using 1; ring
  have h2 : IsCoprime (2 * B - A) 2 := by
    have : IsCoprime (-A + 2 * B) 2 := (h2A.symm.neg_left).add_mul_left_left B
    convert this using 1; ring
  exact (h2.mul_right hA').mul_right hB

/-- Lemma 9.9 (i), first part: `C X = 2B + ε` gives `C (X - 1) = A + ε`. -/
theorem largest_sub_one (A B ε X : ℤ) (hX : (2 * B - A) * X = 2 * B + ε) :
    (2 * B - A) * (X - 1) = A + ε := by
  linear_combination hX

/-- Lemma 9.9 (i), second part: `X` is prime to `2B` and `X - 1` is prime to `A`. -/
theorem largest_coprime_entry (A B ε X : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hX : (2 * B - A) * X = 2 * B + ε) : IsCoprime X (2 * B) ∧ IsCoprime (X - 1) A := by
  have hu : ∀ y : ℤ, IsCoprime ε y := fun y => ⟨ε, 0, by rcases hε with rfl | rfl <;> ring⟩
  have h1 : IsCoprime (2 * B + ε) (2 * B) := by
    have : IsCoprime (ε + (2 * B) * 1) (2 * B) := (hu (2 * B)).add_mul_left_left 1
    convert this using 1; ring
  have h2 : IsCoprime (A + ε) A := by
    have : IsCoprime (ε + A * 1) A := (hu A).add_mul_left_left 1
    convert this using 1; ring
  refine ⟨?_, ?_⟩
  · rw [← hX] at h1
    exact h1.of_mul_left_right
  · rw [← largest_sub_one A B ε X hX] at h2
    exact h2.of_mul_left_right

/-- Lemma 9.9 (ii): if the defect is `1`, the entry is `A + 1 + ε`, that is `A` for `ε = -1` and `A + 2` for
`ε = 1`. -/
theorem largest_defect_one (A B ε X : ℤ) (hC : 2 * B - A = 1)
    (hX : (2 * B - A) * X = 2 * B + ε) : X = A + 1 + ε := by
  rw [hC, one_mul] at hX
  linarith

/-- In `ZMod 3` every element is `0`, `1` or `2`. -/
private theorem zmod3_cases : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by
  decide

private theorem cast3_dvd {a : ℤ} : (3 : ℤ) ∣ a ↔ ((a : ℤ) : ZMod 3) = 0 :=
  (cast3_eq_zero_iff a).symm

/-- Lemma 9.9 (iii), first case: pairwise coprime entries with `gcd(xᵢ, xₗ - 1) = 1`, `3 ∣ A` and
`C X = 2B - 1` give `3 ∣ X`. -/
theorem largest_three_dvd {j : ℕ} (x : Fin j → ℤ) (X : ℤ)
    (hcop : ∀ i l, i ≠ l → IsCoprime (x i) (x l)) (hgcd : ∀ i l, IsCoprime (x i) (x l - 1))
    (h3 : (3 : ℤ) ∣ ∏ i, x i)
    (hX : (2 * ∏ i, (x i - 1) - ∏ i, x i) * X = 2 * ∏ i, (x i - 1) - 1) : (3 : ℤ) ∣ X := by
  obtain ⟨i0, -, hi0⟩ := (Int.prime_three.dvd_finsetProd_iff _).mp h3
  have hx0 : ((x i0 : ℤ) : ZMod 3) = 0 := cast3_dvd.mp hi0
  -- every other entry is `2` modulo `3`
  have hother : ∀ l, l ≠ i0 → ((x l : ℤ) : ZMod 3) = 2 := by
    intro l hl
    rcases zmod3_cases ((x l : ℤ) : ZMod 3) with h | h | h
    · exfalso
      have h3l : (3 : ℤ) ∣ x l := cast3_dvd.mpr h
      have hc := hcop i0 l (Ne.symm hl)
      exact Int.prime_three.not_isUnit (hc.isUnit_of_dvd' hi0 h3l)
    · exfalso
      have h3l : (3 : ℤ) ∣ x l - 1 := cast3_dvd.mpr (by push_cast; rw [h]; ring)
      exact Int.prime_three.not_isUnit ((hgcd i0 l).isUnit_of_dvd' hi0 h3l)
    · exact h
  have hB : ((∏ i, (x i - 1) : ℤ) : ZMod 3) = 2 := by
    push_cast
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0), hx0]
    rw [Finset.prod_eq_one]
    · decide
    · intro l hl
      rw [hother l (Finset.ne_of_mem_erase hl)]
      decide
  have hA : ((∏ i, x i : ℤ) : ZMod 3) = 0 := cast3_dvd.mp h3
  have e := congrArg (fun z : ℤ => (z : ZMod 3)) hX
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_one] at e
  rw [hB, hA] at e
  have e' : ((X : ℤ) : ZMod 3) = 0 := by
    have : (2 * 2 - 0 : ZMod 3) = 1 := by decide
    rw [this, one_mul] at e
    rw [e]; decide
  exact cast3_dvd.mpr e'

/-- Lemma 9.9 (iii), second case: if `3 ∤ A` and `C X = 2B - 1`, then `3` divides neither `X` nor `C`. -/
theorem largest_three_not_dvd {j : ℕ} (x : Fin j → ℤ) (X : ℤ)
    (h3 : ¬ (3 : ℤ) ∣ ∏ i, x i)
    (hX : (2 * ∏ i, (x i - 1) - ∏ i, x i) * X = 2 * ∏ i, (x i - 1) - 1) :
    ¬ (3 : ℤ) ∣ X ∧ ¬ (3 : ℤ) ∣ (2 * ∏ i, (x i - 1) - ∏ i, x i) := by
  -- no entry is `0` modulo `3`, so every `xᵢ - 1` is `0` or `1`, and so is their product
  have hnz : ∀ i, ((x i : ℤ) : ZMod 3) ≠ 0 := by
    intro i hi
    exact h3 (dvd_trans (cast3_dvd.mpr hi) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  have hB : ((∏ i, (x i - 1) : ℤ) : ZMod 3) = 0 ∨ ((∏ i, (x i - 1) : ℤ) : ZMod 3) = 1 := by
    push_cast
    apply Finset.prod_induction _ (fun b : ZMod 3 => b = 0 ∨ b = 1)
    · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
    · right; rfl
    · intro i _
      rcases zmod3_cases ((x i : ℤ) : ZMod 3) with h | h | h
      · exact absurd h (hnz i)
      · left; rw [h]; ring
      · right; rw [h]; decide
  have hne : ((2 * ∏ i, (x i - 1) - 1 : ℤ) : ZMod 3) ≠ 0 := by
    push_cast
    rcases hB with h | h
    · push_cast at h; rw [h]; decide
    · push_cast at h; rw [h]; decide
  rw [← hX] at hne
  push_cast at hne
  constructor
  · intro hd
    apply hne
    rw [cast3_dvd.mp hd, mul_zero]
  · intro hd
    apply hne
    have := cast3_dvd.mp hd
    push_cast at this
    rw [this, zero_mul]

/-! ### Lemma 9.11 -/

/-- Lemma 9.11: appending `y` gives a positive defect `Cy - 2B` exactly when `y ≥ ⌊2B/C⌋ + 1`. -/
theorem defect_pos_iff (B C y : ℤ) (hC : 0 < C) : 0 < C * y - 2 * B ↔ 2 * B / C + 1 ≤ y := by
  rw [Int.add_one_le_iff, Int.ediv_lt_iff_lt_mul hC, mul_comm y C, sub_pos]

/-- Lemma 9.11: the defects of the children form an arithmetic progression with difference `C`. -/
theorem defect_step (B C y : ℤ) :
    C * y - 2 * B = (C * (2 * B / C + 1) - 2 * B) + (y - (2 * B / C + 1)) * C := by
  ring

/-- `r = C y₀ - 2B` equals `C - (2B mod C)`. -/
private theorem defect_rest (B C : ℤ) : C * (2 * B / C + 1) - 2 * B = C - 2 * B % C := by
  linear_combination Int.mul_ediv_add_emod (2 * B) C

/-- Lemma 9.11: `r = C - (2B mod C)` lies between `1` and `C - 1` when `C ≥ 2` does not divide `2B`. -/
theorem defect_rest_bounds (B C : ℤ) (hC : 2 ≤ C) (hnd : ¬ C ∣ 2 * B) :
    C * (2 * B / C + 1) - 2 * B = C - 2 * B % C ∧
      1 ≤ C * (2 * B / C + 1) - 2 * B ∧ C * (2 * B / C + 1) - 2 * B ≤ C - 1 := by
  have hlt : 2 * B % C < C := Int.emod_lt_of_pos _ (by omega)
  have hnn : 0 ≤ 2 * B % C := Int.emod_nonneg _ (by omega)
  have hne : 2 * B % C ≠ 0 := fun h => hnd (Int.dvd_of_emod_eq_zero h)
  rw [defect_rest]
  refine ⟨rfl, ?_, ?_⟩ <;> omega

/-- Lemma 9.11: `C ≥ 2` divides `2B - 1` exactly when `r = C - 1`. -/
theorem defect_dvd_iff (B C : ℤ) (hC : 2 ≤ C) :
    C ∣ 2 * B - 1 ↔ C * (2 * B / C + 1) - 2 * B = C - 1 := by
  have hlt : 2 * B % C < C := Int.emod_lt_of_pos _ (by omega)
  have hnn : 0 ≤ 2 * B % C := Int.emod_nonneg _ (by omega)
  have key : C ∣ 2 * B - 1 ↔ C ∣ 2 * B % C - 1 := by
    have e : 2 * B - 1 = C * (2 * B / C) + (2 * B % C - 1) := by
      linear_combination -(Int.mul_ediv_add_emod (2 * B) C)
    rw [e]
    exact Int.dvd_add_right (dvd_mul_right C _)
  rw [key, defect_rest]
  constructor
  · intro h
    have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  · intro h
    have : 2 * B % C - 1 = 0 := by omega
    rw [this]
    exact dvd_zero C

/-- Lemma 9.11: when `C ≥ 2` divides `2B - 1`, the completing entry is `(2B - 1)/C = ⌊2B/C⌋ = y₀ - 1`. -/
theorem defect_completion (B C : ℤ) (hC : 2 ≤ C) (h : C ∣ 2 * B - 1) :
    (2 * B - 1) / C = 2 * B / C := by
  obtain ⟨m, hm⟩ := h
  have h1 : (2 * B - 1) / C = m := Int.ediv_eq_of_eq_mul_right (by omega) hm
  have h2 : 2 * B / C = m := by
    have e : 2 * B = 1 + m * C := by linarith
    rw [e, Int.add_mul_ediv_right 1 m (by omega : C ≠ 0), Int.ediv_eq_zero_of_lt (by norm_num) (by omega),
      zero_add]
  rw [h1, h2]

end LehmerTotient
