import LehmerTotient.Imports
import Mathlib.Data.Nat.Prime.Int

/-!
# Pseudo-solutions prime to 3 and congruences (Lemma 9.2, Proposition 9.4)

The product equation `x₁ ⋯ x_k + ε = M ∏ (xᵢ - 1)` over the integers, with `ε = ±1`.

* `gcd_of_product_eq`: the conditions `gcd(xᵢ, xⱼ - 1) = 1` follow from the equation.
* `three_parity`: Lemma 9.2. If `3` divides exactly `s ≥ 1` entries, then `ε ≡ M (-1)^s (mod 3)`.
* `three_parity_lehmer`, `three_parity_companion`: for `M = 2`, `s` is even when `ε = -1`, and odd when `ε = +1`
  and `s ≥ 1`.
* `lehmer_coprime_three_free`: a solution with `ε = -1` and pairwise coprime entries has no entry divisible by `3`.
* `local_witness`: Proposition 9.4 for prime-power moduli. With `gcd(A, 2B) = 1`, at least two entries left and any
  prime power `l^e`, the congruence `A y₁ ⋯ y_m + ε ≡ 2B ∏ (yᵢ - 1) (mod l^e)` has a solution with no `yᵢ`
  divisible by `l` and, if `l ∣ A`, no `yᵢ ≡ 1 (mod l)`, except when `l = 3`, `3 ∣ A` and `2B ≢ ε (mod 3)`.
* `three_obstruction`: in that excluded case there is no such solution.
-/

namespace LehmerTotient

open Finset

/-- A residue that is neither `0` nor `1` modulo `3` is `2`. -/
lemma zmod3_eq_two : ∀ {z : ZMod 3}, z ≠ 0 → z ≠ 1 → z = 2 := by decide

lemma cast3_eq_zero_iff (a : ℤ) : ((a : ZMod 3) = 0) ↔ (3 : ℤ) ∣ a := by
  simpa using ZMod.intCast_zmod_eq_zero_iff_dvd a 3

/-- The conditions `gcd(x_i, x_j - 1) = 1` follow from the product equation when `ε = ±1`: a common divisor of
`∏ x_i` and `∏ (x_j - 1)` divides `ε`. -/
theorem gcd_of_product_eq {k : ℕ} (x : Fin k → ℤ) (M ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (heq : ∏ i, x i + ε = M * ∏ i, (x i - 1)) : ∀ i j, Int.gcd (x i) (x j - 1) = 1 := by
  intro i j
  set g : ℤ := ((Int.gcd (x i) (x j - 1) : ℕ) : ℤ)
  have h1 : g ∣ ∏ i, x i := dvd_trans (Int.gcd_dvd_left _ _) (Finset.dvd_prod_of_mem _ (mem_univ i))
  have h2 : g ∣ ∏ i, (x i - 1) := dvd_trans (Int.gcd_dvd_right _ _) (Finset.dvd_prod_of_mem _ (mem_univ j))
  have h3 : g ∣ ε := by
    have : ε = M * ∏ i, (x i - 1) - ∏ i, x i := by linarith
    rw [this]; exact dvd_sub (dvd_mul_of_dvd_right h2 _) h1
  have h4 : g ∣ 1 := by
    rcases hε with rfl | rfl
    · exact h3
    · exact (dvd_neg).mp (by simpa using h3)
  have := Int.eq_one_of_dvd_one (by positivity) h4
  simp only [g] at this
  exact_mod_cast this

/-- The 3-parity lemma. If `x_1 ⋯ x_k + ε = M ∏ (x_i - 1)`, `gcd(x_i, x_j - 1) = 1` for all `i, j`, and `3`
divides some entry, then `ε ≡ M · (-1)^s (mod 3)`, where `s` is the number of entries divisible by `3`. -/
theorem three_parity {k : ℕ} (x : Fin k → ℤ) (M ε : ℤ)
    (hgcd : ∀ i j, Int.gcd (x i) (x j - 1) = 1)
    (heq : ∏ i, x i + ε = M * ∏ i, (x i - 1))
    (h3 : ∃ i, (3 : ℤ) ∣ x i) :
    (ε : ZMod 3) = M * (-1) ^ (univ.filter fun i => (3 : ℤ) ∣ x i).card := by
  obtain ⟨i0, hi0⟩ := h3
  have hne1 : ∀ j, ((x j : ℤ) : ZMod 3) ≠ 1 := by
    intro j hj
    have h31 : (3 : ℤ) ∣ x j - 1 := by
      rw [← cast3_eq_zero_iff]; push_cast; rw [hj]; ring
    have h := Int.dvd_coe_gcd hi0 h31
    rw [hgcd i0 j] at h; norm_num at h
  have hmap := congrArg (fun z : ℤ => (z : ZMod 3)) heq
  simp only [Int.cast_add, Int.cast_mul, Int.cast_prod, Int.cast_sub, Int.cast_one] at hmap
  have hp0 : ∏ i, ((x i : ℤ) : ZMod 3) = 0 :=
    Finset.prod_eq_zero (mem_univ i0) ((cast3_eq_zero_iff _).mpr hi0)
  have hp1 : ∏ i, (((x i : ℤ) : ZMod 3) - 1) = ∏ i, (if (3 : ℤ) ∣ x i then (-1 : ZMod 3) else 1) := by
    apply prod_congr rfl; intro j _
    split_ifs with h
    · rw [(cast3_eq_zero_iff _).mpr h]; ring
    · have h0 : ((x j : ℤ) : ZMod 3) ≠ 0 := by rwa [Ne, cast3_eq_zero_iff]
      rw [zmod3_eq_two h0 (hne1 j)]; decide
  rw [hp0, hp1, prod_ite, prod_const_one, mul_one, prod_const, zero_add] at hmap
  exact hmap

/-- For Lehmer's product equation (`M = 2`, `ε = -1`) the number of entries divisible by `3` is even. -/
theorem three_parity_lehmer {k : ℕ} (x : Fin k → ℤ)
    (heq : ∏ i, x i - 1 = 2 * ∏ i, (x i - 1)) :
    Even (univ.filter fun i => (3 : ℤ) ∣ x i).card := by
  have hgcd := gcd_of_product_eq x 2 (-1) (Or.inr rfl) (by rw [← heq]; ring)
  by_cases h3 : ∃ i, (3 : ℤ) ∣ x i
  · have h := three_parity x 2 (-1) hgcd (by rw [← heq]; ring) h3
    rcases Nat.even_or_odd (univ.filter fun i => (3 : ℤ) ∣ x i).card with he | ho
    · exact he
    · rw [ho.neg_one_pow] at h; exact absurd h (by decide)
  · push Not at h3
    rw [filter_false_of_mem (fun i _ => h3 i)]; simp

/-- For the companion equation (`M = 2`, `ε = +1`) the number of entries divisible by `3` is `0` or odd. -/
theorem three_parity_companion {k : ℕ} (x : Fin k → ℤ)
    (heq : ∏ i, x i + 1 = 2 * ∏ i, (x i - 1)) (h3 : ∃ i, (3 : ℤ) ∣ x i) :
    Odd (univ.filter fun i => (3 : ℤ) ∣ x i).card := by
  have hgcd := gcd_of_product_eq x 2 1 (Or.inl rfl) heq
  have h := three_parity x 2 1 hgcd heq h3
  rcases Nat.even_or_odd (univ.filter fun i => (3 : ℤ) ∣ x i).card with he | ho
  · rw [he.neg_one_pow] at h; exact absurd h (by decide)
  · exact ho

/-- Consequently a formal Lehmer tuple whose entries are pairwise coprime has no entry divisible by `3`. -/
theorem lehmer_coprime_three_free {k : ℕ} (x : Fin k → ℤ)
    (hcop : ∀ i j, i ≠ j → Int.gcd (x i) (x j) = 1)
    (heq : ∏ i, x i - 1 = 2 * ∏ i, (x i - 1)) : ∀ i, ¬ (3 : ℤ) ∣ x i := by
  intro i hi
  have he := three_parity_lehmer x heq
  have hsub : (univ.filter fun j => (3 : ℤ) ∣ x j) = {i} := by
    ext j; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hj; by_contra hne
      have := Int.dvd_coe_gcd hj hi; rw [hcop j i hne] at this; norm_num at this
    · rintro rfl; exact hi
  rw [hsub, card_singleton] at he
  exact absurd he (by decide)

/-- The smallest pseudo-solution of Proposition 9.1 has two entries divisible by 3. -/
example : (univ.filter fun i : Fin 3 => (3 : ℤ) ∣ ![3, 5, 15] i).card = 2 := by decide

/-! ### Local solvability: Lemma 2.2 is the only congruence obstruction -/

lemma not_dvd_one_of_prime {l : ℕ} (hl : l.Prime) : ¬ (l : ℤ) ∣ 1 := by
  intro h
  have := Int.eq_one_of_dvd_one (by positivity) h
  exact hl.one_lt.ne' (by exact_mod_cast this)

/-- Local solvability of the product equation with at least two unknowns. Let `gcd(A, 2B) = 1`, `ε = ±1`,
`l` prime and `e ≥ 1`, and exclude only the case `l = 3`, `3 ∣ A`, `3 ∤ 2B - ε`. Then there are residues `x0, x1`
and `y` (the common residue of the other `m - 2` unknowns), none divisible by `l`, none `≡ 1 (mod l)` when
`l ∣ A`, with `A x0 x1 y^(m-2) + ε ≡ 2B (x0-1)(x1-1)(y-1)^(m-2) (mod l^e)`. -/
theorem local_witness {l e : ℕ} (hl : l.Prime) (he : 1 ≤ e) (m : ℕ) (A B ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hAB : IsCoprime A (2 * B)) (h3 : l = 3 → (3 : ℤ) ∣ A → (3 : ℤ) ∣ 2 * B - ε) :
    ∃ x0 x1 y : ℤ,
      (l : ℤ) ^ e ∣ A * (x0 * x1 * y ^ (m - 2)) + ε - 2 * B * ((x0 - 1) * (x1 - 1) * (y - 1) ^ (m - 2)) ∧
      (¬ (l : ℤ) ∣ x0 ∧ ¬ (l : ℤ) ∣ x1 ∧ ¬ (l : ℤ) ∣ y) ∧
      ((l : ℤ) ∣ A → ¬ (l : ℤ) ∣ x0 - 1 ∧ ¬ (l : ℤ) ∣ x1 - 1 ∧ ¬ (l : ℤ) ∣ y - 1) := by
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hn1 := not_dvd_one_of_prime hl
  have hεu : ¬ (l : ℤ) ∣ ε := by rcases hε with rfl | rfl <;> simp [hn1]
  have hle : (l : ℤ) ∣ (l : ℤ) ^ e := dvd_pow_self _ (by omega)
  by_cases hlA : (l : ℤ) ∣ A
  · -- l divides A: l is odd and prime to 2B
    have h2B : ¬ (l : ℤ) ∣ 2 * B := fun h => hlp.not_isUnit (hAB.isUnit_of_dvd' hlA h)
    have h2 : ¬ (l : ℤ) ∣ 2 := fun h => h2B (dvd_mul_of_dvd_left h _)
    have hB : ¬ (l : ℤ) ∣ B := fun h => h2B (dvd_mul_of_dvd_right h _)
    -- choose u1 in {1, 2} with l ∤ 2 B u1 + ε
    obtain ⟨u1, hu1, hu1l, hx1l, hgood⟩ : ∃ u1 : ℤ, (u1 = 1 ∨ u1 = 2) ∧ ¬ (l : ℤ) ∣ u1 ∧ ¬ (l : ℤ) ∣ u1 + 1 ∧
        ¬ (l : ℤ) ∣ 2 * B * u1 + ε := by
      by_cases hc : (l : ℤ) ∣ 2 * B * 1 + ε
      · refine ⟨2, Or.inr rfl, h2, ?_, ?_⟩
        · intro h3l
          have hl3 : l = 3 := by
            have h3' : (l : ℤ) ≤ 3 := Int.le_of_dvd (by norm_num) h3l
            have h3'' : l ≤ 3 := by exact_mod_cast h3'
            have h1 := hl.two_le
            interval_cases l
            · exact absurd (by norm_num : ((2 : ℕ) : ℤ) ∣ 2) h2
            · rfl
          subst hl3
          have := h3 rfl hlA
          have : (3 : ℤ) ∣ 2 * ε := by
            have := dvd_sub hc this; ring_nf at this ⊢; simpa [mul_comm] using this
          rcases hε with rfl | rfl <;> norm_num at this
        · intro h4
          have : (l : ℤ) ∣ 2 * B := by
            have := dvd_sub h4 hc; ring_nf at this ⊢; simpa [mul_comm] using this
          exact h2B this
      · exact ⟨1, Or.inl rfl, hn1, by simpa using h2, hc⟩
    set K : ℤ := A * (u1 + 1) * 2 ^ (m - 2) - 2 * B * u1 with hK
    have hKl : ¬ (l : ℤ) ∣ K := by
      intro h
      have h' : (l : ℤ) ∣ 2 * B * u1 := by
        have h0 : (l : ℤ) ∣ A * (u1 + 1) * 2 ^ (m - 2) :=
          dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hlA (u1 + 1)) (2 ^ (m - 2))
        have := dvd_sub h0 h
        have key : A * (u1 + 1) * 2 ^ (m - 2) - K = 2 * B * u1 := by rw [hK]; ring
        rwa [key] at this
      rcases hlp.dvd_or_dvd h' with h'' | h''
      · exact h2B h''
      · exact hu1l h''
    have hKc : IsCoprime K ((l : ℤ) ^ e) :=
      IsCoprime.pow_right ((Int.isCoprime_iff_gcd_eq_one.mpr
        (Int.gcd_comm _ _ ▸ (Int.isCoprime_iff_gcd_eq_one.mp ((hlp.coprime_iff_not_dvd).mpr hKl)))))
    obtain ⟨s, t, hst⟩ := hKc
    set x0 := s * (-(2 * B * u1 + ε)) with hx0
    have hexpr : A * (x0 * (u1 + 1) * 2 ^ (m - 2)) + ε - 2 * B * ((x0 - 1) * (u1 + 1 - 1) * (2 - 1) ^ (m - 2))
        = K * x0 + (2 * B * u1 + ε) := by rw [hK]; simp; ring
    have hdiv : (l : ℤ) ^ e ∣ K * x0 + (2 * B * u1 + ε) := by
      refine ⟨t * (2 * B * u1 + ε), ?_⟩
      rw [hx0]; linear_combination (-(2 * B * u1 + ε)) * hst
    refine ⟨x0, u1 + 1, 2, by rw [hexpr]; exact hdiv, ⟨?_, hx1l, h2⟩, fun _ => ⟨?_, by simpa using hu1l, by simpa using hn1⟩⟩
    · intro h
      exact hgood (by
        have := dvd_sub (dvd_trans hle hdiv) (dvd_mul_of_dvd_right h K)
        simpa using this)
    · intro h
      -- K x0 = K (mod l) and K + 2 B u1 = A (u1+1) 2^(m-2) = 0 (mod l)
      have h1 : (l : ℤ) ∣ K * (x0 - 1) := dvd_mul_of_dvd_right h K
      have h2' : (l : ℤ) ∣ A * (u1 + 1) * 2 ^ (m - 2) := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hlA _) _
      have : (l : ℤ) ∣ ε := by
        have := dvd_sub (dvd_sub (dvd_trans hle hdiv) h1) h2'
        have key : K * x0 + (2 * B * u1 + ε) - K * (x0 - 1) - A * (u1 + 1) * 2 ^ (m - 2) = ε := by rw [hK]; ring
        rwa [key] at this
      exact hεu this
  · -- l does not divide A: x0 = y = 1, x1 = -ε A⁻¹
    have hAc : IsCoprime A ((l : ℤ) ^ e) :=
      IsCoprime.pow_right (Int.isCoprime_iff_gcd_eq_one.mpr
        (Int.gcd_comm _ _ ▸ (Int.isCoprime_iff_gcd_eq_one.mp ((hlp.coprime_iff_not_dvd).mpr hlA))))
    obtain ⟨u, v, huv⟩ := hAc
    refine ⟨1, -ε * u, 1, ⟨ε * v, by linear_combination (-ε) * huv⟩, ⟨hn1, ?_, hn1⟩, fun h => absurd h hlA⟩
    · intro h
      have hu : (l : ℤ) ∣ u := by
        rcases hε with rfl | rfl <;> simpa using h
      exact hn1 (by rw [← huv]; exact dvd_add (dvd_mul_of_dvd_left hu _) (dvd_mul_of_dvd_right hle _))

/-- The obstruction at `3` (Lemma 2.2): if `3 ∣ A` and the unknowns are neither `≡ 0` nor `≡ 1 (mod 3)`, then the
product equation modulo `3` forces `2B ≡ ε (mod 3)`. -/
theorem three_obstruction {m : ℕ} (x : Fin m → ℤ) (A B ε : ℤ) (h3A : (3 : ℤ) ∣ A)
    (hx : ∀ i, ¬ (3 : ℤ) ∣ x i ∧ ¬ (3 : ℤ) ∣ x i - 1)
    (h : (3 : ℤ) ∣ A * ∏ i, x i + ε - 2 * B * ∏ i, (x i - 1)) : (3 : ℤ) ∣ 2 * B - ε := by
  rw [← cast3_eq_zero_iff] at h ⊢
  have hA : ((A : ℤ) : ZMod 3) = 0 := (cast3_eq_zero_iff _).mpr h3A
  have hxi : ∀ i, ((x i : ℤ) : ZMod 3) - 1 = 1 := by
    intro i
    have h0 : ((x i : ℤ) : ZMod 3) ≠ 0 := by rw [Ne, cast3_eq_zero_iff]; exact (hx i).1
    have h1 : ((x i : ℤ) : ZMod 3) ≠ 1 := by
      intro h1; apply (hx i).2; rw [← cast3_eq_zero_iff]; push_cast; rw [h1]; ring
    rw [zmod3_eq_two h0 h1]; decide
  push_cast at h ⊢
  rw [hA, Finset.prod_congr rfl (fun i _ => hxi i), prod_const_one] at h
  linear_combination -h

end LehmerTotient
