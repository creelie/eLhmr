import LehmerTotient.PseudoExtend
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Two-entry extensions from the companion sign to Lehmer's sign (Proposition 9.6)

Let `l` solve `x₁ ⋯ x_k + 1 = 2 ∏ (xᵢ - 1)`, let `A = ∏ xᵢ`, and let `d e = A² + A - 1`. Then
`l ++ [A + 1 + d, A + 1 + e]` solves `x₁ ⋯ x_{k+2} - 1 = 2 ∏ (xᵢ - 1)`.

* `lehmer_ext_eq`: the equation.
* `lehmer_ext_pairwise`: if the entries of `l` are pairwise coprime, then so are those of the longer list if and only if
  `gcd(d² - 1, A) = gcd(d - 1, A + 2) = 1`.
* `dvd_mod_five`, `lehmer_ext_five`: if `5 ∣ A`, every divisor of `A² + A - 1` is `≡ ±1 (mod 5)` (by quadratic
  reciprocity), so the condition fails.
-/

namespace LehmerTotient

/-- The equation: two entries built from a factorisation of `A² + A - 1` turn the companion sign into Lehmer's sign. -/
theorem lehmer_ext_eq {l : List ℕ} {d e : ℕ} (h : l.prod + 1 = 2 * pm1 l)
    (hde : d * e + 1 = l.prod * l.prod + l.prod) :
    (l ++ [l.prod + 1 + d, l.prod + 1 + e]).prod = 2 * pm1 (l ++ [l.prod + 1 + d, l.prod + 1 + e]) + 1 := by
  set A := l.prod with hAdef
  have hp : pm1 (l ++ [A + 1 + d, A + 1 + e]) = pm1 l * ((A + d) * (A + e)) := by
    simp only [pm1, List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    congr 2 <;> omega
  rw [hp, List.prod_append]
  simp only [List.prod_cons, List.prod_nil, mul_one]
  have hde' : (d : ℤ) * e + 1 = A * A + A := by exact_mod_cast hde
  have h' : (A : ℤ) + 1 = 2 * pm1 l := by exact_mod_cast h
  have : (A : ℤ) * ((A + 1 + d) * (A + 1 + e)) = 2 * (pm1 l * ((A + d) * (A + e))) + 1 := by
    linear_combination ((A : ℤ) + d) * (A + e) * h' - hde'
  exact_mod_cast this

/-- The longer list is again increasing when `d < e`. -/
theorem lehmer_ext_sorted {l : List ℕ} {d e : ℕ} (hl : l.Pairwise (· < ·)) (hpos : ∀ x ∈ l, 1 ≤ x)
    (hlt : d < e) : (l ++ [l.prod + 1 + d, l.prod + 1 + e]).Pairwise (· < ·) := by
  rw [List.pairwise_append]
  refine ⟨hl, by simp; omega, ?_⟩
  intro a ha b hb
  have hle : a ≤ l.prod := Nat.le_of_dvd (List.prod_pos (fun x hx => hpos x hx)) (List.dvd_prod ha)
  simp at hb
  omega

lemma coprime_X {A d : ℕ} : Nat.Coprime (A + 1 + d) A ↔ Nat.Coprime (d + 1) A := by
  rw [show A + 1 + d = (d + 1) + A by ring]
  exact Nat.coprime_add_self_left

lemma coprime_Y {A d e : ℕ} (h : d * e + 1 = A * A + A) (hd : 1 ≤ d) :
    Nat.Coprime (A + 1 + e) A ↔ Nat.Coprime (d - 1) A := by
  rw [show A + 1 + e = (e + 1) + A by ring, Nat.coprime_add_self_left]
  have hdA : Nat.Coprime d A := by
    have h1 : Nat.gcd d A ∣ d * e := Dvd.dvd.mul_right (Nat.gcd_dvd_left d A) e
    have h2 : Nat.gcd d A ∣ A * A + A :=
      dvd_add (Dvd.dvd.mul_right (Nat.gcd_dvd_right d A) A) (Nat.gcd_dvd_right d A)
    rw [← h] at h2
    exact Nat.eq_one_of_dvd_one ((Nat.dvd_add_right h1).mp h2)
  have hk : d * (e + 1) = (d - 1) + A * (A + 1) := by
    zify [hd] at h ⊢
    linear_combination h
  constructor
  · intro h1
    have h2 : Nat.Coprime (d * (e + 1)) A := Nat.Coprime.mul_left hdA h1
    rw [hk] at h2
    exact (Nat.coprime_add_mul_left_left (d - 1) A (A + 1)).mp h2
  · intro h1
    have h2 : Nat.Coprime (d * (e + 1)) A := by
      rw [hk]; exact (Nat.coprime_add_mul_left_left (d - 1) A (A + 1)).mpr h1
    exact Nat.Coprime.coprime_mul_left h2

lemma coprime_XY {A d e : ℕ} (h : d * e + 1 = A * A + A) (hd : 1 ≤ d) :
    Nat.Coprime (A + 1 + d) (A + 1 + e) ↔ Nat.Coprime (d - 1) (A + 2) := by
  constructor
  · intro hc
    by_contra hn
    obtain ⟨p, hp, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hX : p ∣ A + 1 + d := by
      rw [show A + 1 + d = (A + 2) + (d - 1) by omega]
      exact dvd_add h2 h1
    have hdY : d * (A + 1 + e) = (d - 1) * (A + 1) + A * (A + 2) := by
      zify [hd] at h ⊢
      linear_combination h
    have hpd : ¬ p ∣ d := by
      intro hpd
      have h3 := Nat.dvd_sub hpd h1
      rw [Nat.sub_sub_self hd] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
    have hY : p ∣ A + 1 + e := by
      have h4 : p ∣ d * (A + 1 + e) := by
        rw [hdY]; exact dvd_add (Dvd.dvd.mul_right h1 _) (Dvd.dvd.mul_left h2 _)
      exact ((Nat.Prime.dvd_mul hp).mp h4).resolve_left hpd
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hX, hY⟩) hc
  · intro hc
    by_contra hn
    obtain ⟨p, hp, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hid : (A + 1) * ((A + 1 + d) + (A + 1 + e)) = (A + 1 + d) * (A + 1 + e) + (A + 2) := by
      zify at h ⊢
      linear_combination (-1 : ℤ) * h
    have hA2 : p ∣ A + 2 := by
      have h3 : p ∣ (A + 1) * ((A + 1 + d) + (A + 1 + e)) := Dvd.dvd.mul_left (dvd_add h1 h2) _
      rw [hid] at h3
      exact (Nat.dvd_add_right (Dvd.dvd.mul_right h1 _)).mp h3
    have hd1 : p ∣ d - 1 := by
      rw [show d - 1 = (A + 1 + d) - (A + 2) by omega]
      exact Nat.dvd_sub h1 hA2
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hd1, hA2⟩) hc

/-- Pairwise coprimality of the longer list. -/
theorem lehmer_ext_pairwise {l : List ℕ} {d e : ℕ} (hl : l.Pairwise Nat.Coprime)
    (hde : d * e + 1 = l.prod * l.prod + l.prod) (hd : 1 ≤ d) :
    (l ++ [l.prod + 1 + d, l.prod + 1 + e]).Pairwise Nat.Coprime ↔
      Nat.Coprime (d ^ 2 - 1) l.prod ∧ Nat.Coprime (d - 1) (l.prod + 2) := by
  set A := l.prod with hA
  have hsq : d ^ 2 - 1 = (d - 1) * (d + 1) := by
    zify [hd, Nat.one_le_pow 2 d hd]; ring
  rw [List.pairwise_append, List.pairwise_pair, hsq, Nat.coprime_mul_iff_left]
  have hall : (∀ a ∈ l, ∀ b ∈ [A + 1 + d, A + 1 + e], Nat.Coprime a b) ↔
      Nat.Coprime (A + 1 + d) A ∧ Nat.Coprime (A + 1 + e) A := by
    have key : ∀ x, Nat.Coprime x A ↔ ∀ a ∈ l, Nat.Coprime a x := by
      intro x; rw [Nat.coprime_comm, hA, Nat.coprime_list_prod_left_iff]
    rw [key, key]
    constructor
    · intro h; exact ⟨fun a ha => h a ha _ (by simp), fun a ha => h a ha _ (by simp)⟩
    · intro h a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact h.1 a ha
      · exact h.2 a ha
  rw [hall, coprime_X, coprime_Y hde hd, coprime_XY hde hd]
  tauto

/-- The squares modulo `5` are `0`, `1` and `4`. -/
lemma sq_mod_five : ∀ m : ℕ, m < 5 → ∀ y : ZMod 5, (m : ZMod 5) = y * y → m = 0 ∨ m = 1 ∨ m = 4 := by
  decide

/-- If `5 ∣ A`, every prime factor of `A² + A - 1` is `≡ ±1 (mod 5)`: `(2A + 1)² ≡ 5`, so `5` is a square modulo the
prime, and quadratic reciprocity applies. -/
lemma prime_dvd_mod_five {A r : ℕ} (hr : r.Prime) (h5 : 5 ∣ A) (hA : 1 ≤ A) (hdvd : r ∣ A * A + A - 1) :
    r % 5 = 1 ∨ r % 5 = 4 := by
  have hev : 2 ∣ A * A + A := by
    rw [show A * A + A = A * (A + 1) by ring]; exact even_iff_two_dvd.mp (Nat.even_mul_succ_self A)
  have h5N : 5 ∣ A * A + A := by
    rw [show A * A + A = A * (A + 1) by ring]; exact Dvd.dvd.mul_right h5 _
  have hpos : 2 ≤ A * A + A := by nlinarith
  generalize ht : A * A + A = t at hev h5N hpos hdvd
  have hr2 : r ≠ 2 := by rintro rfl; omega
  have hr5 : r ≠ 5 := by rintro rfl; omega
  have := Fact.mk hr
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsq : IsSquare ((5 : ℕ) : ZMod r) := by
    refine ⟨((2 * A + 1 : ℕ) : ZMod r), ?_⟩
    have hz : ((t - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have hid : (2 * A + 1) * (2 * A + 1) = 4 * (t - 1) + 5 := by
      have : (2 * A + 1) * (2 * A + 1) = 4 * (A * A + A) + 1 := by ring
      rw [this, ht]; omega
    have h2 : (((2 * A + 1) * (2 * A + 1) : ℕ) : ZMod r) = ((4 * (t - 1) + 5 : ℕ) : ZMod r) := by rw [hid]
    rw [Nat.cast_mul] at h2
    rw [h2]
    simp only [Nat.cast_add, Nat.cast_mul, hz, mul_zero, zero_add]
  have hsq' : IsSquare ((r : ℕ) : ZMod 5) :=
    (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := r) (by norm_num) hr2).mpr hsq
  obtain ⟨y, hy⟩ := hsq'
  have hmod : ((r % 5 : ℕ) : ZMod 5) = y * y := by rw [ZMod.natCast_mod]; exact hy
  have hlt : r % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hne : r % 5 ≠ 0 := by
    intro h0
    exact hr5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hr).mp (Nat.dvd_of_mod_eq_zero h0)).symm
  rcases sq_mod_five _ hlt y hmod with h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr h

/-- If `5 ∣ A`, every divisor of `A² + A - 1` is `≡ ±1 (mod 5)`. -/
lemma dvd_mod_five {A d : ℕ} (h5 : 5 ∣ A) (hA : 1 ≤ A) (hd : d ∣ A * A + A - 1) : d % 5 = 1 ∨ d % 5 = 4 := by
  have hNpos : 0 < A * A + A - 1 := by
    have : 2 ≤ A * A + A := by nlinarith
    omega
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases Nat.lt_trichotomy d 1 with h | h | h
    · have h0 : d = 0 := by omega
      subst h0; rw [zero_dvd_iff] at hd; omega
    · subst h; left; rfl
    · have hp := Nat.minFac_prime (show d ≠ 1 by omega)
      obtain ⟨q, hq⟩ := Nat.minFac_dvd d
      have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0, mul_zero] at hq; omega
        · exact h0
      have hq_lt : q < d := by
        have h2 := hp.two_le
        rw [hq]; nlinarith
      have hqd : q ∣ A * A + A - 1 := Dvd.dvd.trans (Dvd.intro_left _ hq.symm) hd
      have hpN : d.minFac ∣ A * A + A - 1 := Dvd.dvd.trans (Nat.minFac_dvd d) hd
      have h1 := prime_dvd_mod_five hp h5 hA hpN
      have h2 := ih q hq_lt hqd
      rw [hq, Nat.mul_mod]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> decide

/-- If `5 ∣ A`, the condition `gcd(d² - 1, A) = 1` fails for every factorisation `d e = A² + A - 1`. -/
theorem lehmer_ext_five {A d e : ℕ} (h5 : 5 ∣ A) (hde : d * e + 1 = A * A + A) :
    ¬ Nat.Coprime (d ^ 2 - 1) A := by
  have hA : 1 ≤ A := by
    rcases Nat.eq_zero_or_pos A with h0 | h0
    · subst h0; omega
    · exact h0
  have hd : d ∣ A * A + A - 1 := ⟨e, by rw [← hde]; simp⟩
  have h := dvd_mod_five h5 hA hd
  have hsq : d ^ 2 % 5 = 1 := by
    rw [Nat.pow_mod]; rcases h with h | h <;> rw [h]
  have h5d : 5 ∣ d ^ 2 - 1 := by
    generalize d ^ 2 = t at hsq ⊢; omega
  exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) h5d h5

end LehmerTotient
