import LehmerTotient.Imports

/-!
# Elementary reductions (Section 2 of the paper)

Throughout, `ε` is `1` or `-1`, and the divisibility `φ n ∣ n + ε` is read in `ℤ`.
The quotient is written `M`, so that `n + ε = M * φ n`.

* `LehmerTotient.odd_of_dvd`, `squarefree_of_dvd`, `prime_not_dvd_sub_one`,
  `prime_not_dvd_quotient`, `not_prime_of_dvd_add_one`, `two_le_quotient`: Lemma 2.1.
* `mod_three_of_three_dvd`, `totient_mod_three`, `quotient_mod_three`: Lemma 2.2, first part.
-/

open Nat

namespace LehmerTotient

/-- `ε` is a sign. -/
def IsSign (ε : ℤ) : Prop := ε = 1 ∨ ε = -1

lemma IsSign.natAbs {ε : ℤ} (hε : IsSign ε) : ε.natAbs = 1 := by
  rcases hε with rfl | rfl <;> rfl

lemma not_dvd_sign {p : ℕ} (hp : p.Prime) {ε : ℤ} (hε : IsSign ε) : ¬ (p : ℤ) ∣ ε := by
  intro h
  have h1 : p ∣ ε.natAbs := Int.natCast_dvd.mp h
  rw [hε.natAbs] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- The basic obstruction: a prime factor of `n` cannot divide `φ n`. -/
lemma false_of_dvd_totient {n p : ℕ} {ε : ℤ} (hε : IsSign ε) (h : (φ n : ℤ) ∣ n + ε)
    (hp : p.Prime) (hpn : p ∣ n) (hpφ : p ∣ φ n) : False := by
  have h1 : (p : ℤ) ∣ n + ε := (Int.natCast_dvd_natCast.mpr hpφ).trans h
  have h2 : (p : ℤ) ∣ n := Int.natCast_dvd_natCast.mpr hpn
  have h3 : (p : ℤ) ∣ ε := by simpa using dvd_sub h1 h2
  exact not_dvd_sign hp hε h3

/-- Lemma 2.1(i): a solution with `n > 2` is odd. -/
theorem odd_of_dvd {n : ℕ} {ε : ℤ} (hε : IsSign ε) (h : (φ n : ℤ) ∣ n + ε) (hn : 2 < n) :
    Odd n := by
  by_contra hodd
  have h2n : 2 ∣ n := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have h2φ : 2 ∣ φ n := even_iff_two_dvd.mp (totient_even hn)
  exact false_of_dvd_totient hε h Nat.prime_two h2n h2φ

/-- Lemma 2.1(i): a solution is squarefree. -/
theorem squarefree_of_dvd {n : ℕ} {ε : ℤ} (hε : IsSign ε) (h : (φ n : ℤ) ∣ n + ε) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp' hpp
  have h1 : φ (p * p) ∣ φ n := totient_dvd_of_dvd hpp
  have h2 : φ (p * p) = p * (p - 1) := by
    rw [← sq, totient_prime_pow hp' (by norm_num)]
    simp
  rw [h2] at h1
  exact false_of_dvd_totient hε h hp' ((dvd_mul_right p p).trans hpp)
    ((dvd_mul_right p (p - 1)).trans h1)

/-- Lemma 2.1(ii): no prime factor of `n` divides `q - 1` for a prime factor `q` of `n`. -/
theorem prime_not_dvd_sub_one {n p q : ℕ} {ε : ℤ} (hε : IsSign ε) (h : (φ n : ℤ) ∣ n + ε)
    (hp : p.Prime) (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n) : ¬ p ∣ q - 1 := by
  intro hpq
  have : q - 1 ∣ φ n := by
    rw [← totient_prime hq]
    exact totient_dvd_of_dvd hqn
  exact false_of_dvd_totient hε h hp hpn (hpq.trans this)

/-- Lemma 2.1(ii): no prime factor of `n` divides the quotient `M`. -/
theorem prime_not_dvd_quotient {n p : ℕ} {ε M : ℤ} (hε : IsSign ε)
    (hM : (n : ℤ) + ε = M * φ n) (hp : p.Prime) (hpn : p ∣ n) : ¬ (p : ℤ) ∣ M := by
  intro hpM
  have h1 : (p : ℤ) ∣ n + ε := by
    rw [hM]
    exact dvd_mul_of_dvd_left hpM _
  have h2 : (p : ℤ) ∣ n := Int.natCast_dvd_natCast.mpr hpn
  have h3 : (p : ℤ) ∣ ε := by simpa using dvd_sub h1 h2
  exact not_dvd_sign hp hε h3

/-- Lemma 2.1(i): for `φ n ∣ n + 1` a prime solution satisfies `n ≤ 3`. -/
theorem not_prime_of_dvd_add_one {n : ℕ} (h : (φ n : ℤ) ∣ n + 1) (hn : 3 < n) :
    ¬ n.Prime := by
  intro hpr
  rw [totient_prime hpr] at h
  have h1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [h1] at h
  have h2 : (n : ℤ) - 1 ∣ 2 := by
    have := dvd_sub h (dvd_refl ((n : ℤ) - 1))
    have e : (n : ℤ) + 1 - ((n : ℤ) - 1) = 2 := by ring
    rwa [e] at this
  have h3 := Int.le_of_dvd (by norm_num) h2
  omega

/-- Lemma 2.1(i): for a composite solution the quotient is at least `2`. -/
theorem two_le_quotient {n : ℕ} {ε M : ℤ} (hε : IsSign ε) (hn : 1 < n) (hc : ¬ n.Prime)
    (hM : (n : ℤ) + ε = M * φ n) : 2 ≤ M := by
  have hlt : φ n < n := totient_lt n hn
  have hne : φ n ≠ n - 1 := fun e => hc ((totient_eq_iff_prime (by omega)).mp e)
  have hle : (φ n : ℤ) ≤ (n : ℤ) - 2 := by
    have : φ n ≤ n - 2 := by omega
    have h2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [← h2]
    exact_mod_cast this
  have hpos : (0 : ℤ) ≤ φ n := by positivity
  rcases hε with rfl | rfl
  · by_contra hM2
    have : M ≤ 1 := by omega
    nlinarith
  · by_contra hM2
    have : M ≤ 1 := by omega
    nlinarith

/-! ### The prime `3` (Lemma 2.2) -/

/-- If `3 ∣ n`, every other prime factor of a solution is `2` modulo `3`. -/
theorem mod_three_of_three_dvd {n q : ℕ} {ε : ℤ} (hε : IsSign ε) (h : (φ n : ℤ) ∣ n + ε)
    (h3 : 3 ∣ n) (hq : q.Prime) (hqn : q ∣ n) (hq3 : q ≠ 3) : q % 3 = 2 := by
  have h1 : ¬ 3 ∣ q - 1 := prime_not_dvd_sub_one hε h Nat.prime_three hq h3 hqn
  have h2 : ¬ 3 ∣ q := fun hd =>
    hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp hd).symm
  have hq2 : 2 ≤ q := hq.two_le
  omega

/-- For squarefree `n` with `3 ∣ n` whose other prime factors are all `2` modulo `3`,
`φ n ≡ 2 (mod 3)`. -/
theorem totient_mod_three {n : ℕ} (hn : n ≠ 0) (hsq : Squarefree n) (h3 : 3 ∣ n)
    (hq : ∀ q ∈ n.primeFactors, q ≠ 3 → q % 3 = 2) : (φ n : ZMod 3) = 2 := by
  rw [totient_eq_prod_factorization hn, Finsupp.prod, Nat.support_factorization, Nat.cast_prod]
  have hfac : ∀ p ∈ n.primeFactors, n.factorization p = 1 := by
    intro p hp
    have h1 := hsq.natFactorization_le_one p
    have h2 : 0 < n.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors hp)
    omega
  have hterm : ∀ p ∈ n.primeFactors,
      (((p ^ (n.factorization p - 1) * (p - 1) : ℕ)) : ZMod 3) = if p = 3 then 2 else 1 := by
    intro p hp
    rw [hfac p hp]
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with h
    · subst h
      decide
    · have hmod : (p - 1) % 3 = 1 := by have := hq p hp h; omega
      simp only [Nat.sub_self, pow_zero, one_mul]
      rw [← ZMod.natCast_mod, hmod]
      simp
  rw [Finset.prod_congr rfl hterm, Finset.prod_ite_eq']
  have : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, hn⟩
  simp [this]

/-- Lemma 2.2: if `3 ∣ n` then `2 M ≡ ε (mod 3)`, so `M ≡ 1` for `ε = -1` and `M ≡ 2` for
`ε = 1`. -/
theorem quotient_mod_three {n : ℕ} {ε M : ℤ} (hε : IsSign ε) (hn : 0 < n)
    (hM : (n : ℤ) + ε = M * φ n) (h3 : 3 ∣ n) : (2 * M : ZMod 3) = ε := by
  have hdvd : (φ n : ℤ) ∣ n + ε := ⟨M, by rw [hM]; ring⟩
  have hsq := squarefree_of_dvd hε hdvd
  have hq : ∀ q ∈ n.primeFactors, q ≠ 3 → q % 3 = 2 := fun q hq hq3 =>
    mod_three_of_three_dvd hε hdvd h3 (Nat.prime_of_mem_primeFactors hq)
      (Nat.dvd_of_mem_primeFactors hq) hq3
  have hφ := totient_mod_three hn.ne' hsq h3 hq
  have hn3 : (n : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff n 3).mpr h3
  have e := congrArg (fun x : ℤ => (x : ZMod 3)) hM
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at e
  rw [hn3, hφ, zero_add] at e
  rw [e]
  ring

end LehmerTotient
