import LehmerTotient.Basic

/-!
# The bounds of the branch-and-bound (Section 3 of the paper)

A solution is a squarefree `n` with `n + ε = 2 φ(n)`.  Its prime factors form the finset
`S = n.primeFactors`, and for a subset `T` we write `P T = ∏_{p ∈ T} p / (p - 1)`.

* `totient_eq_prod_of_squarefree`: `φ n = ∏ (p - 1)` for squarefree `n`.
* `P_primeFactors`: `P S = 2 - ε / φ n` (equation (3.2)).
* `P_lt_two`: Proposition 3.1.
* `bounds_minus`, `bounds_plus`: Proposition 3.2.
* `last_two`: Proposition 3.5.
-/

open Nat Finset

namespace LehmerTotient

/-- `P T = ∏_{p ∈ T} p / (p - 1)`. -/
noncomputable def P (T : Finset ℕ) : ℚ := ∏ p ∈ T, (p : ℚ) / ((p : ℚ) - 1)

lemma one_le_prod {s : Finset ℕ} {f : ℕ → ℚ} (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    have h1 := h a (mem_insert_self a s)
    have h2 := ih (fun i hi => h i (mem_insert_of_mem hi))
    nlinarith

lemma prod_le_pow {s : Finset ℕ} {f : ℕ → ℚ} {x : ℚ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h : ∀ i ∈ s, f i ≤ x) : ∏ i ∈ s, f i ≤ x ^ s.card := by
  rw [← prod_const]
  exact Finset.prod_le_prod₀ h0 h

lemma ratio_gt_one {p : ℕ} (hp : 2 ≤ p) : 1 < (p : ℚ) / ((p : ℚ) - 1) := by
  have : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- `p / (p - 1)` decreases in `p`. -/
lemma ratio_le_ratio {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    (q : ℚ) / ((q : ℚ) - 1) ≤ (p : ℚ) / ((p : ℚ) - 1) := by
  have h1 : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have h2 : (p : ℚ) ≤ q := by exact_mod_cast hpq
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma ratio_lt_ratio {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) :
    (q : ℚ) / ((q : ℚ) - 1) < (p : ℚ) / ((p : ℚ) - 1) := by
  have h1 : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have h2 : (p : ℚ) < q := by exact_mod_cast hpq
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma one_le_P {T : Finset ℕ} (hT : ∀ p ∈ T, 2 ≤ p) : 1 ≤ P T :=
  one_le_prod fun p hp => (ratio_gt_one (hT p hp)).le

lemma P_pos {T : Finset ℕ} (hT : ∀ p ∈ T, 2 ≤ p) : 0 < P T := by
  have := one_le_P hT
  linarith

/-- `P` is multiplicative over a splitting `S = T ∪ (S \ T)`. -/
lemma P_split {S T : Finset ℕ} (h : T ⊆ S) : P S = P T * P (S \ T) := by
  unfold P
  rw [← prod_sdiff h, mul_comm]

/-- `φ n = ∏_{p ∣ n} (p - 1)` for squarefree `n`. -/
theorem totient_eq_prod_of_squarefree {n : ℕ} (hsq : Squarefree n) :
    φ n = ∏ p ∈ n.primeFactors, (p - 1) := by
  have h := totient_mul_prod_primeFactors n
  rw [prod_primeFactors_of_squarefree hsq] at h
  have hn : 0 < n := Nat.pos_of_ne_zero hsq.ne_zero
  rw [mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_left hn h

lemma cast_totient_of_squarefree {n : ℕ} (hsq : Squarefree n) :
    (φ n : ℚ) = ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) := by
  rw [totient_eq_prod_of_squarefree hsq, Nat.cast_prod]
  refine prod_congr rfl fun p hp => ?_
  have : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
  rw [Nat.cast_sub this]
  simp

lemma cast_n_of_squarefree {n : ℕ} (hsq : Squarefree n) :
    (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) := by
  conv_lhs => rw [← prod_primeFactors_of_squarefree hsq]
  rw [Nat.cast_prod]

lemma totient_pos_of_squarefree {n : ℕ} (hsq : Squarefree n) : (0 : ℚ) < φ n := by
  have hn : 0 < n := Nat.pos_of_ne_zero hsq.ne_zero
  exact_mod_cast Nat.totient_pos.mpr hn

/-- `P S = n / φ n` for squarefree `n`. -/
theorem P_eq_div {n : ℕ} (hsq : Squarefree n) : P n.primeFactors = (n : ℚ) / φ n := by
  rw [cast_n_of_squarefree hsq, cast_totient_of_squarefree hsq, P, prod_div_distrib]

/-- Equation (3.2): for a solution of `n + ε = 2 φ n`, `P S = 2 - ε / φ n`. -/
theorem P_primeFactors {n : ℕ} {ε : ℤ} (hsq : Squarefree n)
    (h : (n : ℤ) + ε = 2 * φ n) : P n.primeFactors = 2 - (ε : ℚ) / φ n := by
  have hφ := totient_pos_of_squarefree hsq
  rw [P_eq_div hsq, eq_sub_iff_add_eq, ← add_div, div_eq_iff hφ.ne']
  exact_mod_cast h

/-- A solution of `n + ε = 2 φ n` with `n > 1` is not prime. -/
lemma not_prime_of_solution {n : ℕ} {ε : ℤ} (hε : IsSign ε) (hn : 3 < n)
    (h : (n : ℤ) + ε = 2 * φ n) : ¬ n.Prime := by
  intro hp
  rw [totient_prime hp, Nat.cast_sub hp.one_lt.le] at h
  push_cast at h
  rcases hε with rfl | rfl <;> omega

/-- Proposition 3.1: every proper subset `T` of the prime factors of a solution has
`P T < 2`. -/
theorem P_lt_two {n : ℕ} {ε : ℤ} (hε : IsSign ε) (hsq : Squarefree n) (hn : 3 < n)
    (h : (n : ℤ) + ε = 2 * φ n) {T : Finset ℕ} (hT : T ⊂ n.primeFactors) : P T < 2 := by
  have h2 : ∀ p ∈ n.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hTS : T ⊆ n.primeFactors := hT.subset
  have hφ := totient_pos_of_squarefree hsq
  have hPS := P_primeFactors hsq h
  have hsplit := P_split hTS
  have hPT := P_pos fun p hp => h2 p (hTS hp)
  obtain ⟨p, hpS, hpT⟩ := exists_of_ssubset hT
  have hpR : p ∈ n.primeFactors \ T := mem_sdiff.mpr ⟨hpS, hpT⟩
  -- `P (S \ T) ≥ p / (p - 1)`
  have hR : (p : ℚ) / ((p : ℚ) - 1) ≤ P (n.primeFactors \ T) := by
    unfold P
    rw [← mul_prod_erase _ _ hpR]
    have h1 : 1 ≤ ∏ x ∈ (n.primeFactors \ T).erase p, (x : ℚ) / ((x : ℚ) - 1) :=
      one_le_prod fun x hx => (ratio_gt_one (h2 x (mem_sdiff.mp (mem_of_mem_erase hx)).1)).le
    have h3 : 0 < (p : ℚ) / ((p : ℚ) - 1) := by linarith [ratio_gt_one (h2 p hpS)]
    nlinarith
  rcases hε with rfl | rfl
  · -- `ε = 1`: `P S = 2 - 1/φ n < 2` and `P T ≤ P S`
    have hRge : 1 ≤ P (n.primeFactors \ T) := by linarith [ratio_gt_one (h2 p hpS)]
    have : P n.primeFactors < 2 := by
      rw [hPS]; push_cast
      have : 0 < (1 : ℚ) / φ n := by positivity
      linarith
    nlinarith
  · -- `ε = -1`: `P S = 2 n / (n - 1)` and `p < n`
    have hpn : p < n := by
      have hdvd := Nat.dvd_of_mem_primeFactors hpS
      have hle := Nat.le_of_dvd (by omega) hdvd
      have hne : p ≠ n := fun e => not_prime_of_solution (Or.inr rfl) hn h
        (e ▸ Nat.prime_of_mem_primeFactors hpS)
      omega
    have hlt := ratio_lt_ratio (h2 p hpS) hpn
    -- `n / (n - 1) * P T < P S = 2 n / (n - 1)`
    have hn1 : (1 : ℚ) < n := by exact_mod_cast (show 1 < n by omega)
    have hφn : (φ n : ℚ) = ((n : ℚ) - 1) / 2 := by
      have : ((n : ℤ) : ℚ) + ((-1 : ℤ) : ℚ) = 2 * (φ n : ℚ) := by exact_mod_cast h
      push_cast at this
      linarith
    have hPS' : P n.primeFactors = 2 * ((n : ℚ) / ((n : ℚ) - 1)) := by
      have hne : (n : ℚ) - 1 ≠ 0 := by linarith
      rw [hPS, hφn]
      push_cast
      field_simp
      ring
    have key : (n : ℚ) / ((n : ℚ) - 1) * P T < 2 * ((n : ℚ) / ((n : ℚ) - 1)) := by
      rw [← hPS', hsplit]
      nlinarith
    have hpos : 0 < (n : ℚ) / ((n : ℚ) - 1) := by
      apply _root_.div_pos <;> linarith
    nlinarith

/-! ### Proposition 3.2 -/

/-- The setting of Proposition 3.2: the prime factors `S` of a solution split into the chosen
primes `T` and the remaining primes `R = S \ T`, every element of `R` exceeds `pj` and every
element of `T` is at most `pj`, and `x0 = min R`. -/
structure Split (n : ℕ) (T : Finset ℕ) (pj x0 : ℕ) : Prop where
  sub : T ⊆ n.primeFactors
  odd : ∀ p ∈ n.primeFactors, Odd p
  le_pj : ∀ p ∈ T, p ≤ pj
  pj_odd : Odd pj
  gt_pj : ∀ p ∈ n.primeFactors \ T, pj < p
  x0_mem : x0 ∈ n.primeFactors \ T
  x0_le : ∀ p ∈ n.primeFactors \ T, x0 ≤ p
  two_le : 2 ≤ (n.primeFactors \ T).card

variable {n : ℕ} {T : Finset ℕ} {pj x0 : ℕ}

lemma Split.prime_ge_two (_hs : Split n T pj x0) : ∀ p ∈ n.primeFactors, 2 ≤ p :=
  fun _ hp => (Nat.prime_of_mem_primeFactors hp).two_le

/-- `x < ρ ≤ x ^ m` with `x = x0 / (x0 - 1)` and `ρ = P R`. -/
lemma Split.rho_bounds (hs : Split n T pj x0) :
    (x0 : ℚ) / ((x0 : ℚ) - 1) < P (n.primeFactors \ T) ∧
      P (n.primeFactors \ T) ≤ ((x0 : ℚ) / ((x0 : ℚ) - 1)) ^ (n.primeFactors \ T).card := by
  have h2 := hs.prime_ge_two
  have h2R : ∀ p ∈ n.primeFactors \ T, 2 ≤ p := fun p hp => h2 p (mem_sdiff.mp hp).1
  constructor
  · unfold P
    rw [← mul_prod_erase _ _ hs.x0_mem]
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ n.primeFactors \ T, y ≠ x0 := by
      by_contra hcon
      push Not at hcon
      have : n.primeFactors \ T ⊆ {x0} := fun y hy => mem_singleton.mpr (hcon y hy)
      have := card_le_card this
      simp at this
      have := hs.two_le
      omega
    have hy' : y ∈ (n.primeFactors \ T).erase x0 := mem_erase.mpr ⟨hyx, hy⟩
    have hgt : 1 < ∏ x ∈ (n.primeFactors \ T).erase x0, (x : ℚ) / ((x : ℚ) - 1) := by
      rw [← mul_prod_erase _ _ hy']
      have h1 : 1 ≤ ∏ x ∈ ((n.primeFactors \ T).erase x0).erase y, (x : ℚ) / ((x : ℚ) - 1) :=
        one_le_prod fun x hx =>
          (ratio_gt_one (h2R x (mem_of_mem_erase (mem_of_mem_erase hx)))).le
      have h3 := ratio_gt_one (h2R y hy)
      nlinarith
    have hx0 := ratio_gt_one (h2R x0 hs.x0_mem)
    nlinarith
  · apply prod_le_pow
    · intro p hp
      exact (ratio_gt_one (h2R p hp)).le.trans' (by norm_num)
    · intro p hp
      exact ratio_le_ratio (h2R x0 hs.x0_mem) (hs.x0_le p hp)

/-- `φ n ≥ B_j W` with `W = (pj + 1) ^ m`. -/
lemma Split.totient_ge (hs : Split n T pj x0) (hsq : Squarefree n) :
    (∏ p ∈ T, ((p : ℚ) - 1)) * ((pj : ℚ) + 1) ^ (n.primeFactors \ T).card ≤ φ n := by
  have h2 := hs.prime_ge_two
  rw [cast_totient_of_squarefree hsq, ← prod_sdiff hs.sub, mul_comm]
  apply mul_le_mul_of_nonneg_right
  · rw [← prod_const]
    apply Finset.prod_le_prod₀
    · intro p _; positivity
    · intro p hp
      have hpS := (mem_sdiff.mp hp).1
      have hgt := hs.gt_pj p hp
      obtain ⟨a, ha⟩ := hs.odd p hpS
      obtain ⟨b, hb⟩ := hs.pj_odd
      have : pj + 2 ≤ p := by omega
      have : ((pj + 2 : ℕ) : ℚ) ≤ p := by exact_mod_cast this
      push_cast at this
      linarith
  · apply prod_nonneg
    intro p hp
    have : (1 : ℚ) ≤ p := by exact_mod_cast (h2 p (hs.sub hp)).trans' (by norm_num)
    linarith

/-- Proposition 3.2 for `ε = -1`: with `x = x0 / (x0 - 1)`, `T' = 2 / P_j`, `m = |R|`,
`x ^ m > T'` and `x < T' + 1 / (A_j W)`. -/
theorem bounds_minus (hs : Split n T pj x0) (hsq : Squarefree n)
    (h : (n : ℤ) + (-1) = 2 * φ n) :
    let x := (x0 : ℚ) / ((x0 : ℚ) - 1)
    let m := (n.primeFactors \ T).card
    2 / P T < x ^ m ∧
      x < 2 / P T + 1 / ((∏ p ∈ T, (p : ℚ)) * ((pj : ℚ) + 1) ^ m) := by
  intro x m
  have h2 := hs.prime_ge_two
  have hPT := P_pos fun p hp => h2 p (hs.sub hp)
  have hφ := totient_pos_of_squarefree hsq
  obtain ⟨hlo, hhi⟩ := hs.rho_bounds
  have hPS := P_primeFactors hsq h
  have hsplit := P_split hs.sub
  -- `ρ = 2 / P T + 1 / (P T φ n)`
  have hrho : P (n.primeFactors \ T) = 2 / P T + 1 / (P T * φ n) := by
    have e : P T * P (n.primeFactors \ T) = 2 + 1 / φ n := by
      rw [← hsplit, hPS]; push_cast; ring
    calc P (n.primeFactors \ T) = P T * P (n.primeFactors \ T) / P T :=
          (mul_div_cancel_left₀ _ hPT.ne').symm
      _ = (2 + 1 / φ n) / P T := by rw [e]
      _ = 2 / P T + 1 / (P T * φ n) := by ring
  have hW := hs.totient_ge hsq
  have hA : P T * ∏ p ∈ T, ((p : ℚ) - 1) = ∏ p ∈ T, (p : ℚ) := by
    unfold P
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun p hp => ?_
    have : (1 : ℚ) < p := by exact_mod_cast (h2 p (hs.sub hp))
    exact div_mul_cancel₀ _ (by linarith)
  have hBpos : 0 < ∏ p ∈ T, ((p : ℚ) - 1) := by
    apply prod_pos
    intro p hp
    have : (1 : ℚ) < p := by exact_mod_cast (h2 p (hs.sub hp))
    linarith
  have hWpos : 0 < ((pj : ℚ) + 1) ^ m := by positivity
  constructor
  · have : 0 < 1 / (P T * φ n) := by positivity
    linarith
  · -- `1 / (P T φ n) ≤ 1 / (A W)` because `P T φ n ≥ P T B W = A W`
    have hle : (∏ p ∈ T, (p : ℚ)) * ((pj : ℚ) + 1) ^ m ≤ P T * φ n := by
      rw [← hA, mul_assoc]
      exact mul_le_mul_of_nonneg_left hW hPT.le
    have hApos : 0 < (∏ p ∈ T, (p : ℚ)) * ((pj : ℚ) + 1) ^ m := by
      rw [← hA]; positivity
    have : 1 / (P T * φ n) ≤ 1 / ((∏ p ∈ T, (p : ℚ)) * ((pj : ℚ) + 1) ^ m) :=
      one_div_le_one_div_of_le hApos hle
    linarith

/-- Proposition 3.2 for `ε = 1`: `x ^ m ≥ T' - 1 / (A_j W)` and `x < T'`. -/
theorem bounds_plus (hs : Split n T pj x0) (hsq : Squarefree n)
    (h : (n : ℤ) + 1 = 2 * φ n) :
    let x := (x0 : ℚ) / ((x0 : ℚ) - 1)
    let m := (n.primeFactors \ T).card
    2 / P T - 1 / ((∏ p ∈ T, (p : ℚ)) * ((pj : ℚ) + 1) ^ m) ≤ x ^ m ∧ x < 2 / P T := by
  intro x m
  have h2 := hs.prime_ge_two
  have hPT := P_pos fun p hp => h2 p (hs.sub hp)
  have hφ := totient_pos_of_squarefree hsq
  obtain ⟨hlo, hhi⟩ := hs.rho_bounds
  have hPS := P_primeFactors hsq h
  have hsplit := P_split hs.sub
  have hrho : P (n.primeFactors \ T) = 2 / P T - 1 / (P T * φ n) := by
    have e : P T * P (n.primeFactors \ T) = 2 - 1 / φ n := by
      rw [← hsplit, hPS]; push_cast; ring
    calc P (n.primeFactors \ T) = P T * P (n.primeFactors \ T) / P T :=
          (mul_div_cancel_left₀ _ hPT.ne').symm
      _ = (2 - 1 / φ n) / P T := by rw [e]
      _ = 2 / P T - 1 / (P T * φ n) := by ring
  have hW := hs.totient_ge hsq
  have hA : P T * ∏ p ∈ T, ((p : ℚ) - 1) = ∏ p ∈ T, (p : ℚ) := by
    unfold P
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun p hp => ?_
    have : (1 : ℚ) < p := by exact_mod_cast (h2 p (hs.sub hp))
    exact div_mul_cancel₀ _ (by linarith)
  have hWpos : 0 < ((pj : ℚ) + 1) ^ m := by positivity
  constructor
  · have hle : (∏ p ∈ T, (p : ℚ)) * ((pj : ℚ) + 1) ^ m ≤ P T * φ n := by
      rw [← hA, mul_assoc]
      exact mul_le_mul_of_nonneg_left hW hPT.le
    have hApos : 0 < (∏ p ∈ T, (p : ℚ)) * ((pj : ℚ) + 1) ^ m := by
      rw [← hA]
      have : 0 < ∏ p ∈ T, ((p : ℚ) - 1) := by
        apply prod_pos
        intro p hp
        have : (1 : ℚ) < p := by exact_mod_cast (h2 p (hs.sub hp))
        linarith
      positivity
    have : 1 / (P T * φ n) ≤ 1 / ((∏ p ∈ T, (p : ℚ)) * ((pj : ℚ) + 1) ^ m) :=
      one_div_le_one_div_of_le hApos hle
    linarith
  · have : 0 < 1 / (P T * φ n) := by positivity
    linarith

/-! ### Proposition 3.5 -/

/-- Proposition 3.5: if `A p q + ε = 2 B (p - 1)(q - 1)` with `B ≥ 1`, `p ≥ 2`, `q ≥ 1`, then
`t = C p - 2 B > 0`, `t (q - 1) = A p + ε` and `(C p - 2 B)(C q - 2 B) = 2 A B + ε C`, where
`C = 2 B - A`. -/
theorem last_two {A B p q ε : ℤ} (hε : IsSign ε) (hB : 1 ≤ B) (hp : 2 ≤ p) (hq : 1 ≤ q)
    (h : A * p * q + ε = 2 * B * (p - 1) * (q - 1)) :
    0 < (2 * B - A) * p - 2 * B ∧ ((2 * B - A) * p - 2 * B) * (q - 1) = A * p + ε ∧
      ((2 * B - A) * p - 2 * B) * ((2 * B - A) * q - 2 * B) = 2 * A * B + ε * (2 * B - A) := by
  have hq' : q * ((2 * B - A) * p - 2 * B) = 2 * B * (p - 1) + ε := by linear_combination (-1) * h
  refine ⟨?_, by linear_combination (-1) * h, by linear_combination (-(2 * B - A)) * h⟩
  have hrhs : 0 < 2 * B * (p - 1) + ε := by
    rcases hε with rfl | rfl <;> nlinarith
  by_contra hneg
  push Not at hneg
  have : q * ((2 * B - A) * p - 2 * B) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) hneg
  linarith

/-- The converse direction of Proposition 3.5, used when the last two primes are read off from
a divisor: the identity `(C p - 2 B)(C q - 2 B) = 2 A B + ε C` with `C ≠ 0` gives back
`A p q + ε = 2 B (p - 1)(q - 1)`. -/
theorem last_two_converse {A B p q ε : ℤ} (hC : 2 * B - A ≠ 0)
    (h : ((2 * B - A) * p - 2 * B) * ((2 * B - A) * q - 2 * B) = 2 * A * B + ε * (2 * B - A)) :
    A * p * q + ε = 2 * B * (p - 1) * (q - 1) := by
  have : (2 * B - A) * (A * p * q + ε - 2 * B * (p - 1) * (q - 1)) = 0 := by
    linear_combination (-1) * h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hC
  · linarith

/-- The form of Proposition 3.5 used for the checks of Appendix A.4: if
`b (A p q + ε) = a B (p - 1)(q - 1)` and `C = a B - b A`, then
`(C p - a B)(C q - a B) = b (a A B + ε C)`. -/
theorem last_two_general {a b A B p q ε : ℤ}
    (h : b * (A * p * q + ε) = a * B * (p - 1) * (q - 1)) :
    ((a * B - b * A) * p - a * B) * ((a * B - b * A) * q - a * B) =
      b * (a * A * B + ε * (a * B - b * A)) := by
  linear_combination (-(a * B - b * A)) * h

end LehmerTotient
