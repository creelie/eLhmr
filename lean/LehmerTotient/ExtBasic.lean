import LehmerTotient.Basic

/-!
# Extensions of Fermat-type solutions (Theorem 1.6 (i), (ii))

A Fermat-type solution is an `n` with `n + 1 = 2 φ(n)`.

* `fermatType_mul_iff`: equation (7.1).
* `one_prime_ext`: Theorem 1.6 (i).
* `two_prime_ext`, `two_prime_ext_pos`, `two_prime_ext_of_factor`: Theorem 1.6 (ii).
* `lucas_cert`: a Lucas primality certificate whose hypotheses the kernel checks by `decide`.
* `mem_subprods_of_dvd`: the divisors of a product of primes are its subproducts.
* `pseudo_solution`, `pseudo_solution_prune`: Proposition 9.1. Every Fermat-type `n₀` with prime
  factors `p₁, …, p_m` gives the tuple `(p₁, …, p_m, n₀)` of integers with
  `x₁ ⋯ x_{m+1} - 1 = 2 ∏ (xᵢ - 1)` that passes the congruence prune.
* `three_prime_ext`, `three_prime_identity`: Remark 7.1.
-/

namespace LehmerTotient

open Nat

/-- `n` is a Fermat-type solution: `n + 1 = 2 φ(n)`. -/
def FermatType (n : ℕ) : Prop := 2 * φ n = n + 1

lemma FermatType.pos {n : ℕ} (h : FermatType n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [FermatType] at h
  · exact hn

/-- Equation (6.1): for `Q` prime to a Fermat-type `n₀`, `n₀ Q` is Fermat-type if and only if
`n₀ (Q - φ Q) = φ Q - 1`. -/
theorem fermatType_mul_iff {n0 Q : ℕ} (h0 : FermatType n0) (hcop : Coprime n0 Q) :
    FermatType (n0 * Q) ↔ (n0 : ℤ) * (Q - φ Q) = φ Q - 1 := by
  unfold FermatType at *
  rw [totient_mul hcop]
  have h0' : (2 * φ n0 : ℤ) = n0 + 1 := by exact_mod_cast h0
  constructor
  · intro h
    have h' : (2 * (φ n0 * φ Q) : ℤ) = n0 * Q + 1 := by exact_mod_cast h
    linear_combination -h' + (φ Q : ℤ) * h0'
  · intro h
    have : (2 * (φ n0 * φ Q) : ℤ) = n0 * Q + 1 := by
      linear_combination -h + (φ Q : ℤ) * h0'
    exact_mod_cast this

/-- Theorem 1.6 (i). -/
theorem one_prime_ext {n0 q : ℕ} (h0 : FermatType n0) (hq : q.Prime) (hqn : ¬ q ∣ n0) :
    FermatType (n0 * q) ↔ q = n0 + 2 := by
  have hcop : Coprime n0 q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn).symm
  rw [fermatType_mul_iff h0 hcop, totient_prime hq]
  have h1 : ((q - 1 : ℕ) : ℤ) = q - 1 := by rw [Nat.cast_sub hq.one_lt.le]; simp
  rw [h1]
  constructor
  · intro h
    have : (q : ℤ) = n0 + 2 := by linear_combination -h
    exact_mod_cast this
  · intro h
    subst h
    push_cast
    ring

/-- Theorem 1.6 (ii): the equation for two new primes. -/
theorem two_prime_ext {n0 p q : ℕ} (h0 : FermatType n0) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hpn : ¬ p ∣ n0) (hqn : ¬ q ∣ n0) :
    FermatType (n0 * p * q) ↔ ((p : ℤ) - n0 - 1) * ((q : ℤ) - n0 - 1) = n0 ^ 2 + n0 + 1 := by
  have hcop_pq : Coprime p q := (Nat.coprime_primes hp hq).mpr hpq.ne
  have hcop : Coprime n0 (p * q) :=
    Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm
      ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn).symm
  rw [mul_assoc, fermatType_mul_iff h0 hcop, totient_mul hcop_pq, totient_prime hp,
    totient_prime hq]
  have h1 : ((p - 1 : ℕ) : ℤ) = p - 1 := by rw [Nat.cast_sub hp.one_lt.le]; simp
  have h2 : ((q - 1 : ℕ) : ℤ) = q - 1 := by rw [Nat.cast_sub hq.one_lt.le]; simp
  push_cast [h1, h2]
  constructor <;> intro h <;> linear_combination -h

/-- Both factors in Theorem 1.6 (ii) are positive. -/
theorem two_prime_ext_pos {n0 p q : ℕ} (hn0 : 1 ≤ n0) (hp : 2 ≤ p) (hpq : p < q)
    (h : ((p : ℤ) - n0 - 1) * ((q : ℤ) - n0 - 1) = n0 ^ 2 + n0 + 1) :
    n0 + 1 < p ∧ n0 + 1 < q := by
  have hn : (1 : ℤ) ≤ n0 := by exact_mod_cast hn0
  have hp' : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hpq' : (p : ℤ) + 1 ≤ q := by exact_mod_cast hpq
  have key : (n0 : ℤ) + 1 < p := by
    by_contra hc
    push Not at hc
    -- then `q - n₀ - 1 < 0` as well, and the product is at most `(n₀ - 1)(n₀ - 2)`
    have hq0 : (q : ℤ) - n0 - 1 < 0 := by
      by_contra hc2
      push Not at hc2
      nlinarith
    nlinarith
  constructor
  · exact_mod_cast key
  · have : (n0 : ℤ) + 1 < q := by linarith
    exact_mod_cast this

/-- The converse of Theorem 1.6 (ii): a factorisation `n₀² + n₀ + 1 = d e` with both
`n₀ + 1 + d` and `n₀ + 1 + e` prime gives a Fermat-type solution. -/
theorem two_prime_ext_of_factor {n0 d e : ℕ} (h0 : FermatType n0) (hde : d * e = n0 ^ 2 + n0 + 1)
    (hlt : d < e) (hp : (n0 + 1 + d).Prime) (hq : (n0 + 1 + e).Prime) :
    FermatType (n0 * (n0 + 1 + d) * (n0 + 1 + e)) := by
  have hn0 := h0.pos
  have hnd : ¬ (n0 + 1 + d) ∣ n0 := Nat.not_dvd_of_pos_of_lt hn0 (by omega)
  have hne : ¬ (n0 + 1 + e) ∣ n0 := Nat.not_dvd_of_pos_of_lt hn0 (by omega)
  rw [two_prime_ext h0 hp hq (by omega) hnd hne]
  push_cast
  have : ((d * e : ℕ) : ℤ) = ((n0 ^ 2 + n0 + 1 : ℕ) : ℤ) := by rw [hde]
  push_cast at this
  linear_combination this

/-! ### Primality certificates -/

lemma prime_dvd_prod_pow {q : ℕ} (hq : q.Prime) : ∀ fs : List (ℕ × ℕ), (∀ x ∈ fs, x.1.Prime) →
    q ∣ (fs.map fun x => x.1 ^ x.2).prod → ∃ x ∈ fs, q = x.1
  | [], _, h => by
    simp only [List.map_nil, List.prod_nil, Nat.dvd_one] at h
    exact absurd h hq.one_lt.ne'
  | x :: fs, hfs, h => by
    simp only [List.map_cons, List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
    · exact ⟨x, List.mem_cons_self,
        (Nat.prime_dvd_prime_iff_eq hq (hfs x List.mem_cons_self)).mp (hq.dvd_of_dvd_pow h1)⟩
    · obtain ⟨y, hy, rfl⟩ :=
        prime_dvd_prod_pow hq fs (fun y hy => hfs y (List.mem_cons_of_mem _ hy)) h1
      exact ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

/-- `powModAux f a b m r = r a ^ b mod m`, computed by repeated squaring when `b < 2 ^ f`. -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m, r => r % m
  | f + 1, a, b, m, r =>
    if b = 0 then r % m
    else powModAux f (a * a % m) (b / 2) m (if b % 2 = 1 then r * a % m else r)

theorem powModAux_spec : ∀ f a b m r, b < 2 ^ f → powModAux f a b m r = r * a ^ b % m
  | 0, a, b, m, r, hb => by
    have : b = 0 := by simp at hb; omega
    subst this
    simp [powModAux]
  | f + 1, a, b, m, r, hb => by
    rw [powModAux]
    by_cases h0 : b = 0
    · subst h0
      simp
    · rw [ite_eq_right h0, powModAux_spec f _ _ _ _ (by rw [pow_succ] at hb; omega)]
      have e2 : (a * a % m) ^ (b / 2) ≡ (a * a) ^ (b / 2) [MOD m] := (Nat.mod_modEq _ _).pow _
      by_cases h1 : b % 2 = 1
      · rw [ite_eq_left h1]
        have key := (Nat.mod_modEq (r * a) m).mul e2
        have hb2 : b = 2 * (b / 2) + 1 := by omega
        have e : r * a ^ b = r * a * (a * a) ^ (b / 2) := by
          conv_lhs => rw [hb2]
          ring
        rw [e]
        exact key
      · rw [ite_eq_right h1]
        have key := (Nat.ModEq.refl r).mul e2
        have hb2 : b = 2 * (b / 2) := by omega
        have e : r * a ^ b = r * (a * a) ^ (b / 2) := by
          conv_lhs => rw [hb2]
          ring
        rw [e]
        exact key

/-- A Lucas certificate: `p - 1 = ∏ qᵢ ^ eᵢ` with primes `qᵢ`, `a ^ (p - 1) ≡ 1` and
`a ^ ((p - 1) / qᵢ) ≢ 1 (mod p)` for every `i`.  The powers are computed by `powModAux`, so
that the kernel can check them. -/
theorem lucas_cert (p a : ℕ) (fs : List (ℕ × ℕ)) (hp : 2 ≤ p) (hp64 : p < 2 ^ 70)
    (hfs : ∀ x ∈ fs, x.1.Prime) (hfac : p - 1 = (fs.map fun x => x.1 ^ x.2).prod)
    (ha : powModAux 70 a (p - 1) p 1 = 1)
    (hq : ∀ x ∈ fs, powModAux 70 a ((p - 1) / x.1) p 1 ≠ 1) : p.Prime := by
  rw [powModAux_spec _ _ _ _ _ (by omega), one_mul] at ha
  apply lucas_primality p (a : ZMod p)
  · rw [← Nat.cast_pow, ← ZMod.natCast_mod, ha, Nat.cast_one]
  · intro q hq' hqd
    rw [hfac] at hqd
    obtain ⟨x, hx, rfl⟩ := prime_dvd_prod_pow hq' fs hfs hqd
    intro h
    apply hq x hx
    rw [powModAux_spec _ _ _ _ _ (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)), one_mul]
    have h1 : ((a ^ ((p - 1) / x.1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      push_cast
      exact h
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    rw [h1, Nat.mod_eq_of_lt (by omega)]

/-! ### Divisors of a product of primes -/

/-- The products of the sublists of a list. -/
def subprods : List ℕ → List ℕ
  | [] => [1]
  | p :: ps => subprods ps ++ (subprods ps).map (p * ·)

theorem mem_subprods_of_dvd {d : ℕ} : ∀ ps : List ℕ, (∀ p ∈ ps, p.Prime) → d ∣ ps.prod →
    d ∈ subprods ps
  | [], _, h => by
    simp only [List.prod_nil, Nat.dvd_one] at h
    simp [subprods, h]
  | p :: ps, hps, h => by
    rw [List.prod_cons] at h
    obtain ⟨d1, d2, hd1, hd2, rfl⟩ := Nat.dvd_mul.mp h
    have hp := hps p List.mem_cons_self
    have ih := mem_subprods_of_dvd ps (fun q hq => hps q (List.mem_cons_of_mem p hq)) hd2
    rcases (Nat.dvd_prime hp).mp hd1 with rfl | rfl
    · simp [subprods, ih]
    · simp only [subprods, List.mem_append, List.mem_map]
      exact Or.inr ⟨d2, ih, rfl⟩

/-! ### Pseudo-solutions (Proposition 9.1) -/

/-- Proposition 9.1: every Fermat-type `n₀ = p₁ ⋯ p_m` gives the integers `(p₁, …, p_m, n₀)`,
which satisfy Lehmer's product equation (9.1), `x₁ ⋯ x_{m+1} - 1 = 2 ∏ (xᵢ - 1)`, although `n₀` is
not prime. -/
theorem pseudo_solution {n0 : ℕ} (h0 : FermatType n0) (hsq : Squarefree n0) :
    ((n0 * n0 : ℕ) : ℤ) - 1 = 2 * (∏ p ∈ n0.primeFactors, ((p : ℤ) - 1)) * ((n0 : ℤ) - 1) := by
  have hφ : (φ n0 : ℤ) = ∏ p ∈ n0.primeFactors, ((p : ℤ) - 1) := by
    have := totient_mul_prod_primeFactors n0
    rw [prod_primeFactors_of_squarefree hsq] at this
    have hn : 0 < n0 := h0.pos
    have e : φ n0 = ∏ p ∈ n0.primeFactors, (p - 1) := by
      rw [mul_comm] at this
      exact Nat.eq_of_mul_eq_mul_left hn this
    rw [e, Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le]
    simp
  rw [← hφ]
  have h0' : (2 * φ n0 : ℤ) = n0 + 1 := by exact_mod_cast h0
  push_cast
  linear_combination (-(n0 : ℤ) + 1) * h0'

/-- The integers `(p₁, …, p_m, n₀)` of `pseudo_solution` also pass the congruence prune:
no `pᵢ` divides `n₀ - 1`, and `n₀` is prime to every `pᵢ - 1`. -/
theorem pseudo_solution_prune {n0 p : ℕ} (h0 : FermatType n0) (hp : p ∈ n0.primeFactors) :
    Nat.Coprime p (n0 - 1) ∧ Nat.Coprime n0 (p - 1) := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  have hn := h0.pos
  have hdvd : (φ n0 : ℤ) ∣ n0 + 1 := by
    have e : ((2 * φ n0 : ℕ) : ℤ) = ((n0 + 1 : ℕ) : ℤ) := by rw [show 2 * φ n0 = n0 + 1 from h0]
    push_cast at e
    exact ⟨2, by linarith⟩
  refine ⟨(Nat.Prime.coprime_iff_not_dvd hpp).mpr fun h => ?_, ?_⟩
  · have h1 : p ∣ n0 - (n0 - 1) := Nat.dvd_sub hpn h
    rw [show n0 - (n0 - 1) = 1 by omega] at h1
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
  · exact Nat.coprime_of_dvd fun r hr hrn =>
      prime_not_dvd_sub_one (ε := 1) (Or.inl rfl) hdvd hr hpp hrn hpn

/-! ### Three new primes (Remark 7.1) -/

/-- For three new primes `s < p < q`, with `x = s - 1`, `y = p - 1`, `z = q - 1`, equation (7.1)
reads `x y z = n₀ (x y + y z + z x) + n₀ (x + y + z) + n₀ + 1`. -/
theorem three_prime_ext {n0 s p q : ℕ} (h0 : FermatType n0) (hs : s.Prime) (hp : p.Prime)
    (hq : q.Prime) (hsp : s < p) (hpq : p < q) (hsn : ¬ s ∣ n0) (hpn : ¬ p ∣ n0)
    (hqn : ¬ q ∣ n0) :
    FermatType (n0 * (s * p * q)) ↔
      ((s : ℤ) - 1) * (p - 1) * (q - 1) =
        n0 * ((s - 1) * (p - 1) + (p - 1) * (q - 1) + (q - 1) * (s - 1)) +
          n0 * ((s - 1) + (p - 1) + (q - 1)) + n0 + 1 := by
  have hsp' : Coprime s p := (Nat.coprime_primes hs hp).mpr hsp.ne
  have hsq' : Coprime s q := (Nat.coprime_primes hs hq).mpr (hsp.trans hpq).ne
  have hpq' : Coprime p q := (Nat.coprime_primes hp hq).mpr hpq.ne
  have c1 := ((Nat.Prime.coprime_iff_not_dvd hs).mpr hsn).symm
  have c2 := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm
  have c3 := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn).symm
  have hcop : Coprime n0 (s * p * q) := (c1.mul_right c2).mul_right c3
  rw [fermatType_mul_iff h0 hcop, totient_mul (Nat.coprime_mul_iff_left.mpr ⟨hsq', hpq'⟩),
    totient_mul hsp', totient_prime hs, totient_prime hp, totient_prime hq]
  have h1 : ((s - 1 : ℕ) : ℤ) = s - 1 := by rw [Nat.cast_sub hs.one_lt.le]; simp
  have h2 : ((p - 1 : ℕ) : ℤ) = p - 1 := by rw [Nat.cast_sub hp.one_lt.le]; simp
  have h3 : ((q - 1 : ℕ) : ℤ) = q - 1 := by rw [Nat.cast_sub hq.one_lt.le]; simp
  push_cast [h1, h2, h3]
  constructor <;> intro h <;> linear_combination -h

/-- Remark 7.1: for fixed `x` the equation is bilinear in `y` and `z`. -/
theorem three_prime_identity {n0 x y z : ℤ}
    (h : x * y * z = n0 * (x * y + y * z + z * x) + n0 * (x + y + z) + n0 + 1) :
    ((x - n0) * y - n0 * (x + 1)) * ((x - n0) * z - n0 * (x + 1)) =
      (x - n0) * (n0 * x + n0 + 1) + n0 ^ 2 * (x + 1) ^ 2 := by
  linear_combination (x - n0) * h

end LehmerTotient
