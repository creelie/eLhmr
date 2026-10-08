import LehmerTotient.Three
import LehmerTotient.Thresholds
import LehmerTotient.Barrier

/-!
# Eight prime factors (Section 7.4 of the paper)

* `eight_reduction`: a solution of `φ n ∣ n + 1` with eight prime factors and `3 ∣ n` satisfies
  `n + 1 = 2 φ n`, and its least prime factor is `3`.
* `trial_identity`, `trial_dvd_iff`: step (i). `c (A' p + ε) = A' t + N`, so `t ∣ A' p + ε` if and only if
  `t ∣ N` when `t` is prime to `c`.
* `sigma_identities`, `sigma_class`, `sigma_range`, `sigma_converse`: step (ii). Equation (6.2), the class of
  `σ` modulo `c`, the range of `c σ`, and the converse that turns a square `σ ^ 2 - 4 π` into a completion.
* `sieve_keeps`, `eight_kept`, `int_kept`: step (iii). The sieve keeps every value that comes from integers
  `p, q` avoiding the excluded residues; for eight primes this holds when `p` and `q` have no prime factor up
  to `61`, and in the mode for odd integers prime to `3` (Theorem 9.3) for every completion.
* `fermat_prefix`: for the prefix `3, 5, 17, 257, 65537` the modulus is `c = s - 2 ^ 32`.

All statements are in `ℤ`, with `c = 2 B' - A'`, `t = c p - 2 B'` and `N = 2 A' B' + ε c`.
-/

open Nat

namespace LehmerTotient

/-! ### The reduction to `n + 1 = 2 φ n` and `p₁ = 3` -/

/-- Section 7.4: a solution of `φ n ∣ n + 1` with eight prime factors and `3 ∣ n` has quotient `2`, and
`3` is its least prime factor. -/
theorem eight_reduction {n : ℕ} {M : ℤ} (hn : 3 < n) (hM : (n : ℤ) + 1 = M * φ n)
    (h8 : n.primeFactors.card = 8) (h3 : 3 ∣ n) :
    M = 2 ∧ 3 ∈ n.primeFactors ∧ ∀ p ∈ n.primeFactors, 3 ≤ p := by
  have hdvd : (φ n : ℤ) ∣ n + 1 := ⟨M, by rw [hM]; ring⟩
  have hε : IsSign 1 := Or.inl rfl
  have hc := not_prime_of_dvd_add_one hdvd hn
  have h2M := two_le_quotient hε (by omega) hc hM
  have hM2 : M = 2 := by
    by_contra hne
    have h3M : 3 ≤ M := by omega
    have := (theorem_quotient hn hM h3M).2 h3
    omega
  have hodd := odd_of_dvd hε hdvd (by omega)
  refine ⟨hM2, Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, by omega⟩, ?_⟩
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  have h2 := hpp.two_le
  by_contra hlt
  have hp2 : p = 2 := by omega
  rw [hp2] at hpn
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn)

/-! ### Step (i): trial division -/

/-- The identity of step (i): `c (A' p + ε) = A' t + N`. -/
theorem trial_identity (A' B' p ε : ℤ) :
    (2 * B' - A') * (A' * p + ε) =
      A' * ((2 * B' - A') * p - 2 * B') + (2 * A' * B' + ε * (2 * B' - A')) := by
  ring

/-- Step (i): if `t` is prime to `c`, then `t ∣ A' p + ε` if and only if `t ∣ N`. -/
theorem trial_dvd_iff {A' B' p ε : ℤ}
    (hcop : IsCoprime ((2 * B' - A') * p - 2 * B') (2 * B' - A')) :
    (2 * B' - A') * p - 2 * B' ∣ A' * p + ε ↔
      (2 * B' - A') * p - 2 * B' ∣ 2 * A' * B' + ε * (2 * B' - A') := by
  have key := trial_identity A' B' p ε
  constructor
  · intro h
    have h1 : (2 * B' - A') * p - 2 * B' ∣ (2 * B' - A') * (A' * p + ε) :=
      dvd_mul_of_dvd_right h _
    rw [key] at h1
    exact (dvd_add_right (dvd_mul_left _ A')).mp h1
  · intro h
    have h1 : (2 * B' - A') * p - 2 * B' ∣ (2 * B' - A') * (A' * p + ε) := by
      rw [key]
      exact dvd_add (dvd_mul_left _ A') h
    exact hcop.dvd_of_dvd_mul_left h1

/-! ### Step (ii): the sum and the product -/

/-- Equation (6.2): with `σ = p + q` and `π = p q`, `c π = 2 B' σ - 2 B' + ε` and
`(q - p) ^ 2 = σ ^ 2 - 4 π`; moreover `t + u = c σ - 4 B'` for the two divisors `t = c p - 2 B'` and
`u = c q - 2 B'`. -/
theorem sigma_identities {A' B' p q ε : ℤ} (h : A' * p * q + ε = 2 * B' * (p - 1) * (q - 1)) :
    (2 * B' - A') * (p * q) = 2 * B' * (p + q) - 2 * B' + ε ∧
      (q - p) ^ 2 = (p + q) ^ 2 - 4 * (p * q) ∧
      ((2 * B' - A') * p - 2 * B') + ((2 * B' - A') * q - 2 * B') =
        (2 * B' - A') * (p + q) - 4 * B' :=
  ⟨by linear_combination (-1 : ℤ) * h, by ring, by ring⟩

/-- The class of `σ` modulo `c`: `2 B' σ ≡ 2 B' - ε`. -/
theorem sigma_class {A' B' p q ε : ℤ} (h : A' * p * q + ε = 2 * B' * (p - 1) * (q - 1)) :
    2 * B' * (p + q) ≡ 2 * B' - ε [ZMOD (2 * B' - A')] :=
  Int.modEq_iff_dvd.mpr ⟨-(p * q), by linear_combination (-1 : ℤ) * h⟩

/-- The range of the sum: if `t u = N` with `t_d ≤ t ≤ u`, then `4 N ≤ (t + u) ^ 2` and
`t_d (t + u) ≤ t_d ^ 2 + N`; for `t_d > 0` this says `2 √N ≤ t + u ≤ t_d + N / t_d`. -/
theorem sigma_range {N t u td : ℤ} (hN : t * u = N) (h1 : td ≤ t) (h2 : t ≤ u) :
    4 * N ≤ (t + u) ^ 2 ∧ td * (t + u) ≤ td ^ 2 + N := by
  constructor
  · nlinarith [sq_nonneg (t - u)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (h1.trans h2))]

/-- The converse of step (ii): if `c π = 2 B' σ - 2 B' + ε` and `σ ^ 2 - 4 π = e ^ 2` with `σ - e` even,
then `p = (σ - e) / 2` and `q = (σ + e) / 2` satisfy `A' p q + ε = 2 B' (p - 1)(q - 1)`. -/
theorem sigma_converse {A' B' σ π e ε : ℤ} (hcπ : (2 * B' - A') * π = 2 * B' * σ - 2 * B' + ε)
    (he : σ ^ 2 - 4 * π = e ^ 2) (hpar : Even (σ - e)) :
    A' * ((σ - e) / 2) * ((σ + e) / 2) + ε =
      2 * B' * ((σ - e) / 2 - 1) * ((σ + e) / 2 - 1) := by
  obtain ⟨k, hk⟩ := hpar
  have hp : (σ - e) / 2 = k := by rw [hk]; omega
  have hq : (σ + e) / 2 = k + e := by
    have : σ + e = 2 * (k + e) := by linarith
    rw [this]; omega
  rw [hp, hq]
  have hσ : σ = 2 * k + e := by linarith
  subst hσ
  have h4 : 4 * π = 4 * (k * (k + e)) := by linear_combination (-1 : ℤ) * he
  have hπ : π = k * (k + e) := by linarith
  subst hπ
  linear_combination (-1 : ℤ) * hcπ

/-! ### Step (iii): the sieve -/

/-- The residue `x` is excluded modulo the prime `ℓ`: the residue `0` when `ℓ ∈ Z`, the residue `1` when
`ℓ ∈ O`. -/
def Excluded (Z O : Finset ℕ) (ℓ : ℕ) (x : ℤ) : Prop :=
  (ℓ ∈ Z ∧ (ℓ : ℤ) ∣ x) ∨ (ℓ ∈ O ∧ (ℓ : ℤ) ∣ x - 1)

/-- Being excluded depends only on the residue. -/
lemma excluded_congr {Z O : Finset ℕ} {ℓ : ℕ} {x y : ℤ} (h : x ≡ y [ZMOD ℓ]) :
    Excluded Z O ℓ x ↔ Excluded Z O ℓ y := by
  have hd : (ℓ : ℤ) ∣ y - x := Int.ModEq.dvd h
  have h0 : (ℓ : ℤ) ∣ x ↔ (ℓ : ℤ) ∣ y := by
    constructor
    · intro hx
      have := dvd_add hx hd
      rwa [show x + (y - x) = y by ring] at this
    · intro hy
      have := dvd_sub hy hd
      rwa [show y - (y - x) = x by ring] at this
  have h1 : (ℓ : ℤ) ∣ x - 1 ↔ (ℓ : ℤ) ∣ y - 1 := by
    constructor
    · intro hx
      have := dvd_add hx hd
      rwa [show x - 1 + (y - x) = y - 1 by ring] at this
    · intro hy
      have := dvd_sub hy hd
      rwa [show y - 1 - (y - x) = x - 1 by ring] at this
  unfold Excluded
  rw [h0, h1]

/-- The sieve of the trial division: `p` is kept if it lies at no excluded residue modulo a prime
`ℓ ≤ 61`. -/
def TrialKept (Z O : Finset ℕ) (p : ℤ) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ 61 → ¬ Excluded Z O ℓ p

/-- The sieve of the sum: `σ` is kept if `σ ^ 2 - 4 π` is a square modulo `2 ^ 8`, `3 ^ 2`, `5 ^ 2` and
`7 ^ 2`, and if for every prime `ℓ ≤ 43` the polynomial `X ^ 2 - σ X + π` has a root modulo `ℓ` and no root
at an excluded residue. -/
def SumKept (Z O : Finset ℕ) (σ π : ℤ) : Prop :=
  (∀ m ∈ ({256, 9, 25, 49} : Finset ℤ), ∃ y : ℤ, y ^ 2 ≡ σ ^ 2 - 4 * π [ZMOD m]) ∧
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ 43 →
      (∃ x : ℤ, x ^ 2 - σ * x + π ≡ 0 [ZMOD ℓ]) ∧
        ∀ x : ℤ, x ^ 2 - σ * x + π ≡ 0 [ZMOD ℓ] → ¬ Excluded Z O ℓ x

/-- Step (iii): if `p` and `q` are kept by the sieve of the trial division, then `σ = p + q` is kept by
the sieve of the sum. Modulo a prime the roots of `X ^ 2 - σ X + π = (X - p)(X - q)` are `p` and `q`. -/
theorem sieve_keeps {Z O : Finset ℕ} {p q : ℤ} (hp : TrialKept Z O p) (hq : TrialKept Z O q) :
    SumKept Z O (p + q) (p * q) := by
  refine ⟨fun m _ => ⟨q - p, ?_⟩, fun ℓ hℓ hle => ⟨⟨p, ?_⟩, ?_⟩⟩
  · rw [show (p + q) ^ 2 - 4 * (p * q) = (q - p) ^ 2 by ring]
  · rw [show p ^ 2 - (p + q) * p + p * q = 0 by ring]
  · intro x hx
    have hd : (ℓ : ℤ) ∣ (x - p) * (x - q) := by
      have := Int.ModEq.dvd hx
      rw [show (0 : ℤ) - (x ^ 2 - (p + q) * x + p * q) = -((x - p) * (x - q)) by ring] at this
      exact (dvd_neg).mp this
    rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_or_dvd hd with h | h
    · have hxp : x ≡ p [ZMOD ℓ] := Int.modEq_iff_dvd.mpr (by
        have := dvd_neg.mpr h
        rwa [show -(x - p) = p - x by ring] at this)
      rw [excluded_congr hxp]
      exact hp ℓ hℓ (by omega)
    · have hxq : x ≡ q [ZMOD ℓ] := Int.modEq_iff_dvd.mpr (by
        have := dvd_neg.mpr h
        rwa [show -(x - q) = q - x by ring] at this)
      rw [excluded_congr hxq]
      exact hq ℓ hℓ (by omega)

/-- A prime of `A'` divides neither `p - 1` nor `q - 1`: it would divide `ε`. -/
theorem not_dvd_sub_one_of_dvd {A' B' p q ε : ℤ} (hε : IsSign ε)
    (h : A' * p * q + ε = 2 * B' * (p - 1) * (q - 1)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hA : (ℓ : ℤ) ∣ A') : ¬ (ℓ : ℤ) ∣ p - 1 ∧ ¬ (ℓ : ℤ) ∣ q - 1 := by
  have key : ∀ d : ℤ, d ∣ A' → (d ∣ p - 1 ∨ d ∣ q - 1) → d ∣ ε := by
    intro d hdA hd
    have e : ε = 2 * B' * (p - 1) * (q - 1) - A' * p * q := by linarith
    rw [e]
    refine dvd_sub ?_ (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdA _) _)
    rcases hd with hd | hd
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _
    · exact dvd_mul_of_dvd_right hd _
  exact ⟨fun h1 => not_dvd_sign hℓ hε (key _ hA (Or.inl h1)),
    fun h1 => not_dvd_sign hℓ hε (key _ hA (Or.inr h1))⟩

/-- A prime larger than `61` has no prime factor up to `61`. -/
theorem no_small_factor_of_prime {p : ℕ} (hp : p.Prime) (h61 : 61 < p) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ 61 → ¬ (ℓ : ℤ) ∣ (p : ℤ) := by
  intro ℓ hℓ hle hd
  have h1 : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (Int.natCast_dvd_natCast.mp hd)
  omega

/-- Step (iii) for eight primes: let `A' p q + ε = 2 B' (p - 1)(q - 1)`, let every prime of `O` divide `A'`,
and let `p` and `q` have no prime factor up to `61`. Then both sieves keep `p`, `q` and `σ = p + q`, whatever
the set `Z`. -/
theorem eight_kept {A' B' p q ε : ℤ} (hε : IsSign ε)
    (h : A' * p * q + ε = 2 * B' * (p - 1) * (q - 1)) {Z O : Finset ℕ}
    (hO : ∀ ℓ ∈ O, (ℓ : ℤ) ∣ A')
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ 61 → ¬ (ℓ : ℤ) ∣ p)
    (hq : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ 61 → ¬ (ℓ : ℤ) ∣ q) :
    TrialKept Z O p ∧ TrialKept Z O q ∧ SumKept Z O (p + q) (p * q) := by
  have hp' : TrialKept Z O p := by
    intro ℓ hℓ hle hex
    rcases hex with ⟨-, hd⟩ | ⟨hO', hd⟩
    · exact hp ℓ hℓ hle hd
    · exact (not_dvd_sub_one_of_dvd hε h hℓ (hO ℓ hO')).1 hd
  have hq' : TrialKept Z O q := by
    intro ℓ hℓ hle hex
    rcases hex with ⟨-, hd⟩ | ⟨hO', hd⟩
    · exact hq ℓ hℓ hle hd
    · exact (not_dvd_sub_one_of_dvd hε h hℓ (hO ℓ hO')).2 hd
  exact ⟨hp', hq', sieve_keeps hp' hq'⟩

/-- For the product equation with `ε = ±1`: a prime dividing some `x_i - 1` divides no entry, and a prime
dividing some entry divides no `x_j - 1`. -/
theorem int_not_excluded {k : ℕ} (x : Fin k → ℤ) (M ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (heq : ∏ i, x i + ε = M * ∏ i, (x i - 1)) {ℓ : ℕ} (hℓ : ℓ.Prime) (i j : Fin k) :
    ((ℓ : ℤ) ∣ x i - 1 → ¬ (ℓ : ℤ) ∣ x j) ∧ ((ℓ : ℤ) ∣ x i → ¬ (ℓ : ℤ) ∣ x j - 1) := by
  have hpr := Nat.prime_iff_prime_int.mp hℓ
  have g1 : IsCoprime (x j) (x i - 1) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (gcd_of_product_eq x M ε hε heq j i)
  have g2 : IsCoprime (x i) (x j - 1) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (gcd_of_product_eq x M ε hε heq i j)
  exact ⟨fun h1 h2 => hpr.not_isUnit (g1.isUnit_of_dvd' h2 h1),
    fun h1 h2 => hpr.not_isUnit (g2.isUnit_of_dvd' h1 h2)⟩

/-- Step (iii) in the mode for odd integers prime to `3` (Theorem 9.3): if the entries satisfy the product
equation, are odd and prime to `3`, the residue `0` is excluded only modulo `2`, `3` and primes dividing
`∏ (x_i - 1)`, and the residue `1` only modulo primes dividing `∏ x_i`, then every entry is kept by the sieve
of the trial division, and the sum of any two entries by the sieve of the sum. -/
theorem int_kept {k : ℕ} (x : Fin k → ℤ) (M ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (heq : ∏ i, x i + ε = M * ∏ i, (x i - 1)) {Z O : Finset ℕ}
    (hZ : ∀ ℓ ∈ Z, ℓ.Prime → ℓ = 2 ∨ ℓ = 3 ∨ (ℓ : ℤ) ∣ ∏ i, (x i - 1))
    (hO : ∀ ℓ ∈ O, ℓ.Prime → (ℓ : ℤ) ∣ ∏ i, x i)
    (h2 : ∀ j, ¬ (2 : ℤ) ∣ x j) (h3 : ∀ j, ¬ (3 : ℤ) ∣ x j) :
    (∀ j, TrialKept Z O (x j)) ∧ ∀ i j, SumKept Z O (x i + x j) (x i * x j) := by
  have hk : ∀ j, TrialKept Z O (x j) := by
    intro j ℓ hℓ _ hex
    have hpr := Nat.prime_iff_prime_int.mp hℓ
    rcases hex with ⟨hZ', hd⟩ | ⟨hO', hd⟩
    · rcases hZ ℓ hZ' hℓ with rfl | rfl | hdiv
      · exact h2 j (by exact_mod_cast hd)
      · exact h3 j (by exact_mod_cast hd)
      · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpr _).mp hdiv
        exact (int_not_excluded x M ε hε heq hℓ i j).1 hi hd
    · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpr _).mp (hO ℓ hO' hℓ)
      exact (int_not_excluded x M ε hε heq hℓ i j).2 hi hd
  exact ⟨hk, fun i j => sieve_keeps (hk i) (hk j)⟩

/-! ### The prefix `3, 5, 17, 257, 65537` -/

/-- For the prefix `3, 5, 17, 257, 65537`: `A = 2 ^ 32 - 1`, `B = 2 ^ 31`, and with `A' = A s`,
`B' = B (s - 1)` the modulus is `c = 2 B' - A' = s - 2 ^ 32`. -/
theorem fermat_prefix (s : ℤ) :
    (3 * 5 * 17 * 257 * 65537 : ℤ) = 2 ^ 32 - 1 ∧
      ((3 - 1) * (5 - 1) * (17 - 1) * (257 - 1) * (65537 - 1) : ℤ) = 2 ^ 31 ∧
      2 * (2 ^ 31 * (s - 1)) - (2 ^ 32 - 1) * s = s - 2 ^ 32 :=
  ⟨by norm_num, by norm_num, by ring⟩

end LehmerTotient
