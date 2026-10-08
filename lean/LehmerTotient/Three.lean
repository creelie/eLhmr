import LehmerTotient.Search

/-!
# The last three primes (Section 4 of the paper)

* `class_of_solution`, `solution_of_class`: Proposition 4.1 and its converse.
* `coset_of_divisor`, `box_bounds`, `window_of_modEq`: Lemma 4.2.
* `sum_identity`, `sum_converse`, `at_most_one_divisor`: Section 4.4.

All statements are in `ℤ`.  We write `c = 2 B' - A'` and `N = 2 A' B' + ε c`.
-/

namespace LehmerTotient

/-! ### Proposition 4.1 -/

/-- Proposition 4.1: the divisor `t = c p - 2 B'` of `N` lies in the class `-2 B'` modulo `c`,
satisfies `1 ≤ t` and `t ^ 2 ≤ N`; moreover `2 B'` is prime to `c` and `N ≡ (2 B') ^ 2`. -/
theorem class_of_solution {A' B' p q ε : ℤ} (hc : 1 ≤ 2 * B' - A')
    (hcop : IsCoprime (2 * B') A')
    (hN : ((2 * B' - A') * p - 2 * B') * ((2 * B' - A') * q - 2 * B')
      = 2 * A' * B' + ε * (2 * B' - A'))
    (ht : 0 < (2 * B' - A') * p - 2 * B') (hpq : p < q) :
    ((2 * B' - A') * p - 2 * B') ∣ 2 * A' * B' + ε * (2 * B' - A') ∧
      (2 * B' - A') * p - 2 * B' ≡ -2 * B' [ZMOD (2 * B' - A')] ∧
      ((2 * B' - A') * p - 2 * B') ^ 2 ≤ 2 * A' * B' + ε * (2 * B' - A') ∧
      IsCoprime (2 * B') (2 * B' - A') ∧
      2 * A' * B' + ε * (2 * B' - A') ≡ (2 * B') ^ 2 [ZMOD (2 * B' - A')] := by
  refine ⟨⟨_, hN.symm⟩, ?_, ?_, ?_, ?_⟩
  · exact Int.modEq_iff_dvd.mpr ⟨-p, by ring⟩
  · have hlt : (2 * B' - A') * p - 2 * B' < (2 * B' - A') * q - 2 * B' := by nlinarith
    rw [← hN, sq]
    exact mul_le_mul_of_nonneg_left hlt.le ht.le
  · have := hcop.neg_right.add_mul_left_right 1
    convert this using 1
    ring
  · exact Int.modEq_iff_dvd.mpr ⟨2 * B' - ε, by ring⟩

/-- The converse part of Proposition 4.1: a divisor `t` of `N` in the class `-2 B'` modulo `c`
gives integers `p, q` with `t = c p - 2 B'`, `(c q - 2 B') t = N` and
`A' p q + ε = 2 B' (p - 1)(q - 1)`. -/
theorem solution_of_class {A' B' ε t : ℤ} (hc : 1 ≤ 2 * B' - A')
    (hcop : IsCoprime (2 * B') (2 * B' - A'))
    (htN : t ∣ 2 * A' * B' + ε * (2 * B' - A')) (htr : t ≡ -2 * B' [ZMOD (2 * B' - A')]) :
    ∃ p q : ℤ, (2 * B' - A') * p - 2 * B' = t ∧
      ((2 * B' - A') * q - 2 * B') * t = 2 * A' * B' + ε * (2 * B' - A') ∧
      A' * p * q + ε = 2 * B' * (p - 1) * (q - 1) := by
  obtain ⟨s, hs⟩ := htN
  obtain ⟨p, hp⟩ : (2 * B' - A') ∣ t + 2 * B' := by
    have := Int.modEq_iff_dvd.mp htr.symm
    simpa [sub_neg_eq_add] using this
  -- the cofactor `s` lies in the same class: `c ∣ 2 B' (s + 2 B')`
  have h1 : (2 * B' - A') ∣ 2 * B' * (s + 2 * B') :=
    ⟨p * s - ε + 2 * B', by linear_combination hs + s * hp⟩
  obtain ⟨q, hq⟩ := hcop.symm.dvd_of_dvd_mul_left h1
  have hpt : (2 * B' - A') * p - 2 * B' = t := by linarith
  have hqs : (2 * B' - A') * q - 2 * B' = s := by linarith
  refine ⟨p, q, hpt, by rw [hqs, hs]; ring, ?_⟩
  apply last_two_converse (by omega)
  rw [hpt, hqs, hs]

/-! ### Lemma 4.2 -/

/-- The coset (4.2): if `c u v + r' u + r v = w` and `r ri ≡ 1 (mod c)`, then
`v ≡ α - β u` with `α = w ri` and `β = r' ri`. -/
theorem coset_of_divisor {c r r' ri u v w : ℤ} (hri : r * ri ≡ 1 [ZMOD c])
    (h : c * u * v + r' * u + r * v = w) : v ≡ w * ri - r' * ri * u [ZMOD c] := by
  have h1 : r * v ≡ w - r' * u [ZMOD c] :=
    Int.modEq_iff_dvd.mpr ⟨u * v, by linear_combination (-1 : ℤ) * h⟩
  have h3 : ri * (r * v) ≡ v [ZMOD c] := by
    have := hri.mul_right v
    calc ri * (r * v) = r * ri * v := by ring
      _ ≡ 1 * v [ZMOD c] := this
      _ = v := one_mul v
  calc v ≡ ri * (r * v) [ZMOD c] := h3.symm
    _ ≡ ri * (w - r' * u) [ZMOD c] := h1.mul_left ri
    _ = w * ri - r' * ri * u := by ring

/-- The two bounds of Lemma 4.2, with `⌊x / c⌋ = x / c` and `⌈x / c⌉ = -((-x) / c)` for
`c > 0`: `v⁻ ≤ v ≤ v⁺`. -/
theorem box_bounds {N c r r' u v u0 u1 : ℤ} (hc : 0 < c) (hr : 0 < r) (hu0 : 0 ≤ u0)
    (h0 : u0 ≤ u) (h1 : u ≤ u1) (hs : 0 ≤ r' + c * v)
    (hN : (r + c * u) * (r' + c * v) = N) :
    -((r' - (-((-N) / (r + c * u1)))) / c) ≤ v ∧ v ≤ (N / (r + c * u0) - r') / c := by
  have ht0 : 0 < r + c * u0 := by nlinarith
  have htt0 : r + c * u0 ≤ r + c * u := by nlinarith
  have htt1 : r + c * u ≤ r + c * u1 := by nlinarith
  constructor
  · have hceil : -((-N) / (r + c * u1)) ≤ r' + c * v := by
      have : -(r' + c * v) ≤ (-N) / (r + c * u1) := by
        apply Int.le_ediv_of_mul_le (by linarith)
        nlinarith
      linarith
    have : -v ≤ (r' - (-((-N) / (r + c * u1)))) / c := by
      apply Int.le_ediv_of_mul_le hc
      linarith
    linarith
  · have hfl : r' + c * v ≤ N / (r + c * u0) := by
      apply Int.le_ediv_of_mul_le ht0
      nlinarith
    apply Int.le_ediv_of_mul_le hc
    linarith

/-- The window of Lemma 4.2: if `x ≡ y (mod c)` with `0 ≤ y`, then `x mod c ≤ y`. Applied with
`x = α - β u - v⁻` and `y = v - v⁻ ≤ H - 1`. -/
theorem window_of_modEq {x y c : ℤ} (hc : 0 < c) (hy : 0 ≤ y) (h : x ≡ y [ZMOD c]) :
    x % c ≤ y := by
  have e : x % c = y % c := h
  rw [e]
  have h1 := Int.mul_ediv_add_emod y c
  have h2 : 0 ≤ y / c := Int.ediv_nonneg hy hc.le
  nlinarith

/-- Lemma 4.2 as used in the search: a divisor `t = r + c u` of `N` with `u₀ ≤ u ≤ u₁` has
`(α - β u - v⁻) mod c ≤ v⁺ - v⁻`, that is, `u` lies in the window (4.3) with `H = v⁺ - v⁻ + 1`. -/
theorem box {N c r ri u u0 u1 : ℤ} (hc : 0 < c) (hr : 0 < r) (hri : r * ri ≡ 1 [ZMOD c])
    (hu0 : 0 ≤ u0) (h0 : u0 ≤ u) (h1 : u ≤ u1) (hN0 : 0 ≤ N) (ht : (r + c * u) ∣ N) :
    let r' := N * ri % c
    let w := (N - r * r') / c
    let vp := (N / (r + c * u0) - r') / c
    let vm := -((r' - (-((-N) / (r + c * u1)))) / c)
    (w * ri - r' * ri * u - vm) % c ≤ vp - vm := by
  intro r' w vp vm
  obtain ⟨s, hs⟩ := ht
  have htpos : 0 < r + c * u := by nlinarith
  have hs0 : 0 ≤ s := by
    by_contra hneg
    push Not at hneg
    nlinarith
  -- `s ≡ r'`
  have hsr : s ≡ r' [ZMOD c] := by
    have e1 : r + c * u ≡ r [ZMOD c] := Int.modEq_iff_dvd.mpr ⟨-u, by ring⟩
    have e2 : ri * (r * s) ≡ ri * N [ZMOD c] := by
      have : r * s ≡ (r + c * u) * s [ZMOD c] := (e1.mul_right s).symm
      rw [← hs] at this
      exact this.mul_left ri
    have e3 : ri * (r * s) ≡ s [ZMOD c] := by
      calc ri * (r * s) = r * ri * s := by ring
        _ ≡ 1 * s [ZMOD c] := hri.mul_right s
        _ = s := one_mul s
    calc s ≡ ri * (r * s) [ZMOD c] := e3.symm
      _ ≡ ri * N [ZMOD c] := e2
      _ = N * ri := by ring
      _ ≡ N * ri % c [ZMOD c] := (Int.mod_modEq _ _).symm
  obtain ⟨v, hv⟩ : c ∣ s - r' := (Int.modEq_iff_dvd.mp hsr.symm)
  have hsv : s = r' + c * v := by linarith
  have hN : (r + c * u) * (r' + c * v) = N := by rw [← hsv, hs]
  have hw : c * w = N - r * r' := by
    have : c ∣ N - r * r' := ⟨u * r' + v * r + c * u * v, by rw [← hN]; ring⟩
    exact Int.mul_ediv_cancel' this
  have huv : c * u * v + r' * u + r * v = w := by
    have : c * (c * u * v + r' * u + r * v) = c * w := by rw [hw, ← hN]; ring
    exact mul_left_cancel₀ hc.ne' this
  have hcos := coset_of_divisor hri huv
  obtain ⟨hlo, hhi⟩ := box_bounds hc hr hu0 h0 h1 (by rw [← hsv]; exact hs0) hN
  have hwin := window_of_modEq hc (show 0 ≤ v - vm by linarith)
    ((hcos.symm.sub_right vm))
  linarith

/-! ### Section 4.4: the sum of the two factors -/

/-- Equation (4.4): with `N = r ^ 2 + c m`, `(r + c u)(r + c v) = N` if and only if
`c u v + r (u + v) = m`. -/
theorem sum_identity {N c r m u v : ℤ} (hc : c ≠ 0) (hm : N = r ^ 2 + c * m) :
    (r + c * u) * (r + c * v) = N ↔ c * u * v + r * (u + v) = m := by
  constructor
  · intro h
    have : c * (c * u * v + r * (u + v) - m) = 0 := by rw [hm] at h; linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hc
    · linarith
  · intro h
    rw [hm]
    linear_combination c * h

/-- The converse used by the sum route: if `c ∣ m - r S` and `S ^ 2 - 4 (m - r S) / c = e ^ 2`
with `S ≡ e (mod 2)`, then `u = (S - e) / 2`, `v = (S + e) / 2` give a factorisation. -/
theorem sum_converse {N c r m S e : ℤ} (hc : c ≠ 0) (hm : N = r ^ 2 + c * m)
    (hS : c ∣ m - r * S) (he : S ^ 2 - 4 * ((m - r * S) / c) = e ^ 2) (hpar : Even (S - e)) :
    (r + c * ((S - e) / 2)) * (r + c * ((S + e) / 2)) = N := by
  obtain ⟨P, hP⟩ := hS
  have hPc : (m - r * S) / c = P := by rw [hP]; exact Int.mul_ediv_cancel_left P hc
  rw [hPc] at he
  obtain ⟨k, hk⟩ := hpar
  have hu : (S - e) / 2 = k := by rw [hk]; omega
  have hv : (S + e) / 2 = k + e := by
    have : S + e = 2 * (k + e) := by linarith
    rw [this]; omega
  rw [hu, hv]
  apply (sum_identity hc hm).mpr
  -- `u + v = S` and `u v = P`
  have hS' : S = 2 * k + e := by linarith
  subst hS'
  have : c * (k * (k + e)) = c * P := by
    have : k * (k + e) = P := by nlinarith
    rw [this]
  nlinarith

/-- The cofactor of a divisor in the class `r` is again in the class `r` when `N ≡ r ^ 2` and
`r` is prime to `c`. -/
theorem cofactor_class {N c r t w : ℤ} (hcop : IsCoprime r c) (hN : N ≡ r ^ 2 [ZMOD c])
    (htw : t * w = N) (ht : t ≡ r [ZMOD c]) : w ≡ r [ZMOD c] := by
  have h1 : r * w ≡ r * r [ZMOD c] := by
    calc r * w ≡ t * w [ZMOD c] := (ht.mul_right w).symm
      _ = N := htw
      _ ≡ r ^ 2 [ZMOD c] := hN
      _ = r * r := sq r
  have h2 : c ∣ r * (r - w) := by
    rw [show r * (r - w) = r * r - r * w by ring]
    exact Int.modEq_iff_dvd.mp h1
  exact Int.modEq_iff_dvd.mpr (hcop.symm.dvd_of_dvd_mul_left h2)

/-- Section 4.4: two divisors `r + c ≤ t₁ < t₂` of `N`, both at most their cofactors and both
in the class `r` with `1 ≤ r < c`, force `c ^ 3 < N + 2 c ^ 2`. Hence if `c ^ 3 ≥ N + 2 c ^ 2`
the class contains at most one divisor `t ≤ √N` besides `t = r`. -/
theorem at_most_one_divisor {N c r t1 t2 w1 w2 : ℤ} (hc : 2 ≤ c) (hr1 : 1 ≤ r) (hrc : r < c)
    (hcop : IsCoprime r c) (hN : N ≡ r ^ 2 [ZMOD c])
    (h1 : t1 * w1 = N) (h2 : t2 * w2 = N) (ht1 : t1 ≡ r [ZMOD c]) (ht2 : t2 ≡ r [ZMOD c])
    (hlo : r + c ≤ t1) (h12 : t1 < t2) (hle1 : t1 ≤ w1) (hle2 : t2 ≤ w2) :
    c ^ 3 < N + 2 * c ^ 2 := by
  have hw1 := cofactor_class hcop hN h1 ht1
  have hw2 := cofactor_class hcop hN h2 ht2
  obtain ⟨a1, ha1⟩ := Int.modEq_iff_dvd.mp ht1.symm
  obtain ⟨a2, ha2⟩ := Int.modEq_iff_dvd.mp ht2.symm
  obtain ⟨b1, hb1⟩ := Int.modEq_iff_dvd.mp hw1.symm
  obtain ⟨b2, hb2⟩ := Int.modEq_iff_dvd.mp hw2.symm
  -- `t = r + c u`, `w = r + c v`; the sums `S = u + v` agree modulo `c`
  have hk : c ∣ (a1 + b1) - (a2 + b2) := by
    have e : r * ((a1 + b1) - (a2 + b2)) = c * (a2 * b2 - a1 * b1) := by
      have e1 : (r + c * a1) * (r + c * b1) = (r + c * a2) * (r + c * b2) := by
        rw [show r + c * a1 = t1 by linarith, show r + c * b1 = w1 by linarith,
          show r + c * a2 = t2 by linarith, show r + c * b2 = w2 by linarith, h1, h2]
      have : c * (r * ((a1 + b1) - (a2 + b2)) - c * (a2 * b2 - a1 * b1)) = 0 := by
        linear_combination e1
      rcases mul_eq_zero.mp this with h0 | h0
      · omega
      · linarith
    exact hcop.symm.dvd_of_dvd_mul_left ⟨_, e⟩
  obtain ⟨k, hk⟩ := hk
  have hd : (t1 + w1) - (t2 + w2) = c ^ 2 * k := by
    have : t1 + w1 = 2 * r + c * (a1 + b1) := by linarith
    have : t2 + w2 = 2 * r + c * (a2 + b2) := by linarith
    rw [sq]; linear_combination c * hk + (by linarith : t1 + w1 = 2 * r + c * (a1 + b1)) -
      (by linarith : t2 + w2 = 2 * r + c * (a2 + b2))
  -- the sum decreases: `t₁ t₂ (s₁ - s₂) = (t₂ - t₁)(N - t₁ t₂) > 0`
  have ht1pos : 0 < t1 := by linarith
  have hpos : 0 < (t1 + w1) - (t2 + w2) := by
    have hNt : t1 * t2 < N := by nlinarith
    have e : t1 * t2 * ((t1 + w1) - (t2 + w2)) = (t2 - t1) * (N - t1 * t2) := by
      linear_combination t2 * h1 - t1 * h2
    have : 0 < t1 * t2 * ((t1 + w1) - (t2 + w2)) := by rw [e]; nlinarith
    have ht12 : 0 < t1 * t2 := by nlinarith
    exact pos_of_mul_pos_right this ht12.le
  have hk1 : 1 ≤ k := by
    by_contra hcon
    push Not at hcon
    have : c ^ 2 * k ≤ 0 := by nlinarith
    linarith
  have hge : c ^ 2 ≤ (t1 + w1) - (t2 + w2) := by nlinarith
  have hs2 : 0 < t2 + w2 := by linarith
  have hs1 : (r + c) * (t1 + w1) ≤ (r + c) ^ 2 + N := by nlinarith
  have hmain : (r + c) * c ^ 2 < (r + c) ^ 2 + N := by nlinarith
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ r - 1 by linarith) (show (0 : ℤ) ≤ c - 1 - r by linarith)]

/-! ### The coprimality in Proposition 4.1 -/

/-- If `A' = ∏ p` over a set `T` of odd primes, `B' = ∏ (p - 1)`, and no `p ∈ T` divides `q - 1`
for `q ∈ T` (the congruence prune), then `2 B'` is prime to `A'`. -/
theorem coprime_of_prune {T : Finset ℕ} (hprime : ∀ p ∈ T, p.Prime) (hodd : ∀ p ∈ T, p ≠ 2)
    (hprune : ∀ p ∈ T, ∀ q ∈ T, ¬ p ∣ q - 1) :
    Nat.Coprime (2 * ∏ p ∈ T, (p - 1)) (∏ p ∈ T, p) := by
  apply Nat.Coprime.prod_right
  intro p hp
  have hpp := hprime p hp
  refine Nat.coprime_mul_iff_left.mpr ⟨?_, ?_⟩
  · exact (Nat.coprime_primes Nat.prime_two hpp).mpr (hodd p hp).symm
  · apply Nat.Coprime.prod_left
    intro q hq
    exact ((Nat.Prime.coprime_iff_not_dvd hpp).mpr (hprune p hp q hq)).symm

/-- The same statement over `ℤ`, in the form used by `class_of_solution`. -/
theorem isCoprime_of_prune {T : Finset ℕ} (hprime : ∀ p ∈ T, p.Prime) (hodd : ∀ p ∈ T, p ≠ 2)
    (hprune : ∀ p ∈ T, ∀ q ∈ T, ¬ p ∣ q - 1) :
    IsCoprime (2 * ((∏ p ∈ T, (p - 1) : ℕ) : ℤ)) ((∏ p ∈ T, p : ℕ) : ℤ) := by
  have := coprime_of_prune hprime hodd hprune
  rw [← Nat.isCoprime_iff_coprime] at this
  exact_mod_cast this

end LehmerTotient
