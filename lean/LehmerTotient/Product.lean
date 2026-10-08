import LehmerTotient.Imports
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# A sharp product lemma and light solutions (Sections 6.1 and 6.2)

For `m ≥ 1` and real `y` put `E_m(y) = y ^ 2 ^ m - y ^ 2 ^ (m - 1)`. Sequences are indexed from `0`, so the paper's
`x₁ ≤ ⋯ ≤ x_m` is `x 0 ≤ ⋯ ≤ x (m - 1)`, and `X_u = x 0 ⋯ x (u - 1)`, `Y_u = (x 0 - 1) ⋯ (x (u - 1) - 1)`.

* `E_comp`, `E_mono`: the identity (6.1) `E_m(y ^ 2 ^ u) = E_{m+u}(y)` and monotonicity on `y ≥ 1`.
* `tail`: Lemma 6.3.
* `major`: Lemma 6.4, the majorisation inequality, with its strict form.
* `cn_mul_prod`, `cn_mul_prod_all`, `cn_prod_one_sub`: the extremal sequence of Lemma 6.5 and the identity (6.3).
* `cook_nielsen`: Lemma 6.5 (Cook, Nielsen), `a X_m ≤ E_m(a + 1)`.
* `deficit`, `deficit_attained`: Theorem 6.2, `a X_m ≤ E_{m-1}(b (a + 1) / (b - a))`, with equality for a suitable
  sequence when `b - a ∣ b + 1`.
* `size_bounds`: Proposition 6.8, `n < (A_j + 1) ^ 2 ^ (k - j)` and `n < V_j ^ 2 ^ (k - j - 1)`.
* `light`: Corollary 6.10, a solution that is not `s`-heavy (Definition 6.9) satisfies `n < 2 ^ 2 ^ (k - s)`.

Proposition 6.8 and Corollary 6.10 are stated for integers `2 ≤ p 0 ≤ ⋯ ≤ p (k - 1)` with
`p 0 ⋯ p (k - 1) = M ∏ (p i - 1) + 1` and `M ≥ 2`, which every composite solution of (1.1) satisfies.
-/

namespace LehmerTotient.Product

open Finset

/-- `E_m(y) = y ^ 2 ^ m - y ^ 2 ^ (m - 1)`. -/
noncomputable def E (m : ℕ) (y : ℝ) : ℝ := y ^ 2 ^ m - y ^ 2 ^ (m - 1)

lemma E_eq {m : ℕ} (hm : 1 ≤ m) (y : ℝ) : E m y = y ^ 2 ^ (m - 1) * (y ^ 2 ^ (m - 1) - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  unfold E
  rw [Nat.add_sub_cancel, pow_succ, pow_mul]
  ring

/-- The identity (6.1): `E_m(y ^ 2 ^ u) = E_{m+u}(y)`. -/
lemma E_comp {m : ℕ} (hm : 1 ≤ m) (u : ℕ) (y : ℝ) : E m (y ^ 2 ^ u) = E (m + u) y := by
  unfold E
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  have : m + u - 1 = m - 1 + u := by omega
  rw [this, add_comm u m, add_comm u (m - 1)]

/-- `E_m` is increasing on `y ≥ 1`. -/
lemma E_mono {m : ℕ} (hm : 1 ≤ m) {y y' : ℝ} (hy : 1 ≤ y) (h : y ≤ y') : E m y ≤ E m y' := by
  rw [E_eq hm, E_eq hm]
  have h1 : 1 ≤ y ^ 2 ^ (m - 1) := one_le_pow₀ hy
  have h2 : y ^ 2 ^ (m - 1) ≤ y' ^ 2 ^ (m - 1) := pow_le_pow_left₀ (by linarith) h _
  nlinarith

/-! ### Lemma 6.3 -/

/-- `X_u = x 0 ⋯ x (u - 1)`. -/
def X (x : ℕ → ℕ) (u : ℕ) : ℕ := ∏ i ∈ range u, x i

/-- `Y_u = (x 0 - 1) ⋯ (x (u - 1) - 1)`. -/
def Y (x : ℕ → ℕ) (u : ℕ) : ℕ := ∏ i ∈ range u, (x i - 1)

/-- The hypothesis (6.2), `∏_{i<m} (1 - 1/xᵢ) ≤ a/b < ∏_{i<m-1} (1 - 1/xᵢ)`, cleared of denominators. -/
def Hyp (a b : ℕ) (x : ℕ → ℕ) (m : ℕ) : Prop :=
  b * Y x m ≤ a * X x m ∧ a * X x (m - 1) < b * Y x (m - 1)

lemma X_add (x : ℕ → ℕ) (u v : ℕ) : X x (u + v) = X x u * X (fun i => x (u + i)) v := by
  simp only [X, prod_range_add]

lemma Y_add (x : ℕ → ℕ) (u v : ℕ) : Y x (u + v) = Y x u * Y (fun i => x (u + i)) v := by
  simp only [Y, prod_range_add]

lemma X_succ (x : ℕ → ℕ) (u : ℕ) : X x (u + 1) = X x u * x u := by simp only [X, prod_range_succ]

lemma Y_succ (x : ℕ → ℕ) (u : ℕ) : Y x (u + 1) = Y x u * (x u - 1) := by simp only [Y, prod_range_succ]

lemma Y_le_X (x : ℕ → ℕ) (u : ℕ) : Y x u ≤ X x u :=
  Finset.prod_le_prod fun _ _ => Nat.sub_le _ _

lemma X_pos {x : ℕ → ℕ} {m : ℕ} (hx : ∀ i < m, 2 ≤ x i) {u : ℕ} (hu : u ≤ m) : 0 < X x u :=
  prod_pos (fun i hi => by have := hx i (by simp at hi; omega); omega)

/-- `∏_{i<u} (1 - 1/xᵢ) = Y_u / X_u` for entries at least `1`. -/
lemma prod_one_sub {x : ℕ → ℕ} {u : ℕ} (hx : ∀ i < u, 1 ≤ x i) :
    ∏ i ∈ range u, (1 - 1 / (x i : ℝ)) = (Y x u : ℝ) / X x u := by
  rw [Y, X, Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
  refine prod_congr rfl (fun i hi => ?_)
  have h := hx i (by simpa using hi)
  rw [Nat.cast_sub h, Nat.cast_one]
  have : (x i : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ x i := by exact_mod_cast h
                             linarith
  field_simp

/-- The hypothesis (6.2) in the paper's form is `Hyp`. -/
lemma hyp_iff {a b m : ℕ} {x : ℕ → ℕ} (hb : 0 < b) (hx : ∀ i < m, 2 ≤ x i) :
    (∏ i ∈ range m, (1 - 1 / (x i : ℝ)) ≤ a / b ∧ (a : ℝ) / b < ∏ i ∈ range (m - 1), (1 - 1 / (x i : ℝ))) ↔
      Hyp a b x m := by
  have hX : (0 : ℝ) < X x m := by exact_mod_cast X_pos hx le_rfl
  have hX' : (0 : ℝ) < X x (m - 1) := by exact_mod_cast X_pos hx (Nat.sub_le m 1)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [prod_one_sub (fun i hi => by have := hx i hi; omega),
    prod_one_sub (fun i hi => by have := hx i (by omega); omega), div_le_div_iff₀ hX hb', div_lt_div_iff₀ hb' hX',
    Hyp]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast (by linarith : (b : ℝ) * Y x m ≤ a * X x m),
      by exact_mod_cast (by linarith : (a : ℝ) * X x (m - 1) < b * Y x (m - 1))⟩
  · rintro ⟨h1, h2⟩
    have h1' : (b : ℝ) * Y x m ≤ a * X x m := by exact_mod_cast h1
    have h2' : (a : ℝ) * X x (m - 1) < b * Y x (m - 1) := by exact_mod_cast h2
    constructor <;> linarith

/-- Lemma 6.3. For `u ≤ m - 1` the tail `x u, …, x (m - 1)` satisfies (6.2) with `(a X_u, b Y_u)`, and
`a X_u < b Y_u`. -/
theorem tail {a b m u : ℕ} {x : ℕ → ℕ} (h : Hyp a b x m) (hu : u ≤ m - 1) :
    Hyp (a * X x u) (b * Y x u) (fun i => x (u + i)) (m - u) ∧ a * X x u < b * Y x u := by
  obtain ⟨h1, h2⟩ := h
  have hm1 : m - 1 = u + (m - 1 - u) := by omega
  rw [hm1, X_add, Y_add] at h2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_cases hm : m = 0
    · subst hm
      have : u = 0 := by omega
      subst this
      simpa [X, Y] using h1
    have : m = u + (m - u) := by omega
    rw [this, X_add, Y_add] at h1
    calc b * Y x u * Y (fun i => x (u + i)) (m - u) = b * (Y x u * Y (fun i => x (u + i)) (m - u)) := by ring
      _ ≤ a * (X x u * X (fun i => x (u + i)) (m - u)) := h1
      _ = a * X x u * X (fun i => x (u + i)) (m - u) := by ring
  · rw [show m - u - 1 = m - 1 - u by omega]
    calc a * X x u * X (fun i => x (u + i)) (m - 1 - u)
        = a * (X x u * X (fun i => x (u + i)) (m - 1 - u)) := by ring
      _ < b * (Y x u * Y (fun i => x (u + i)) (m - 1 - u)) := h2
      _ = b * Y x u * Y (fun i => x (u + i)) (m - 1 - u) := by ring
  · by_contra hc
    push Not at hc
    have := Y_le_X (fun i => x (u + i)) (m - 1 - u)
    have h3 : b * (Y x u * Y (fun i => x (u + i)) (m - 1 - u)) ≤ a * (X x u * X (fun i => x (u + i)) (m - 1 - u)) :=
      calc b * (Y x u * Y (fun i => x (u + i)) (m - 1 - u))
          = b * Y x u * Y (fun i => x (u + i)) (m - 1 - u) := by ring
        _ ≤ a * X x u * Y (fun i => x (u + i)) (m - 1 - u) := Nat.mul_le_mul_right _ hc
        _ ≤ a * X x u * X (fun i => x (u + i)) (m - 1 - u) := Nat.mul_le_mul_left _ this
        _ = a * (X x u * X (fun i => x (u + i)) (m - 1 - u)) := by ring
    omega

/-! ### Lemma 6.4 -/

/-- The tangent line of `t ↦ log (1 - e^(-t))` at `log x`, evaluated at `log z`, lies above the function. -/
lemma log_tangent {x z : ℝ} (hx : 1 < x) (hz : 1 < z) :
    Real.log (1 - 1 / z) ≤ Real.log (1 - 1 / x) + (Real.log z - Real.log x) / (x - 1) := by
  have hx0 : 0 < 1 - 1 / x := by rw [sub_pos, div_lt_one (by linarith)]; exact hx
  have hz0 : 0 < 1 - 1 / z := by rw [sub_pos, div_lt_one (by linarith)]; exact hz
  have h1 : Real.log (1 - 1 / z) - Real.log (1 - 1 / x) ≤ (1 - 1 / z) / (1 - 1 / x) - 1 := by
    rw [← Real.log_div hz0.ne' hx0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hz0 hx0)
  have h2 : Real.log x - Real.log z ≤ x / z - 1 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    exact Real.log_le_sub_one_of_pos (by positivity)
  have hx1 : x - 1 ≠ 0 := by linarith
  have hx2 : x ≠ 0 := by linarith
  have hz2 : z ≠ 0 := by linarith
  have h3 : (1 - 1 / z) / (1 - 1 / x) - 1 = (1 - x / z) / (x - 1) := by
    field_simp
    ring
  have h4 : (1 - x / z) / (x - 1) ≤ (Real.log z - Real.log x) / (x - 1) :=
    (div_le_div_iff_of_pos_right (by linarith)).2 (by linarith)
  linarith

/-- Summation by parts: for `c` nonincreasing and nonnegative and partial sums `D_u ≤ 0`,
`∑_{i<n} cᵢ dᵢ ≤ c_{n-1} D_n`. -/
lemma abel_le (c d : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (hc : ∀ i, i + 1 < n → c (i + 1) ≤ c i)
    (hD : ∀ u ≤ n, ∑ i ∈ range u, d i ≤ 0) :
    ∑ i ∈ range n, c i * d i ≤ c (n - 1) * ∑ i ∈ range n, d i := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_range_succ, sum_range_succ, Nat.add_sub_cancel]
    have ih' := ih (fun i hi => hc i (by omega)) (fun u hu => hD u (by omega))
    have hcn : c n ≤ c (n - 1) := by
      have := hc (n - 1) (by omega)
      rwa [Nat.sub_add_cancel hn] at this
    have hDn := hD n (by omega)
    nlinarith [mul_nonneg (sub_nonneg.2 hcn) (neg_nonneg.2 hDn)]

/-- Lemma 6.4. If `x 0 ≤ ⋯ ≤ x (m - 1)` and `z 0, …, z (m - 1)` exceed `1` and `Z_u ≤ X_u` for `1 ≤ u ≤ m`,
then `∏ (1 - 1/zᵢ) ≤ ∏ (1 - 1/xᵢ)`, strictly if `Z_m < X_m`. -/
theorem major {m : ℕ} (x z : ℕ → ℝ) (hx : ∀ i < m, 1 < x i) (hz : ∀ i < m, 1 < z i)
    (hmono : ∀ i, i + 1 < m → x i ≤ x (i + 1))
    (hXZ : ∀ u, 1 ≤ u → u ≤ m → ∏ i ∈ range u, z i ≤ ∏ i ∈ range u, x i) :
    ∏ i ∈ range m, (1 - 1 / z i) ≤ ∏ i ∈ range m, (1 - 1 / x i) ∧
      (∏ i ∈ range m, z i < ∏ i ∈ range m, x i →
        ∏ i ∈ range m, (1 - 1 / z i) < ∏ i ∈ range m, (1 - 1 / x i)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  have hx0 : ∀ i ∈ range m, 0 < x i := fun i hi => by have := hx i (by simpa using hi); linarith
  have hz0 : ∀ i ∈ range m, 0 < z i := fun i hi => by have := hz i (by simpa using hi); linarith
  have hfx : ∀ i ∈ range m, 0 < 1 - 1 / x i := fun i hi => by
    have := hx i (by simpa using hi); rw [sub_pos, div_lt_one (by linarith)]; exact this
  have hfz : ∀ i ∈ range m, 0 < 1 - 1 / z i := fun i hi => by
    have := hz i (by simpa using hi); rw [sub_pos, div_lt_one (by linarith)]; exact this
  set c : ℕ → ℝ := fun i => 1 / (x i - 1) with hc
  set d : ℕ → ℝ := fun i => Real.log (z i) - Real.log (x i) with hd
  -- the partial sums of `d` are `log (Z_u / X_u)`
  have hDsum : ∀ u ≤ m, ∑ i ∈ range u, d i = Real.log (∏ i ∈ range u, z i) - Real.log (∏ i ∈ range u, x i) := by
    intro u hu
    rw [Real.log_prod (fun i hi => (hz0 i (by simp at hi ⊢; omega)).ne'),
      Real.log_prod (fun i hi => (hx0 i (by simp at hi ⊢; omega)).ne'), ← sum_sub_distrib]
  have hD : ∀ u ≤ m, ∑ i ∈ range u, d i ≤ 0 := by
    intro u hu
    rw [hDsum u hu, sub_nonpos]
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · subst h0; simp
    exact Real.log_le_log (prod_pos (fun i hi => hz0 i (by simp at hi ⊢; omega))) (hXZ u h0 hu)
  have hcmono : ∀ i, i + 1 < m → c (i + 1) ≤ c i := by
    intro i hi
    have h1 := hx i (by omega)
    simp only [hc]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [hmono i hi])
  have hcpos : 0 < c (m - 1) := by
    have := hx (m - 1) (by omega); simp only [hc]; exact one_div_pos.2 (by linarith)
  have habel := abel_le c d hm hcmono hD
  have htan : ∑ i ∈ range m, Real.log (1 - 1 / z i) ≤
      ∑ i ∈ range m, Real.log (1 - 1 / x i) + ∑ i ∈ range m, c i * d i := by
    rw [← sum_add_distrib]
    refine sum_le_sum (fun i hi => ?_)
    have := log_tangent (hx i (by simpa using hi)) (hz i (by simpa using hi))
    simp only [hc, hd]
    linarith [show (Real.log (z i) - Real.log (x i)) / (x i - 1) = 1 / (x i - 1) * (Real.log (z i) - Real.log (x i))
      by ring]
  have hlogz := Real.log_prod (fun i hi => (hfz i hi).ne')
  have hlogx := Real.log_prod (fun i hi => (hfx i hi).ne')
  have hPz := prod_pos hfz
  have hPx := prod_pos hfx
  have hDm := hD m le_rfl
  constructor
  · rw [← Real.log_le_log_iff hPz hPx, hlogz, hlogx]
    nlinarith
  · intro hlt
    have hDm' : ∑ i ∈ range m, d i < 0 := by
      rw [hDsum m le_rfl, sub_neg]
      exact Real.log_lt_log (prod_pos hz0) hlt
    rw [← Real.log_lt_log_iff hPz hPx, hlogz, hlogx]
    nlinarith [mul_neg_of_pos_of_neg hcpos hDm']

/-! ### Lemma 6.5 -/

/-- The extremal sequence of Lemma 6.5 with `n` terms: `(α + 1) ^ 2 ^ i + 1` for `i < n - 1`, and
`(α + 1) ^ 2 ^ (n - 1)` for `i = n - 1`. -/
noncomputable def cn (α : ℝ) (n i : ℕ) : ℝ := if i + 1 < n then (α + 1) ^ 2 ^ i + 1 else (α + 1) ^ 2 ^ i

lemma cn_mul_prod (α : ℝ) {n u : ℕ} (hu : u ≤ n - 1) :
    α * ∏ i ∈ range u, cn α n i = (α + 1) ^ 2 ^ u - 1 := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [prod_range_succ, ← mul_assoc, ih (by omega), cn, ite_eq_left (by omega), pow_succ, pow_mul]
    ring

lemma cn_mul_prod_all (α : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    α * ∏ i ∈ range n, cn α n i = E n (α + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [prod_range_succ, ← mul_assoc, cn_mul_prod α (by omega), cn, ite_eq_right (by omega), E_eq hn, Nat.add_sub_cancel]
  ring

lemma cn_gt_one {α : ℝ} (hα : 0 < α) (n i : ℕ) : 1 < cn α n i := by
  have : 1 < (α + 1) ^ 2 ^ i := one_lt_pow₀ (by linarith) (by positivity)
  unfold cn; split_ifs <;> linarith

/-- The identity (6.3): `∏_{i<n} (1 - 1/zᵢ) = α / (α + 1)`. -/
lemma cn_prod_one_sub {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∏ i ∈ range n, (1 - 1 / cn α n i) = α / (α + 1) := by
  -- `∏_{i<u} (1 - 1/zᵢ) · ((α + 1) ^ 2 ^ u - 1) · (α + 1) = α (α + 1) ^ 2 ^ u` for `u ≤ n - 1`
  have key : ∀ u, u ≤ n - 1 → (∏ i ∈ range u, (1 - 1 / cn α n i)) * ((α + 1) ^ 2 ^ u - 1) * (α + 1) =
      α * (α + 1) ^ 2 ^ u := by
    intro u
    induction u with
    | zero => intro _; simp
    | succ u ih =>
      intro hu
      have ih := ih (by omega)
      have ht1 : 1 < (α + 1) ^ 2 ^ u := one_lt_pow₀ (by linarith) (by positivity)
      rw [prod_range_succ, cn, ite_eq_left (by omega), pow_succ, pow_mul]
      set t := (α + 1) ^ 2 ^ u
      set P := ∏ i ∈ range u, (1 - 1 / cn α n i)
      have ht0 : t + 1 ≠ 0 := by linarith
      have : P * (1 - 1 / (t + 1)) * (t ^ 2 - 1) * (α + 1) = t * (P * (t - 1) * (α + 1)) := by
        field_simp; ring
      rw [this, ih]; ring
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := key k (by omega)
  have ht1 : 1 < (α + 1) ^ 2 ^ k := one_lt_pow₀ (by linarith) (by positivity)
  rw [prod_range_succ, cn, ite_eq_right (by omega)]
  set t := (α + 1) ^ 2 ^ k
  set P := ∏ i ∈ range k, (1 - 1 / cn α (k + 1) i)
  have ht0 : t ≠ 0 := by linarith
  have hα1 : α + 1 ≠ 0 := by linarith
  rw [eq_div_iff hα1]
  have : P * (1 - 1 / t) * (α + 1) = (P * (t - 1) * (α + 1)) / t := by field_simp
  rw [this, hk]; field_simp

/-- Lemma 6.5 (Cook, Nielsen) for `Hyp`. -/
theorem cook_nielsen_hyp : ∀ (m a b : ℕ) (x : ℕ → ℕ), 1 ≤ m → 1 ≤ a → a < b → (∀ i < m, 2 ≤ x i) →
    (∀ i, i + 1 < m → x i ≤ x (i + 1)) → Hyp a b x m → (a : ℝ) * X x m ≤ E m (a + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro a b x hm ha hab hx hmono hhyp
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hcastX : ∀ u, (X x u : ℝ) = ∏ i ∈ range u, (x i : ℝ) := fun u => by simp [X]
  by_cases hcase : ∃ u, 1 ≤ u ∧ u ≤ m - 1 ∧ (X x u : ℝ) ≤ ∏ i ∈ range u, cn a m i
  · -- `X_u ≤ Z_u` for some `u ≤ m - 1`: the induction hypothesis on the tail
    obtain ⟨u, hu1, hu, hXu⟩ := hcase
    obtain ⟨htail, hlt⟩ := tail hhyp hu
    have hXpos := X_pos hx (show u ≤ m by omega)
    have hrec := IH (m - u) (by omega) (a * X x u) (b * Y x u) (fun i => x (u + i)) (by omega)
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) hlt
      (fun i hi => hx (u + i) (by omega)) (fun i hi => hmono (u + i) (by omega)) htail
    have hbound : (a : ℝ) * X x u + 1 ≤ (a + 1) ^ 2 ^ u := by
      have := cn_mul_prod (a : ℝ) (n := m) hu
      nlinarith [mul_le_mul_of_nonneg_left hXu ha'.le]
    have h0 : (0 : ℝ) ≤ ((a * X x u : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (a : ℝ) * X x m = ((a * X x u : ℕ) : ℝ) * X (fun i => x (u + i)) (m - u) := by
          conv_lhs => rw [show m = u + (m - u) by omega, X_add]
          push_cast; ring
      _ ≤ E (m - u) (((a * X x u : ℕ) : ℝ) + 1) := hrec
      _ ≤ E (m - u) (((a : ℝ) + 1) ^ 2 ^ u) := E_mono (by omega) (by linarith) (by push_cast; exact hbound)
      _ = E m (a + 1) := by rw [E_comp (by omega), Nat.sub_add_cancel (by omega)]
  · -- `X_u > Z_u` for all `u ≤ m - 1`: then `X_m ≤ Z_m`, by Lemma 6.4 and (6.3)
    push Not at hcase
    by_contra hcon
    push Not at hcon
    have hZ := cn_mul_prod_all (a : ℝ) hm
    have hlt : ∏ i ∈ range m, cn a m i < X x m := by
      by_contra h
      push Not at h
      exact absurd (hZ ▸ mul_le_mul_of_nonneg_left h ha'.le) (not_le.2 hcon)
    obtain ⟨-, hstrict⟩ := major (m := m) (fun i => (x i : ℝ)) (cn a m)
      (fun i hi => by have := hx i hi; exact_mod_cast (by omega : 1 < x i)) (fun i _ => cn_gt_one ha' m i)
      (fun i hi => by exact_mod_cast hmono i hi)
      (fun u hu1 hu => by
        rw [← hcastX]
        rcases eq_or_lt_of_le hu with rfl | hlt'
        · exact hlt.le
        · exact (hcase u hu1 (by omega)).le)
    have h1 := hstrict (by rw [← hcastX]; exact hlt)
    rw [cn_prod_one_sub ha' hm] at h1
    have h2 := ((hyp_iff (by omega) hx).2 hhyp).1
    have h3 : (a : ℝ) / b ≤ a / (a + 1) :=
      div_le_div_of_nonneg_left ha'.le (by positivity) (by exact_mod_cast Nat.succ_le_of_lt hab)
    linarith

/-- Lemma 6.5 (Cook, Nielsen). If `1 ≤ a < b`, `m ≥ 1` and `2 ≤ x 0 ≤ ⋯ ≤ x (m - 1)` satisfy (6.2), then
`a X_m ≤ E_m(a + 1)`. -/
theorem cook_nielsen {a b m : ℕ} (x : ℕ → ℕ) (ha : 1 ≤ a) (hab : a < b) (hm : 1 ≤ m)
    (hx : ∀ i < m, 2 ≤ x i) (hmono : ∀ i, i + 1 < m → x i ≤ x (i + 1))
    (hhyp : ∏ i ∈ range m, (1 - 1 / (x i : ℝ)) ≤ a / b)
    (hhyp' : (a : ℝ) / b < ∏ i ∈ range (m - 1), (1 - 1 / (x i : ℝ))) :
    (a : ℝ) * ∏ i ∈ range m, (x i : ℝ) ≤ E m (a + 1) := by
  have := cook_nielsen_hyp m a b x hm ha hab hx hmono ((hyp_iff (by omega) hx).1 ⟨hhyp, hhyp'⟩)
  simpa [X] using this

/-! ### Theorem 6.2 -/

/-- The comparison sequence of Theorem 6.2: `(b + 1) / d` with `d = b - a`, followed by the sequence of Lemma 6.5
with `G - 1` in place of `a` and `m - 1` terms, where `G = b (a + 1) / d`. -/
noncomputable def zd (a b m i : ℕ) : ℝ :=
  if i = 0 then ((b : ℝ) + 1) / ((b : ℝ) - a) else cn ((b : ℝ) * (a + 1) / ((b : ℝ) - a) - 1) (m - 1) (i - 1)

section deficit

variable {a b m : ℕ}

private lemma G_sub_one (hab : a < b) :
    (b : ℝ) * (a + 1) / ((b : ℝ) - a) - 1 = a * (((b : ℝ) + 1) / ((b : ℝ) - a)) := by
  have hd : (b : ℝ) - a ≠ 0 := by have : (a : ℝ) < b := by exact_mod_cast hab
                                  linarith
  field_simp
  ring

private lemma G_sub_one_pos (ha : 1 ≤ a) (hab : a < b) : 0 < (b : ℝ) * (a + 1) / ((b : ℝ) - a) - 1 := by
  rw [G_sub_one hab]
  have : (a : ℝ) < b := by exact_mod_cast hab
  have : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have : 0 < ((b : ℝ) + 1) / ((b : ℝ) - a) := div_pos (by linarith) (by linarith)
  positivity

lemma zd_prod_succ (u : ℕ) : ∏ i ∈ range (u + 1), zd a b m i =
    (∏ i ∈ range u, cn ((b : ℝ) * (a + 1) / ((b : ℝ) - a) - 1) (m - 1) i) * (((b : ℝ) + 1) / ((b : ℝ) - a)) := by
  rw [prod_range_succ']
  simp [zd]

lemma zd_gt_one (ha : 1 ≤ a) (hab : a < b) (i : ℕ) : 1 < zd a b m i := by
  unfold zd
  split_ifs
  · have : (a : ℝ) < b := by exact_mod_cast hab
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    rw [one_lt_div (by linarith)]; linarith
  · exact cn_gt_one (G_sub_one_pos ha hab) _ _

/-- `a Z_u = G ^ 2 ^ (u - 1) - 1` for `1 ≤ u ≤ m - 1`. -/
lemma zd_mul_prod (hab : a < b) {u : ℕ} (hu1 : 1 ≤ u) (hu : u ≤ m - 1) :
    a * ∏ i ∈ range u, zd a b m i = ((b : ℝ) * (a + 1) / ((b : ℝ) - a)) ^ 2 ^ (u - 1) - 1 := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  rw [zd_prod_succ, Nat.add_sub_cancel]
  have := cn_mul_prod ((b : ℝ) * (a + 1) / ((b : ℝ) - a) - 1) (n := m - 1) (u := v) (by omega)
  rw [sub_add_cancel] at this
  rw [← this, G_sub_one hab]
  ring

/-- `a Z_m = E_{m-1}(G)`. -/
lemma zd_mul_prod_all (hab : a < b) (hm : 2 ≤ m) :
    a * ∏ i ∈ range m, zd a b m i = E (m - 1) ((b : ℝ) * (a + 1) / ((b : ℝ) - a)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [zd_prod_succ, Nat.add_sub_cancel]
  have := cn_mul_prod_all ((b : ℝ) * (a + 1) / ((b : ℝ) - a) - 1) (n := k) (by omega)
  rw [sub_add_cancel] at this
  rw [← this, G_sub_one hab]
  ring

/-- `∏_{i<m} (1 - 1/zᵢ) = a / b`. -/
lemma zd_prod_one_sub (ha : 1 ≤ a) (hab : a < b) (hm : 2 ≤ m) :
    ∏ i ∈ range m, (1 - 1 / zd a b m i) = a / b := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [prod_range_succ']
  have h1 : ∏ i ∈ range k, (1 - 1 / zd a b (k + 1) (i + 1)) =
      ∏ i ∈ range k, (1 - 1 / cn ((b : ℝ) * (a + 1) / ((b : ℝ) - a) - 1) k i) := by
    refine prod_congr rfl (fun i _ => ?_)
    simp [zd]
  rw [h1, cn_prod_one_sub (G_sub_one_pos ha hab) (by omega), sub_add_cancel]
  have : (a : ℝ) < b := by exact_mod_cast hab
  have : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hd : (b : ℝ) - a ≠ 0 := by linarith
  have hb1 : (b : ℝ) + 1 ≠ 0 := by linarith
  have ha1 : (a : ℝ) + 1 ≠ 0 := by linarith
  have hb : (b : ℝ) ≠ 0 := by linarith
  simp only [zd, ite_true]
  field_simp
  ring

/-- Theorem 6.2 for `Hyp`. -/
theorem deficit_hyp (x : ℕ → ℕ) (ha : 1 ≤ a) (hab : a < b) (hm : 2 ≤ m) (hx : ∀ i < m, 2 ≤ x i)
    (hmono : ∀ i, i + 1 < m → x i ≤ x (i + 1)) (hhyp : Hyp a b x m) :
    (a : ℝ) * X x m ≤ E (m - 1) ((b : ℝ) * (a + 1) / ((b : ℝ) - a)) := by
  set G := (b : ℝ) * (a + 1) / ((b : ℝ) - a) with hG
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hG1 : 1 < G := by have := G_sub_one_pos ha hab; linarith
  have hcastX : ∀ u, (X x u : ℝ) = ∏ i ∈ range u, (x i : ℝ) := fun u => by simp [X]
  by_cases hcase : ∃ u, 1 ≤ u ∧ u ≤ m - 1 ∧ (X x u : ℝ) ≤ ∏ i ∈ range u, zd a b m i
  · -- `X_u ≤ Z_u` for some `u ≤ m - 1`: Lemmas 6.3 and 6.5 on the tail
    obtain ⟨u, hu1, hu, hXu⟩ := hcase
    obtain ⟨htail, hlt⟩ := tail hhyp hu
    have hXpos := X_pos hx (show u ≤ m by omega)
    have hrec := cook_nielsen_hyp (m - u) (a * X x u) (b * Y x u) (fun i => x (u + i)) (by omega)
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) hlt
      (fun i hi => hx (u + i) (by omega)) (fun i hi => hmono (u + i) (by omega)) htail
    have hbound : (a : ℝ) * X x u + 1 ≤ G ^ 2 ^ (u - 1) := by
      have := zd_mul_prod hab hu1 hu
      nlinarith [mul_le_mul_of_nonneg_left hXu ha'.le]
    have h0 : (0 : ℝ) ≤ ((a * X x u : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (a : ℝ) * X x m = ((a * X x u : ℕ) : ℝ) * X (fun i => x (u + i)) (m - u) := by
          conv_lhs => rw [show m = u + (m - u) by omega, X_add]
          push_cast; ring
      _ ≤ E (m - u) (((a * X x u : ℕ) : ℝ) + 1) := hrec
      _ ≤ E (m - u) (G ^ 2 ^ (u - 1)) := E_mono (by omega) (by linarith) (by push_cast; exact hbound)
      _ = E (m - 1) G := by rw [E_comp (by omega), show m - u + (u - 1) = m - 1 by omega]
  · -- `X_u > Z_u` for all `u ≤ m - 1`: then `X_m ≤ Z_m` by Lemma 6.4
    push Not at hcase
    by_contra hcon
    push Not at hcon
    have hZ := zd_mul_prod_all hab hm
    have hlt : ∏ i ∈ range m, zd a b m i < X x m := by
      by_contra h
      push Not at h
      exact absurd (hZ ▸ mul_le_mul_of_nonneg_left h ha'.le) (not_le.2 hcon)
    obtain ⟨-, hstrict⟩ := major (m := m) (fun i => (x i : ℝ)) (zd a b m)
      (fun i hi => by have := hx i hi; exact_mod_cast (by omega : 1 < x i)) (fun i _ => zd_gt_one ha hab i)
      (fun i hi => by exact_mod_cast hmono i hi)
      (fun u hu1 hu => by
        rw [← hcastX]
        rcases eq_or_lt_of_le hu with rfl | hlt'
        · exact hlt.le
        · exact (hcase u hu1 (by omega)).le)
    have h1 := hstrict (by rw [← hcastX]; exact hlt)
    rw [zd_prod_one_sub ha hab hm] at h1
    have h2 := ((hyp_iff (by omega) hx).2 hhyp).1
    linarith

/-- Theorem 6.2. If `1 ≤ a < b`, `d = b - a`, `m ≥ 2` and `2 ≤ x 0 ≤ ⋯ ≤ x (m - 1)` satisfy (6.2), then
`a X_m ≤ E_{m-1}(b (a + 1) / d)`. -/
theorem deficit (x : ℕ → ℕ) (ha : 1 ≤ a) (hab : a < b) (hm : 2 ≤ m)
    (hx : ∀ i < m, 2 ≤ x i) (hmono : ∀ i, i + 1 < m → x i ≤ x (i + 1))
    (hhyp : ∏ i ∈ range m, (1 - 1 / (x i : ℝ)) ≤ a / b)
    (hhyp' : (a : ℝ) / b < ∏ i ∈ range (m - 1), (1 - 1 / (x i : ℝ))) :
    (a : ℝ) * ∏ i ∈ range m, (x i : ℝ) ≤ E (m - 1) ((b : ℝ) * (a + 1) / ((b : ℝ) - a)) := by
  have := deficit_hyp x ha hab hm hx hmono ((hyp_iff (by omega) hx).1 ⟨hhyp, hhyp'⟩)
  simpa [X] using this

/-- For `d = 1` the bound of Theorem 6.2 is the bound `E_m(a + 1)` of Lemma 6.5. -/
lemma deficit_one (a : ℕ) {m : ℕ} (hm : 2 ≤ m) :
    E (m - 1) (((a : ℝ) + 1) * (a + 1) / (((a : ℝ) + 1) - a)) = E m (a + 1) := by
  rw [show ((a : ℝ) + 1) - a = 1 by ring, div_one, ← sq, show ((a : ℝ) + 1) ^ 2 = ((a : ℝ) + 1) ^ 2 ^ 1 by norm_num,
    E_comp (by omega), Nat.sub_add_cancel (by omega)]

/-- Theorem 6.2, equality: if `d ∣ b + 1`, some integers `2 ≤ x 0 ≤ ⋯ ≤ x (m - 1)` satisfying (6.2) attain
`a X_m = E_{m-1}(b (a + 1) / d)`. -/
theorem deficit_attained (ha : 1 ≤ a) (hab : a < b) (hm : 2 ≤ m) (hdvd : b - a ∣ b + 1) :
    ∃ x : ℕ → ℕ, (∀ i < m, 2 ≤ x i) ∧ (∀ i, i + 1 < m → x i ≤ x (i + 1)) ∧
      ∏ i ∈ range m, (1 - 1 / (x i : ℝ)) ≤ a / b ∧ (a : ℝ) / b < ∏ i ∈ range (m - 1), (1 - 1 / (x i : ℝ)) ∧
      (a : ℝ) * ∏ i ∈ range m, (x i : ℝ) = E (m - 1) ((b : ℝ) * (a + 1) / ((b : ℝ) - a)) := by
  obtain ⟨z, hz⟩ := hdvd
  set g := a * z + 1 with hg
  have hz2 : 2 ≤ z := by
    rcases Nat.lt_or_ge z 2 with h | h
    · interval_cases z
      · simp at hz
      · omega
    · exact h
  have hg3 : 3 ≤ g := by nlinarith
  let x : ℕ → ℕ := fun i => if i = 0 then z else if i + 1 < m then g ^ 2 ^ (i - 1) + 1 else g ^ 2 ^ (i - 1)
  -- the integers `x i` are the numbers `zd a b m i`
  have hbr : (b : ℝ) < b + 1 := by linarith
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hd : (b : ℝ) - a ≠ 0 := by linarith
  have hzr : (z : ℝ) = ((b : ℝ) + 1) / ((b : ℝ) - a) := by
    have : ((b + 1 : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) * z := by exact_mod_cast hz
    push_cast [Nat.cast_sub hab.le] at this
    field_simp
    linarith
  have hgr : (g : ℝ) = (b : ℝ) * (a + 1) / ((b : ℝ) - a) := by
    have := G_sub_one hab
    rw [hg]; push_cast; rw [hzr]; linarith
  have hcast : ∀ i, (x i : ℝ) = zd a b m i := by
    intro i
    simp only [x, zd, cn, sub_add_cancel, ← hgr]
    split_ifs <;> first | omega | exact hzr | (push_cast; ring)
  have hprod : ∀ u, ∏ i ∈ range u, (1 - 1 / (x i : ℝ)) = ∏ i ∈ range u, (1 - 1 / zd a b m i) :=
    fun u => prod_congr rfl (fun i _ => by rw [hcast])
  refine ⟨x, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [x]
    split_ifs
    · exact hz2
    · have := Nat.le_self_pow (pow_ne_zero (i - 1) two_ne_zero) g; omega
    · have := Nat.le_self_pow (pow_ne_zero (i - 1) two_ne_zero) g; omega
  · intro i hi
    simp only [x]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have : z ≤ g := by nlinarith
      simp only [Nat.zero_add, Nat.sub_self, pow_zero, pow_one]
      split_ifs <;> omega
    · have hpow : g ^ 2 ^ i = (g ^ 2 ^ (i - 1)) ^ 2 := by
        rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hi0]
      have ht : 3 ≤ g ^ 2 ^ (i - 1) := le_trans hg3 (Nat.le_self_pow (pow_ne_zero _ two_ne_zero) g)
      have hsq : g ^ 2 ^ (i - 1) + 1 ≤ (g ^ 2 ^ (i - 1)) ^ 2 := by nlinarith
      rw [Nat.add_sub_cancel, hpow]
      split_ifs <;> first | contradiction | omega
  · rw [hprod, zd_prod_one_sub ha hab hm]
  · rw [hprod, ← zd_prod_one_sub ha hab hm]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [prod_range_succ, Nat.add_sub_cancel]
    have hP : 0 < ∏ i ∈ range k, (1 - 1 / zd a b (k + 1) i) := prod_pos (fun i _ => by
      have := zd_gt_one (m := k + 1) ha hab i; rw [sub_pos, div_lt_one (by linarith)]; exact this)
    have hl := zd_gt_one (m := k + 1) ha hab k
    have : 1 - 1 / zd a b (k + 1) k < 1 := by
      have : 0 < 1 / zd a b (k + 1) k := one_div_pos.2 (by linarith)
      linarith
    nlinarith
  · rw [← zd_mul_prod_all hab hm]
    congr 1
    exact prod_congr rfl (fun i _ => hcast i)

end deficit

/-! ### Proposition 6.8 and Corollary 6.10 -/

section heavy

variable {p : ℕ → ℕ} {k M : ℕ}

lemma E_lt_pow (m : ℕ) {y : ℝ} (hy : 0 < y) : E m y < y ^ 2 ^ m := by
  unfold E
  have : 0 < y ^ 2 ^ (m - 1) := pow_pos hy _
  linarith

/-- `V_j = M B_j (A_j + 1) / (M B_j - A_j)`, equation (6.4), with `A_j = X p j` and `B_j = Y p j`. -/
noncomputable def V (p : ℕ → ℕ) (M j : ℕ) : ℝ :=
  ((M : ℝ) * Y p j) * ((X p j : ℝ) + 1) / ((M : ℝ) * Y p j - X p j)

/-- Lemma 6.1 (i) in the form `Hyp 1 M p k`: `M ≤ P_k` and `P_{k-1} < M`, cleared of denominators. -/
lemma hyp_of_eq (hk : 1 ≤ k) (hM : 2 ≤ M) (hp : ∀ i < k, 2 ≤ p i) (heq : X p k = M * Y p k + 1) :
    Hyp 1 M p k := by
  refine ⟨by omega, ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, one_mul]
  have hq := hp l (by omega)
  have hY : 1 ≤ Y p l := Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 (fun i hi => by
    have := hp i (by simp at hi; omega); omega))
  obtain ⟨r, hr⟩ : ∃ r, p l = r + 1 := ⟨p l - 1, by omega⟩
  have heq' : X p l * (r + 1) = M * Y p l * r + 1 := by
    have := heq
    simp only [X, Y, prod_range_succ] at this
    rw [hr, Nat.add_sub_cancel] at this
    simp only [X, Y]
    linarith
  by_contra h
  push Not at h
  nlinarith

/-- `V_j > 1` whenever `1 ≤ A_j < M B_j`. -/
lemma one_lt_V {j : ℕ} (hA : 1 ≤ X p j) (hlt : X p j < M * Y p j) : 1 < V p M j := by
  have hlt' : (X p j : ℝ) < M * Y p j := by exact_mod_cast hlt
  have hA' : (1 : ℝ) ≤ X p j := by exact_mod_cast hA
  unfold V
  rw [one_lt_div (by linarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ M * Y p j) (by linarith : (0 : ℝ) ≤ X p j)]

/-- Proposition 6.8. Let `2 ≤ p 0 ≤ ⋯ ≤ p (k - 1)`, `M ≥ 2` and `p 0 ⋯ p (k - 1) - 1 = M ∏ (p i - 1)`. For
`j ≤ k - 1`, `n < (A_j + 1) ^ 2 ^ (k - j)` and `n < V_j ^ 2 ^ (k - j - 1)`. -/
theorem size_bounds (hk : 1 ≤ k) (hM : 2 ≤ M) (hp : ∀ i < k, 2 ≤ p i)
    (hmono : ∀ i, i + 1 < k → p i ≤ p (i + 1)) (heq : X p k = M * Y p k + 1) {j : ℕ} (hj : j ≤ k - 1) :
    (X p k : ℝ) < ((X p j : ℝ) + 1) ^ 2 ^ (k - j) ∧ (X p k : ℝ) < V p M j ^ 2 ^ (k - j - 1) := by
  obtain ⟨htail, hlt⟩ := tail (hyp_of_eq hk hM hp heq) hj
  rw [one_mul] at htail hlt
  have hA : 1 ≤ X p j := X_pos hp (by omega)
  have hsplit : (X p k : ℝ) = (X p j : ℝ) * X (fun i => p (j + i)) (k - j) := by
    conv_lhs => rw [show k = j + (k - j) by omega, X_add]
    push_cast; ring
  have hx : ∀ i < k - j, 2 ≤ p (j + i) := fun i hi => hp (j + i) (by omega)
  have hmono' : ∀ i, i + 1 < k - j → p (j + i) ≤ p (j + (i + 1)) := fun i hi => hmono (j + i) (by omega)
  have hA' : (1 : ℝ) ≤ X p j := by exact_mod_cast hA
  refine ⟨?_, ?_⟩
  · have := cook_nielsen_hyp (k - j) (X p j) (M * Y p j) (fun i => p (j + i)) (by omega) hA hlt hx hmono' htail
    rw [hsplit]
    exact lt_of_le_of_lt this (E_lt_pow _ (by linarith))
  · have hV := one_lt_V hA hlt
    rcases Nat.lt_or_ge (k - j) 2 with h1 | h2
    · -- `j = k - 1`: Lemma 6.1 (ii)
      have hjk : k = j + 1 := by omega
      rw [show k - j - 1 = 0 by omega, pow_zero, pow_one]
      subst hjk
      have hlt' : (X p j : ℝ) < M * Y p j := by exact_mod_cast hlt
      have hq := hp j (by omega)
      have h := heq
      rw [X_succ, Y_succ] at h
      have heq' : (X p j : ℝ) * p j = M * Y p j * (p j - 1) + 1 := by
        have : ((X p j * p j : ℕ) : ℝ) = ((M * (Y p j * (p j - 1)) + 1 : ℕ) : ℝ) := by rw [h]
        push_cast [Nat.cast_sub (by omega : 1 ≤ p j)] at this
        linarith
      rw [X_succ, Nat.cast_mul, V, lt_div_iff₀ (by linarith)]
      nlinarith
    · have := deficit_hyp (fun i => p (j + i)) hA hlt h2 hx hmono' htail
      have hG : ((M * Y p j : ℕ) : ℝ) * ((X p j : ℝ) + 1) / (((M * Y p j : ℕ) : ℝ) - X p j) = V p M j := by
        unfold V; push_cast; ring
      rw [hG] at this
      rw [hsplit]
      exact lt_of_le_of_lt this (E_lt_pow _ (by linarith))

/-- `θ_i = 2 ^ 2 ^ (i - s)` for `i ≥ s`, and `θ_i = 1` for `i < s`. -/
def θ (s i : ℕ) : ℕ := if s ≤ i then 2 ^ 2 ^ (i - s) else 1

/-- Definition 6.9: the solution is `s`-heavy if `A_j ≥ θ_j` (H1) and `V_j ≥ θ_{j+1}` (H2) for `0 ≤ j ≤ k - 1`. -/
def Heavy (p : ℕ → ℕ) (k M s : ℕ) : Prop := ∀ j < k, θ s j ≤ X p j ∧ (θ s (j + 1) : ℝ) ≤ V p M j

/-- Corollary 6.10. A solution that is not `s`-heavy satisfies `n < 2 ^ 2 ^ (k - s)`. -/
theorem light (hk : 1 ≤ k) (hM : 2 ≤ M) (hp : ∀ i < k, 2 ≤ p i)
    (hmono : ∀ i, i + 1 < k → p i ≤ p (i + 1)) (heq : X p k = M * Y p k + 1) {s : ℕ} (hs : ¬ Heavy p k M s) :
    (X p k : ℝ) < 2 ^ 2 ^ (k - s) := by
  unfold Heavy at hs
  push Not at hs
  obtain ⟨j, hj, hH⟩ := hs
  obtain ⟨hb1, hb2⟩ := size_bounds hk hM hp hmono heq (j := j) (by omega)
  have hA : 1 ≤ X p j := X_pos hp (by omega)
  by_cases h1 : θ s j ≤ X p j
  · -- (H2) fails at `j`
    have h2 := hH h1
    have hlt := (tail (hyp_of_eq hk hM hp heq) (u := j) (by omega)).2
    rw [one_mul] at hlt
    have hV := one_lt_V hA hlt
    have hsj : s ≤ j + 1 := by
      by_contra h
      simp only [θ, ite_eq_right (show ¬ s ≤ j + 1 by omega), Nat.cast_one] at h2
      linarith
    simp only [θ, ite_eq_left hsj] at h2
    calc (X p k : ℝ) < V p M j ^ 2 ^ (k - j - 1) := hb2
      _ < ((2 : ℝ) ^ 2 ^ (j + 1 - s)) ^ 2 ^ (k - j - 1) :=
          pow_lt_pow_left₀ (by exact_mod_cast h2) (by linarith) (by positivity)
      _ = 2 ^ 2 ^ (k - s) := by
          rw [← pow_mul, ← pow_add, show j + 1 - s + (k - j - 1) = k - s by omega]
  · -- (H1) fails at `j`
    push Not at h1
    have hsj : s ≤ j := by
      by_contra h
      simp only [θ, ite_eq_right h] at h1
      omega
    simp only [θ, ite_eq_left hsj] at h1
    have h1' : (X p j : ℝ) + 1 ≤ 2 ^ 2 ^ (j - s) := by exact_mod_cast h1
    calc (X p k : ℝ) < ((X p j : ℝ) + 1) ^ 2 ^ (k - j) := hb1
      _ ≤ ((2 : ℝ) ^ 2 ^ (j - s)) ^ 2 ^ (k - j) := pow_le_pow_left₀ (by positivity) h1' _
      _ = 2 ^ 2 ^ (k - s) := by
          rw [← pow_mul, ← pow_add, show j - s + (k - j) = k - s by omega]

end heavy

end LehmerTotient.Product
