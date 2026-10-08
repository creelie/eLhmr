import LehmerTotient.PseudoExtend
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.CarmichaelNumber

/-!
# Descent, three entries and Korselt's criterion (Section 9.7)

The product equation `x₁ ⋯ x_k + ε = 2 ∏ (xᵢ - 1)` after a prefix with products `A = ∏ xᵢ` and `B = ∏ (xᵢ - 1)`.

* `degree_one`, `degree_one_unique`: with all entries but `x` fixed, the equation reads `x (2B' - A') = 2B' + ε`, so
  at most one `x` completes it.
* `three_entries_identity`: Proposition 9.7 (i), the identity
  `uvw - 2AB(u + v + w) = 12AB² - 8B³ + (2B + ε)C² - C² F` with `C = 2B - A`, `u = Cx - 2B`, `v = Cy - 2B`,
  `w = Cz - 2B`.
* `no_linear_factorisation`: Proposition 9.7 (ii), for nonzero `A`, `B` and `2B - A` the polynomial `F` is never a product of three
  affine forms plus a constant.
* `fermat_entry`: Lemma 9.8, an entry `x` prime to `N` with `a ^ N ≡ 1 (mod x)` for every `a` prime to `x` is
  squarefree, and `q - 1 ∣ N` for every prime `q ∣ x`.
* `fermat_tuple`, `fermat_tuple_carmichael`: for pairwise coprime entries with this property, `A = ∏ xᵢ` is
  squarefree and `q - 1 ∣ N` for every prime `q ∣ A`; for Lehmer's sign and at least two entries `A` is a Carmichael
  number (Korselt's criterion, `Nat.isCarmichael_iff_korselt`).
-/

namespace LehmerTotient

/-! ### Degree one in each entry -/

/-- With the other entries fixed (products `A'` and `B'`), the equation is linear in the remaining entry. -/
theorem degree_one (A' B' x ε : ℤ) :
    A' * x + ε = 2 * B' * (x - 1) ↔ x * (2 * B' - A') = 2 * B' + ε := by
  constructor <;> intro h <;> linear_combination -h

/-- At most one value of the remaining entry completes the equation once `2B' - A' ≠ 0`. -/
theorem degree_one_unique (A' B' ε x y : ℤ) (hC : 2 * B' - A' ≠ 0)
    (hx : A' * x + ε = 2 * B' * (x - 1)) (hy : A' * y + ε = 2 * B' * (y - 1)) : x = y := by
  rw [degree_one] at hx hy
  have : (x - y) * (2 * B' - A') = 0 := by linear_combination hx - hy
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hC

/-! ### Three entries: Proposition 9.7 -/

/-- The equation for the last three entries after a prefix with products `A` and `B`, written as `F = 0`. -/
def F3 {R : Type*} [CommRing R] (A B ε x y z : R) : R :=
  A * x * y * z + ε - 2 * B * (x - 1) * (y - 1) * (z - 1)

/-- Proposition 9.7 (i). -/
theorem three_entries_identity {R : Type*} [CommRing R] (A B ε x y z : R) :
    let C := 2 * B - A
    let u := C * x - 2 * B
    let v := C * y - 2 * B
    let w := C * z - 2 * B
    u * v * w - 2 * A * B * (u + v + w)
      = 12 * A * B ^ 2 - 8 * B ^ 3 + (2 * B + ε) * C ^ 2 - C ^ 2 * F3 A B ε x y z := by
  simp only [F3]
  ring

/-- A cubic polynomial over `ℚ` that vanishes everywhere has zero coefficients. -/
lemma cubic_eq_zero {c₃ c₂ c₁ c₀ : ℚ} (h : ∀ t : ℚ, c₃ * t ^ 3 + c₂ * t ^ 2 + c₁ * t + c₀ = 0) :
    c₃ = 0 ∧ c₂ = 0 ∧ c₁ = 0 ∧ c₀ = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  have h3 := h 2
  norm_num at h0 h1 h2 h3
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- An affine form in `y` and `z`. -/
def aff (b c d y z : ℚ) : ℚ := b * y + c * z + d

/-- The coefficient of `x` in `F3 A B ε x y z`, a polynomial in `y` and `z`. -/
def P3 (A B y z : ℚ) : ℚ := -(2 * B - A) * y * z + 2 * B * y + 2 * B * z - 2 * B

lemma P3_one (A B : ℚ) : P3 A B 1 1 = A := by simp only [P3]; ring

/-- If `A`, `B` and `2B - A` are nonzero, the coefficient of `x` is not `α` times a product of two affine forms in `y`
and `z`. -/
lemma P3_not_product (A B α b₂ c₂ d₂ b₃ c₃ d₃ : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : 2 * B - A ≠ 0)
    (h : ∀ y z : ℚ, P3 A B y z = α * aff b₂ c₂ d₂ y z * aff b₃ c₃ d₃ y z) : False := by
  have e00 := h 0 0
  have e10 := h 1 0
  have e20 := h (-1) 0
  have e01 := h 0 1
  have e02 := h 0 (-1)
  have e11 := h 1 1
  simp only [P3, aff] at e00 e10 e20 e01 e02 e11
  -- the six coefficients of the identity in `y` and `z`
  have hyy : α * (b₂ * b₃) = 0 := by linear_combination -(e10 + e20 - 2 * e00) / 2
  have hzz : α * (c₂ * c₃) = 0 := by linear_combination -(e01 + e02 - 2 * e00) / 2
  have hy : α * (b₂ * d₃ + d₂ * b₃) = 2 * B := by linear_combination (-(e10 - e20) / 2)
  have hz : α * (c₂ * d₃ + d₂ * c₃) = 2 * B := by linear_combination (-(e01 - e02) / 2)
  have h0 : α * (d₂ * d₃) = -2 * B := by linear_combination -e00
  have hyz : α * (b₂ * c₃ + c₂ * b₃) = -(2 * B - A) := by
    linear_combination (-e11 + e10 + e01 - e00)
  have hα : α ≠ 0 := by
    rintro rfl
    exact hB (by linarith)
  have hbb : b₂ * b₃ = 0 := (mul_eq_zero.1 hyy).resolve_left hα
  have hcc : c₂ * c₃ = 0 := (mul_eq_zero.1 hzz).resolve_left hα
  -- the product of the `y`- and `z`-coefficients equals that of the `yz`- and constant coefficients
  have key : (α * (b₂ * d₃ + d₂ * b₃)) * (α * (c₂ * d₃ + d₂ * c₃))
      = (α * (b₂ * c₃ + c₂ * b₃)) * (α * (d₂ * d₃)) := by
    rcases mul_eq_zero.1 hbb with hb | hb <;> rcases mul_eq_zero.1 hcc with hc | hc
    · exfalso; rw [hb, hc] at hyz; exact hC (by linarith)
    · rw [hb, hc]; ring
    · rw [hb, hc]; ring
    · exfalso; rw [hb, hc] at hyz; exact hC (by linarith)
  rw [hy, hz, hyz, h0] at key
  have : B * A = 0 := by linear_combination key / 2
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hB h1
  · exact hA h1

/-- Proposition 9.7 (ii): for nonzero `A`, `B` and `C = 2B - A`, `F3 A B ε` is not of the form `L₁ L₂ L₃ + κ` with affine forms
`Lᵢ = aᵢ x + bᵢ y + cᵢ z + dᵢ` over `ℚ`. -/
theorem no_linear_factorisation (A B ε κ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ a₃ b₃ c₃ d₃ : ℚ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : 2 * B - A ≠ 0) :
    ¬ ∀ x y z : ℚ, F3 A B ε x y z =
      (a₁ * x + aff b₁ c₁ d₁ y z) * (a₂ * x + aff b₂ c₂ d₂ y z) * (a₃ * x + aff b₃ c₃ d₃ y z) + κ := by
  intro h
  -- for fixed `y, z`, compare the coefficients of the cubic in `x`
  have coeff : ∀ y z : ℚ, a₁ * a₂ * a₃ = 0 ∧
      a₁ * a₂ * aff b₃ c₃ d₃ y z + a₁ * aff b₂ c₂ d₂ y z * a₃ + aff b₁ c₁ d₁ y z * a₂ * a₃ = 0 ∧
      P3 A B y z = a₁ * aff b₂ c₂ d₂ y z * aff b₃ c₃ d₃ y z + aff b₁ c₁ d₁ y z * a₂ * aff b₃ c₃ d₃ y z
        + aff b₁ c₁ d₁ y z * aff b₂ c₂ d₂ y z * a₃ := by
    intro y z
    obtain ⟨h3, h2, h1, -⟩ := cubic_eq_zero (c₃ := -(a₁ * a₂ * a₃))
      (c₂ := -(a₁ * a₂ * aff b₃ c₃ d₃ y z + a₁ * aff b₂ c₂ d₂ y z * a₃ + aff b₁ c₁ d₁ y z * a₂ * a₃))
      (c₁ := P3 A B y z - (a₁ * aff b₂ c₂ d₂ y z * aff b₃ c₃ d₃ y z
        + aff b₁ c₁ d₁ y z * a₂ * aff b₃ c₃ d₃ y z + aff b₁ c₁ d₁ y z * aff b₂ c₂ d₂ y z * a₃))
      (c₀ := (2 * B * y * z - 2 * B * y - 2 * B * z + 2 * B + ε) - κ
        - aff b₁ c₁ d₁ y z * aff b₂ c₂ d₂ y z * aff b₃ c₃ d₃ y z) (fun t => by
        have ht := h t y z
        simp only [F3, P3] at ht ⊢
        linear_combination ht)
    exact ⟨by linarith, by linarith, by linarith⟩
  have hP11 : P3 A B 1 1 ≠ 0 := by rw [P3_one]; exact hA
  obtain ⟨h3, h2, hP⟩ := coeff 1 1
  by_cases ha₁ : a₁ = 0 <;> by_cases ha₂ : a₂ = 0 <;> by_cases ha₃ : a₃ = 0
  · exact hP11 (by rw [hP, ha₁, ha₂, ha₃]; ring)
  · exact P3_not_product A B a₃ b₁ c₁ d₁ b₂ c₂ d₂ hA hB hC (fun y z => by
      rw [(coeff y z).2.2, ha₁, ha₂]; ring)
  · exact P3_not_product A B a₂ b₁ c₁ d₁ b₃ c₃ d₃ hA hB hC (fun y z => by
      rw [(coeff y z).2.2, ha₁, ha₃]; ring)
  · have hm : aff b₁ c₁ d₁ 1 1 * (a₂ * a₃) = 0 := by rw [ha₁] at h2; linear_combination h2
    have hm' := (mul_eq_zero.1 hm).resolve_right (mul_ne_zero ha₂ ha₃)
    exact hP11 (by rw [hP, ha₁, hm']; ring)
  · exact P3_not_product A B a₁ b₂ c₂ d₂ b₃ c₃ d₃ hA hB hC (fun y z => by
      rw [(coeff y z).2.2, ha₂, ha₃]; ring)
  · have hm : aff b₂ c₂ d₂ 1 1 * (a₁ * a₃) = 0 := by rw [ha₂] at h2; linear_combination h2
    have hm' := (mul_eq_zero.1 hm).resolve_right (mul_ne_zero ha₁ ha₃)
    exact hP11 (by rw [hP, ha₂, hm']; ring)
  · have hm : aff b₃ c₃ d₃ 1 1 * (a₁ * a₂) = 0 := by rw [ha₃] at h2; linear_combination h2
    have hm' := (mul_eq_zero.1 hm).resolve_right (mul_ne_zero ha₁ ha₂)
    exact hP11 (by rw [hP, ha₃, hm']; ring)
  · exact mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃ h3

/-! ### Fermat's test on an entry: Lemma 9.8 -/

/-- `(1 + q) ^ n = 1 + n q` modulo `q²`. -/
lemma one_add_pow_mod_sq (q n : ℕ) :
    ((1 + q : ℕ) : ZMod (q * q)) ^ n = ((1 + n * q : ℕ) : ZMod (q * q)) := by
  have hqq : ((q : ZMod (q * q)) * q) = 0 := by exact_mod_cast ZMod.natCast_self (q * q)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (n : ZMod (q * q)) * hqq

/-- Lemma 9.8. An integer `x > 0` prime to `N` with `a ^ N ≡ 1 (mod x)` for every `a` prime to `x` is squarefree,
and `q - 1 ∣ N` for every prime `q ∣ x`. -/
theorem fermat_entry {x N : ℕ} (hx : x ≠ 0) (hcop : Nat.Coprime x N)
    (h : ∀ a : ℕ, Nat.Coprime a x → a ^ N ≡ 1 [MOD x]) :
    Squarefree x ∧ ∀ q, q.Prime → q ∣ x → q - 1 ∣ N := by
  have : NeZero x := ⟨hx⟩
  -- every unit of `ZMod x` satisfies `u ^ N = 1`
  have hunit : ∀ u : (ZMod x)ˣ, u ^ N = 1 := by
    intro u
    have hc := h _ (ZMod.val_coe_unit_coprime u)
    rw [← ZMod.natCast_eq_natCast_iff] at hc
    push_cast at hc
    rw [ZMod.natCast_zmod_val] at hc
    ext
    rw [Units.val_pow_eq_pow_val, hc, Units.val_one]
  constructor
  · rw [Nat.squarefree_iff_prime_squarefree]
    intro q hq hqq
    have : NeZero (q * q) := ⟨Nat.mul_ne_zero hq.ne_zero hq.ne_zero⟩
    have hcop1 : Nat.Coprime (1 + q) (q * q) := by
      have : Nat.Coprime (1 + q) q := by
        rw [Nat.coprime_add_self_left]; exact Nat.coprime_one_left q
      exact Nat.Coprime.mul_right this this
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hqq (ZMod.unitOfCoprime (1 + q) hcop1)
    have h1 := congrArg (ZMod.unitsMap hqq) (hunit u)
    rw [map_pow, hu, map_one] at h1
    have h2 := congrArg Units.val h1
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, one_add_pow_mod_sq] at h2
    -- `1 + N q ≡ 1 (mod q²)`, so `q ∣ N`
    have h2' : ((1 + N * q : ℕ) : ZMod (q * q)) = ((1 : ℕ) : ZMod (q * q)) := by rw [h2, Nat.cast_one]
    have h3 : q * q ∣ q * N := by
      have := (Nat.modEq_iff_dvd' (by omega)).1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h2').symm
      simpa [mul_comm] using this
    have hqN : q ∣ N := Nat.dvd_of_mul_dvd_mul_left hq.pos h3
    have hqx : q ∣ x := dvd_trans (dvd_mul_right q q) hqq
    exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqx hcop) hqN)
  · intro q hq hqx
    have := Fact.mk hq
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
    have hord : orderOf g = q - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hqx g
    have h1 := congrArg (ZMod.unitsMap hqx) (hunit u)
    rw [map_pow, hu, map_one] at h1
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h1

/-- Lemma 9.8 for a tuple: if the entries are pairwise coprime, nonzero, their product is prime to `N`, and each entry
has the property of `fermat_entry`, then the product is squarefree and `q - 1 ∣ N` for every prime `q` dividing it. -/
theorem fermat_tuple {l : List ℕ} {N : ℕ} (hpos : ∀ x ∈ l, x ≠ 0) (hpw : l.Pairwise Nat.Coprime)
    (hcop : Nat.Coprime l.prod N) (h : ∀ x ∈ l, ∀ a : ℕ, Nat.Coprime a x → a ^ N ≡ 1 [MOD x]) :
    Squarefree l.prod ∧ ∀ q, q.Prime → q ∣ l.prod → q - 1 ∣ N := by
  have hent : ∀ x ∈ l, Squarefree x ∧ ∀ q, q.Prime → q ∣ x → q - 1 ∣ N := fun x hx =>
    fermat_entry (hpos x hx) (Nat.Coprime.coprime_dvd_left (List.dvd_prod hx) hcop) (h x hx)
  refine ⟨?_, ?_⟩
  · clear hcop h
    induction l with
    | nil => simp
    | cons y l ih =>
      rw [List.pairwise_cons] at hpw
      rw [List.prod_cons, Nat.squarefree_mul_iff]
      refine ⟨?_, (hent y (by simp)).1, ih (fun x hx => hpos x (by simp [hx])) hpw.2
        (fun x hx => hent x (by simp [hx]))⟩
      rw [Nat.coprime_list_prod_right_iff]
      exact hpw.1
  · intro q hq hqA
    obtain ⟨x, hx, hqx⟩ := (Nat.Prime.prime hq).dvd_prod_iff.1 hqA
    exact (hent x hx).2 q hq hqx

/-- For Lehmer's sign, `A = x₁ ⋯ x_k = 2 ∏ (xᵢ - 1) + 1`, with at least two entries, all at least `2` and pairwise
coprime, each passing Fermat's test to the exponent `A - 1`, the product `A` is a Carmichael number. -/
theorem fermat_tuple_carmichael {l : List ℕ} (hlen : 2 ≤ l.length) (h2 : ∀ x ∈ l, 2 ≤ x)
    (hpw : l.Pairwise Nat.Coprime) (heq : l.prod = 2 * pm1 l + 1)
    (h : ∀ x ∈ l, ∀ a : ℕ, Nat.Coprime a x → a ^ (l.prod - 1) ≡ 1 [MOD x]) :
    Nat.IsCarmichael l.prod := by
  have hA : 1 ≤ l.prod := by omega
  have hcop : Nat.Coprime l.prod (l.prod - 1) := by
    have := (Nat.coprime_self_sub_right (m := 1) (n := l.prod) hA).2 (Nat.coprime_one_right _)
    exact this
  obtain ⟨hsq, hdvd⟩ := fermat_tuple (fun x hx => by have := h2 x hx; omega) hpw hcop h
  obtain ⟨y, l', rfl⟩ : ∃ y l', l = y :: l' := by
    cases l with
    | nil => simp at hlen
    | cons y l' => exact ⟨y, l', rfl⟩
  have hy : 2 ≤ y := h2 y (by simp)
  have hl' : 2 ≤ l'.prod := by
    obtain ⟨z, l'', rfl⟩ : ∃ z l'', l' = z :: l'' := by
      cases l' with
      | nil => simp at hlen
      | cons z l'' => exact ⟨z, l'', rfl⟩
    have hz : 2 ≤ z := h2 z (by simp)
    have : 1 ≤ l''.prod := Nat.one_le_iff_ne_zero.2 (List.prod_ne_zero (fun h0 => by
      have := h2 0 (by simp [h0]); omega))
    rw [List.prod_cons]
    nlinarith
  rw [Nat.isCarmichael_iff_korselt]
  refine ⟨?_, ?_, hsq, hdvd⟩
  · rw [List.prod_cons]; nlinarith
  · rw [List.prod_cons]
    exact Nat.not_prime_mul (by omega) (by omega)

end LehmerTotient
