import LehmerTotient.Imports
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Pseudo-solutions prime to 3: extension to every larger length (Section 9.6)

A list `l` of natural numbers is a *pseudo-solution prime to 3* of the product equation
`x₁ ⋯ x_k + ε = 2 ∏ (xᵢ - 1)` if its entries are strictly increasing, at least `5`, odd and not divisible by `3`,
satisfy `gcd(xᵢ, xⱼ - 1) = 1` for all `i, j`, and satisfy the equation.

* `companion_step`: if `l` solves the equation with `ε = +1` and `3 ∣ ∏ (xᵢ - 1)`, then so does `l ++ [2 ∏ (xᵢ - 1) + 1]`.
* `lehmer_step`: under the same hypotheses, `l ++ [∏ xᵢ]` solves the equation with `ε = -1`.
* `companion_all`, `lehmer_all`: one companion pseudo-solution prime to 3 with `k` entries and `3 ∣ ∏ (xᵢ - 1)` gives
  companion pseudo-solutions prime to 3 with every length `≥ k` and Lehmer pseudo-solutions with every length `≥ k + 1`.
-/

namespace LehmerTotient

/-- `∏ (x - 1)` over a list. -/
def pm1 (l : List ℕ) : ℕ := (l.map (· - 1)).prod

/-- The conditions on the entries: increasing, `≥ 5`, odd, prime to `3`, and `gcd(x, y - 1) = 1`. -/
def EntriesOK (l : List ℕ) : Prop :=
  l.Pairwise (· < ·) ∧ (∀ x ∈ l, 5 ≤ x ∧ x % 2 = 1 ∧ ¬ 3 ∣ x) ∧ (∀ x ∈ l, ∀ y ∈ l, Nat.Coprime x (y - 1))

/-- A pseudo-solution prime to 3 of `x₁ ⋯ x_k + 1 = 2 ∏ (xᵢ - 1)` (companion sign). -/
def CompanionPS (l : List ℕ) : Prop := EntriesOK l ∧ l.prod + 1 = 2 * pm1 l

/-- A pseudo-solution prime to 3 of `x₁ ⋯ x_k - 1 = 2 ∏ (xᵢ - 1)` (Lehmer's sign). -/
def LehmerPS (l : List ℕ) : Prop := EntriesOK l ∧ l.prod = 2 * pm1 l + 1

lemma pm1_append (l : List ℕ) (x : ℕ) : pm1 (l ++ [x]) = pm1 l * (x - 1) := by
  simp [pm1, List.map_append, List.prod_append]

lemma prod_append_single (l : List ℕ) (x : ℕ) : (l ++ [x]).prod = l.prod * x := by
  simp [List.prod_append]

lemma sub_one_dvd_pm1 {l : List ℕ} {y : ℕ} (hy : y ∈ l) : y - 1 ∣ pm1 l :=
  List.dvd_prod (List.mem_map.2 ⟨y, hy, rfl⟩)

lemma coprime_pm1 {l : List ℕ} {x : ℕ} (h : ∀ y ∈ l, Nat.Coprime x (y - 1)) : Nat.Coprime x (pm1 l) := by
  unfold pm1
  rw [Nat.coprime_list_prod_right_iff]
  intro n hn
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
  exact h y hy

/-- In a nonempty companion pseudo-solution, every entry is at most `∏ (xᵢ - 1) + 1`, and `∏ (xᵢ - 1) ≥ 4`. -/
lemma pm1_bounds {l : List ℕ} (h : CompanionPS l) (hne : l ≠ []) :
    4 ≤ pm1 l ∧ ∀ y ∈ l, y ≤ pm1 l + 1 := by
  have hpos : 0 < pm1 l := by have := h.2; omega
  have hle : ∀ y ∈ l, y ≤ pm1 l + 1 := by
    intro y hy
    have := Nat.le_of_dvd hpos (sub_one_dvd_pm1 hy)
    omega
  refine ⟨?_, hle⟩
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil l hne
  have h5 := (h.1.2.1 y hy).1
  have := Nat.le_of_dvd hpos (sub_one_dvd_pm1 hy)
  omega

/-- Appending `2 ∏ (xᵢ - 1) + 1` to a companion pseudo-solution prime to 3 gives another one. -/
theorem companion_step {l : List ℕ} (h : CompanionPS l) (h3 : 3 ∣ pm1 l) (hne : l ≠ []) :
    CompanionPS (l ++ [2 * pm1 l + 1]) ∧ 3 ∣ pm1 (l ++ [2 * pm1 l + 1]) := by
  obtain ⟨⟨hpw, hent, hcop⟩, heq⟩ := h
  obtain ⟨hQ4, hle⟩ := pm1_bounds ⟨⟨hpw, hent, hcop⟩, heq⟩ hne
  set Q := pm1 l with hQdef
  set x := 2 * Q + 1 with hx
  have hx1 : x - 1 = 2 * Q := by omega
  have hxQ : Nat.Coprime x Q := by
    have h2Q : 2 * Q + 1 = Q * 2 + 1 := by ring
    rw [hx, h2Q, Nat.coprime_mul_left_add_left]
    exact Nat.coprime_one_left Q
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨hpw, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    have := hle a ha
    omega
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hent y hy
    · rw [List.mem_singleton] at hy
      subst hy
      obtain ⟨t, ht⟩ := h3
      refine ⟨by omega, by omega, ?_⟩
      rintro ⟨u, hu⟩
      omega
  · intro a ha b hb
    rcases List.mem_append.1 ha with ha | ha <;> rcases List.mem_append.1 hb with hb | hb
    · exact hcop a ha b hb
    · rw [List.mem_singleton] at hb
      subst hb
      rw [hx1]
      have h2 : Nat.Coprime a 2 := by
        rw [Nat.coprime_comm, Nat.coprime_two_left]
        exact Nat.odd_iff.2 (hent a ha).2.1
      exact Nat.Coprime.mul_right h2 (coprime_pm1 (hcop a ha))
    · rw [List.mem_singleton] at ha
      subst ha
      exact Nat.Coprime.coprime_dvd_right (sub_one_dvd_pm1 hb) hxQ
    · rw [List.mem_singleton] at ha hb
      subst ha; subst hb
      rw [hx1, hx, Nat.coprime_self_add_left]
      exact Nat.coprime_one_left _
  · rw [prod_append_single, pm1_append, hx1]
    have : 2 * (Q * (2 * Q)) = (2 * Q) * (2 * Q) := by ring
    rw [this, ← heq, hx, ← heq]
    ring
  · rw [pm1_append]
    exact Dvd.dvd.mul_right h3 _

/-- Appending `∏ xᵢ` to a companion pseudo-solution prime to 3 gives a Lehmer pseudo-solution prime to 3. -/
theorem lehmer_step {l : List ℕ} (h : CompanionPS l) (h3 : 3 ∣ pm1 l) (hne : l ≠ []) :
    LehmerPS (l ++ [l.prod]) := by
  obtain ⟨⟨hpw, hent, hcop⟩, heq⟩ := h
  obtain ⟨hQ4, hle⟩ := pm1_bounds ⟨⟨hpw, hent, hcop⟩, heq⟩ hne
  set Q := pm1 l with hQdef
  set P := l.prod with hP
  have hPP : Nat.Coprime P (P - 1) := by
    have hP1 : P = (P - 1) + 1 := by omega
    conv_lhs => rw [hP1]
    rw [Nat.coprime_self_add_left]
    exact Nat.coprime_one_left _
  have hPQ : Nat.Coprime P Q := by
    have h2 : Nat.Coprime P (2 * Q) := by
      rw [← heq, Nat.coprime_self_add_right]
      exact Nat.coprime_one_right _
    exact Nat.Coprime.coprime_mul_left_right h2
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨hpw, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    have := hle a ha
    omega
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hent y hy
    · rw [List.mem_singleton] at hy
      subst hy
      obtain ⟨t, ht⟩ := h3
      refine ⟨by omega, by omega, ?_⟩
      rintro ⟨u, hu⟩
      omega
  · intro a ha b hb
    rcases List.mem_append.1 ha with ha | ha <;> rcases List.mem_append.1 hb with hb | hb
    · exact hcop a ha b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact Nat.Coprime.coprime_dvd_left (List.dvd_prod ha) hPP
    · rw [List.mem_singleton] at ha
      subst ha
      exact Nat.Coprime.coprime_dvd_right (sub_one_dvd_pm1 hb) hPQ
    · rw [List.mem_singleton] at ha hb
      subst ha; subst hb
      exact hPP
  · rw [prod_append_single, pm1_append, ← hP]
    obtain ⟨m, hm⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
    have h2 : 2 * (Q * (P - 1)) = (2 * Q) * (P - 1) := by ring
    rw [h2, ← heq, hm, Nat.add_sub_cancel]
    ring

/-- From one companion pseudo-solution prime to 3 with `3 ∣ ∏ (xᵢ - 1)`: one of every larger length. -/
theorem companion_all {l₀ : List ℕ} (h : CompanionPS l₀) (h3 : 3 ∣ pm1 l₀) (hne : l₀ ≠ []) (n : ℕ) :
    ∃ l, l.length = l₀.length + n ∧ CompanionPS l ∧ 3 ∣ pm1 l ∧ l ≠ [] := by
  induction n with
  | zero => exact ⟨l₀, rfl, h, h3, hne⟩
  | succ n ih =>
    obtain ⟨l, hl, hc, h3l, hnel⟩ := ih
    obtain ⟨hc', h3'⟩ := companion_step hc h3l hnel
    refine ⟨l ++ [2 * pm1 l + 1], ?_, hc', h3', by simp⟩
    simp [hl]; omega

/-- From one companion pseudo-solution prime to 3 with `k` entries: Lehmer pseudo-solutions of every length `> k`. -/
theorem lehmer_all {l₀ : List ℕ} (h : CompanionPS l₀) (h3 : 3 ∣ pm1 l₀) (hne : l₀ ≠ []) (n : ℕ) :
    ∃ l, l.length = l₀.length + n + 1 ∧ LehmerPS l := by
  obtain ⟨l, hl, hc, h3l, hnel⟩ := companion_all h h3 hne n
  exact ⟨l ++ [l.prod], by simp [hl], lehmer_step hc h3l hnel⟩

end LehmerTotient
