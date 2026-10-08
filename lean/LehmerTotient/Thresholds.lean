import LehmerTotient.Search
import LehmerTotient.Data

/-!
# The thresholds of Section 2

* `walk_sound`: a certified list of primes contains every prime of an arithmetic progression up
  to its last entry.
* `prod_bound`: `k` primes from such a progression have `∏ p / (p - 1)` at most, and
  `∏ (p - 1)` at least, the product over the first `k` entries of the list.
* `quotient_ge_four_imp`: Lemma 2.2, the bound `ω(n) ≥ 1540`.
* `quotient_eq_two_of_not_three_dvd`: Lemma 2.3.
* `quotient_eq_two_of_card_le_seven`: Corollary 2.4.
* `theorem_quotient`: the product bounds 33 and 1540 for a quotient at least 3.
-/

namespace LehmerTotient

open Nat Finset

/-! ### Certified lists of primes -/

/-- `walk d fuel x L W` runs through `x, x + d, x + 2 d, …` for `fuel` steps.  Each number met
must be either the next entry of `L` or have the next entry of `W` as a proper factor.  The run
stops with success when `L` is used up. -/
def walk (d : ℕ) : ℕ → ℕ → List ℕ → List ℕ → Bool
  | 0, _, _, _ => true
  | _ + 1, _, [], _ => true
  | fuel + 1, x, l :: L, W =>
    if x = l then walk d fuel (x + d) L W
    else match W with
      | [] => false
      | w :: W => (decide (1 < w) && decide (w < x) && x % w == 0) &&
          walk d fuel (x + d) (l :: L) W

lemma add_le_of_mod_eq {d x y : ℕ} (hxy : x < y) (h : y % d = x % d) :
    x + d ≤ y := by
  have h1 := Nat.div_add_mod y d
  have h2 := Nat.div_add_mod x d
  have h3 : x / d < y / d := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul_left d hc
    omega
  have h4 : d * (x / d + 1) ≤ d * (y / d) := Nat.mul_le_mul_left d h3
  rw [Nat.mul_add, mul_one] at h4
  omega

/-- Soundness of `walk`: every prime `y` of the progression that is at most some entry of `L`
is an entry of `L`. -/
theorem walk_sound {d : ℕ} : ∀ fuel x L W, walk d fuel x L W = true →
    ∀ y, x ≤ y → y < x + d * fuel → y % d = x % d → y.Prime → (∃ l ∈ L, y ≤ l) → y ∈ L := by
  intro fuel
  induction fuel with
  | zero => intro x L W _ y h1 h2; omega
  | succ fuel ih =>
    intro x L W hw y hxy hy hmod hp hl
    have hy' : y < x + d + d * fuel := by rw [Nat.mul_succ] at hy; omega
    have hmod' : y % d = (x + d) % d := by rw [Nat.add_mod_right]; exact hmod
    rcases L with _ | ⟨l, L⟩
    · obtain ⟨l, hl, _⟩ := hl
      cases hl
    by_cases hxl : x = l
    · have hw' : walk d fuel (x + d) L W = true := by
        simpa [walk, hxl] using hw
      rcases hxy.lt_or_eq with hlt | heq
      · have hxd := add_le_of_mod_eq hlt hmod
        refine List.mem_cons_of_mem l (ih (x + d) L W hw' y hxd hy' hmod' hp ?_)
        obtain ⟨l', hl', hyl'⟩ := hl
        rcases List.mem_cons.mp hl' with rfl | h
        · omega
        · exact ⟨l', h, hyl'⟩
      · subst heq
        rw [hxl]
        exact List.mem_cons_self
    · rcases W with _ | ⟨w, W⟩
      · simp [walk, hxl] at hw
      · have hw' : (1 < w ∧ w < x ∧ x % w = 0) ∧ walk d fuel (x + d) (l :: L) W = true := by
          simpa [walk, hxl, and_assoc] using hw
        obtain ⟨⟨hw1, hw2, hw3⟩, hw4⟩ := hw'
        rcases hxy.lt_or_eq with hlt | heq
        · exact ih (x + d) (l :: L) W hw4 y (add_le_of_mod_eq hlt hmod) hy' hmod' hp hl
        · subst heq
          have := hp.eq_one_or_self_of_dvd w (Nat.dvd_of_mod_eq_zero hw3)
          omega

/-- A Boolean test that a list is strictly increasing. -/
def increasing : List ℕ → Bool
  | a :: b :: l => decide (a < b) && increasing (b :: l)
  | _ => true

lemma pairwise_of_increasing : ∀ {L : List ℕ}, increasing L = true → L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_increasing h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hc)

/-- In a strictly increasing list, an entry below the `k`-th entry is among the first `k`. -/
lemma mem_take_of_lt {L : List ℕ} (hL : L.Pairwise (· < ·)) {k : ℕ} (hk : k < L.length)
    {y : ℕ} (hy : y ∈ L) (hlt : y < L[k]) : y ∈ L.take k := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have hjk : j < k := by
    by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with h | h
    · have := List.pairwise_iff_getElem.mp hL k j hk hj h
      omega
    · subst h
      omega
  rw [List.mem_iff_getElem]
  exact ⟨j, by simp [hjk, hj], by simp⟩

/-! ### Comparison with the first primes of a progression -/

/-- `∏_{l ∈ L} l / (l - 1)`. -/
noncomputable def PL (L : List ℕ) : ℚ := (L.map fun l : ℕ => (l : ℚ) / ((l : ℚ) - 1)).prod

lemma PL_eq (L : List ℕ) (h : ∀ l ∈ L, 2 ≤ l) :
    PL L = (L.prod : ℚ) / ((L.map fun l : ℕ => l - 1).prod : ℚ) := by
  induction L with
  | nil => simp [PL]
  | cons a L ih =>
    have ha : 2 ≤ a := h a List.mem_cons_self
    have ih' := ih fun l hl => h l (List.mem_cons_of_mem a hl)
    have hpos : (0 : ℚ) < ((L.map fun l : ℕ => l - 1).prod : ℕ) := by
      have : 0 < (L.map fun l : ℕ => l - 1).prod := by
        apply List.prod_pos
        intro x hx
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
        have := h l (List.mem_cons_of_mem a hl)
        omega
      exact_mod_cast this
    have ha1 : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have ha' : (a : ℚ) - 1 ≠ 0 := by
      have : (2 : ℚ) ≤ a := by exact_mod_cast ha
      linarith
    simp only [PL, List.map_cons, List.prod_cons] at ih' ⊢
    rw [ih', Nat.cast_mul, Nat.cast_mul, ha1]
    field_simp

lemma one_le_list_prod {l : List ℚ} (h : ∀ x ∈ l, 1 ≤ x) : 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    nlinarith

lemma one_le_PL (L : List ℕ) (h : ∀ l ∈ L, 2 ≤ l) : 1 ≤ PL L := by
  apply one_le_list_prod
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  exact (ratio_gt_one (h l hl)).le

lemma PL_take_le (L : List ℕ) (h : ∀ l ∈ L, 2 ≤ l) (k : ℕ) : PL (L.take k) ≤ PL L := by
  have e := List.prod_take_mul_prod_drop (L.map fun l : ℕ => (l : ℚ) / ((l : ℚ) - 1)) k
  rw [← List.map_take, ← List.map_drop] at e
  have h1 : 1 ≤ PL (L.drop k) := one_le_PL _ fun l hl => h l (List.mem_of_mem_drop hl)
  have h0 : 0 ≤ PL (L.take k) := by
    have := one_le_PL (L.take k) fun l hl => h l (List.mem_of_mem_take hl)
    linarith
  unfold PL at h1 h0 ⊢
  rw [← e]
  nlinarith

/-- The comparison lemma behind Lemmas 2.2 and 2.3. -/
theorem prod_bound (good : ℕ → Prop) (L : List ℕ) (hL : L.Pairwise (· < ·))
    (h2 : ∀ l ∈ L, 2 ≤ l) (hcov : ∀ y, good y → (∃ l ∈ L, y ≤ l) → y ∈ L) :
    ∀ S : Finset ℕ, (∀ p ∈ S, good p) → (∀ p ∈ S, 2 ≤ p) → S.card ≤ L.length →
      P S ≤ PL (L.take S.card) ∧
        ((L.take S.card).map fun l : ℕ => l - 1).prod ≤ ∏ p ∈ S, (p - 1) := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _ _ _; simp [P, PL]
  | insert a s hlt ih =>
    intro hgood h2S hcard
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has] at hcard ⊢
    have hk : s.card < L.length := by omega
    -- the largest element `a` is at least the `k`-th entry of `L`
    have hak : L[s.card] ≤ a := by
      by_contra hc
      push Not at hc
      have hsub : insert a s ⊆ (L.take s.card).toFinset := by
        intro y hy
        have hya : y ≤ a := by
          rcases mem_insert.mp hy with rfl | h
          · exact le_rfl
          · exact (hlt y h).le
        have hyL : y ∈ L := hcov y (hgood y hy) ⟨L[s.card], List.getElem_mem _, by omega⟩
        exact List.mem_toFinset.mpr (mem_take_of_lt hL hk hyL (by omega))
      have h1 := card_le_card hsub
      rw [card_insert_of_notMem has] at h1
      have h3 := List.toFinset_card_le (L.take s.card)
      simp only [List.length_take] at h3
      omega
    obtain ⟨ih1, ih2⟩ := ih (fun p hp => hgood p (mem_insert_of_mem hp))
      (fun p hp => h2S p (mem_insert_of_mem hp)) (by omega)
    have hLk : 2 ≤ L[s.card] := h2 _ (List.getElem_mem _)
    have htake : L.take (s.card + 1) = L.take s.card ++ [L[s.card]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      rfl
    rw [htake]
    have hf := ratio_le_ratio hLk hak
    have hPs : 0 ≤ P s := (P_pos fun p hp => h2S p (mem_insert_of_mem hp)).le
    have hfa : 0 ≤ (a : ℚ) / ((a : ℚ) - 1) :=
      (ratio_gt_one (hLk.trans hak)).le.trans' zero_le_one
    have key := mul_le_mul ih1 hf hfa (hPs.trans ih1)
    constructor
    · unfold P PL at *
      rw [prod_insert has, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton]
      linarith
    · rw [prod_insert has, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, mul_comm (a - 1)]
      exact Nat.mul_le_mul ih2 (by omega)

/-! ### Consequences for a solution -/

section Solution

variable {n : ℕ} {ε M : ℤ}

/-- Lemma 2.1(iii) in rational form: `∏_{p ∣ n} p / (p - 1) = M - ε / φ n`. -/
theorem P_eq_quotient (hsq : Squarefree n) (hM : (n : ℤ) + ε = M * φ n) :
    P n.primeFactors = M - (ε : ℚ) / φ n := by
  have hφ := totient_pos_of_squarefree hsq
  rw [P_eq_div hsq, eq_sub_iff_add_eq, ← add_div, div_eq_iff hφ.ne']
  exact_mod_cast hM

/-- Every prime factor of an odd `n` with `3 ∤ n` is at least `5`. -/
lemma five_le_of_mem {n p : ℕ} (hodd : Odd n) (h3 : ¬ 3 ∣ n) (hp : p ∈ n.primeFactors) :
    5 ≤ p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  have h2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn)
  have h3' : p ≠ 3 := by rintro rfl; exact h3 hpn
  have h4 : p ≠ 4 := by rintro rfl; norm_num at hpp
  have := hpp.two_le
  omega

/-- The bound `M < 3` from a list of primes: `M ≤ ∏ p/(p-1) + 1/φ(n)`, and both terms are
controlled by the first `ω(n)` entries of the list. -/
lemma quotient_lt_three (hε : IsSign ε) (hsq : Squarefree n) (hM : (n : ℤ) + ε = M * φ n)
    (good : ℕ → Prop) (L : List ℕ) (hL : L.Pairwise (· < ·)) (h2 : ∀ l ∈ L, 2 ≤ l)
    (hcov : ∀ y, good y → (∃ l ∈ L, y ≤ l) → y ∈ L) (hgood : ∀ p ∈ n.primeFactors, good p)
    (hcard : n.primeFactors.card ≤ L.length)
    (hnum : (L.take n.primeFactors.card).prod + 1 <
      3 * ((L.take n.primeFactors.card).map fun l : ℕ => l - 1).prod) :
    M < 3 := by
  have h2S : ∀ p ∈ n.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  obtain ⟨hP, hφ⟩ := prod_bound good L hL h2 hcov _ hgood h2S hcard
  set T := L.take n.primeFactors.card
  have hT2 : ∀ l ∈ T, 2 ≤ l := fun l hl => h2 l (List.mem_of_mem_take hl)
  have hφpos := totient_pos_of_squarefree hsq
  rw [← totient_eq_prod_of_squarefree hsq] at hφ
  have hQpos : 0 < (T.map fun l : ℕ => l - 1).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    have := hT2 l hl
    omega
  have hQ : (0 : ℚ) < ((T.map fun l : ℕ => l - 1).prod : ℕ) := by exact_mod_cast hQpos
  have hφQ : ((T.map fun l : ℕ => l - 1).prod : ℚ) ≤ φ n := by exact_mod_cast hφ
  have hPM := P_eq_quotient hsq hM
  -- `M ≤ P + 1/φ ≤ PL T + 1/Q = (Π + 1)/Q < 3`
  have hεφ : (ε : ℚ) / φ n ≤ 1 / ((T.map fun l : ℕ => l - 1).prod : ℕ) := by
    have h1 : (ε : ℚ) / φ n ≤ 1 / φ n := by
      apply div_le_div_of_nonneg_right _ hφpos.le
      rcases hε with rfl | rfl <;> norm_num
    exact h1.trans (one_div_le_one_div_of_le hQ hφQ)
  have hnum' : ((T.prod : ℕ) : ℚ) + 1 < 3 * ((T.map fun l : ℕ => l - 1).prod : ℕ) := by
    exact_mod_cast hnum
  have hPL := PL_eq T hT2
  have key : (M : ℚ) < 3 := by
    have : (M : ℚ) = P n.primeFactors + (ε : ℚ) / φ n := by rw [hPM]; ring
    rw [this]
    have h3 : PL T + 1 / ((T.map fun l : ℕ => l - 1).prod : ℕ) < 3 := by
      rw [hPL, ← add_div, div_lt_iff₀ hQ]
      linarith
    linarith
  exact_mod_cast key

end Solution

/-! ### Lemma 2.3 and Corollary 2.4 -/

lemma primesFrom5_increasing : increasing primesFrom5 = true := by decide +kernel

lemma primesFrom5_walk : walk 2 70 5 primesFrom5 witnessesFrom5 = true := by decide +kernel

lemma primesFrom5_last : ∀ l ∈ primesFrom5, l ≤ 139 := by decide +kernel

lemma primesFrom5_cover : ∀ y, (y.Prime ∧ 5 ≤ y) → (∃ l ∈ primesFrom5, y ≤ l) →
    y ∈ primesFrom5 := by
  rintro y ⟨hp, h5⟩ ⟨l, hl, hyl⟩
  have hl139 : l ≤ 139 := primesFrom5_last l hl
  apply walk_sound 70 5 _ _ primesFrom5_walk y h5 (by omega) _ hp ⟨l, hl, hyl⟩
  have := hp.eq_one_or_self_of_dvd 2
  rcases Nat.even_or_odd y with ⟨m, hm⟩ | ⟨m, hm⟩
  · have := this ⟨m, by omega⟩
    omega
  · omega

lemma primesFrom5_two_le : ∀ l ∈ primesFrom5, 2 ≤ l := by decide +kernel

lemma primesFrom5_length : primesFrom5.length = 32 := by decide +kernel

lemma primesFrom5_num : ∀ k ≤ 32, (primesFrom5.take k).prod + 1 <
    3 * ((primesFrom5.take k).map fun l : ℕ => l - 1).prod := by decide +kernel

/-- Lemma 2.3: if `3 ∤ n` and `ω(n) ≤ 32`, then `M = 2`. -/
theorem quotient_eq_two_of_not_three_dvd {n : ℕ} {ε M : ℤ} (hε : IsSign ε) (hn : 1 < n)
    (hc : ¬ n.Prime) (hM : (n : ℤ) + ε = M * φ n) (h3 : ¬ 3 ∣ n)
    (hk : n.primeFactors.card ≤ 32) : M = 2 := by
  have hdvd : (φ n : ℤ) ∣ n + ε := ⟨M, by rw [hM]; ring⟩
  have hsq := squarefree_of_dvd hε hdvd
  have hn2 : 2 < n := by
    by_contra h
    interval_cases n
    exact hc Nat.prime_two
  have hodd := odd_of_dvd hε hdvd hn2
  have h2M := two_le_quotient hε hn hc hM
  have hlt := quotient_lt_three hε hsq hM (fun y => y.Prime ∧ 5 ≤ y) primesFrom5
    (pairwise_of_increasing primesFrom5_increasing) primesFrom5_two_le primesFrom5_cover
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, five_le_of_mem hodd h3 hp⟩)
    (by rw [primesFrom5_length]; exact hk) (primesFrom5_num _ hk)
  omega

lemma oddPrimes7_increasing : increasing oddPrimes7 = true := by decide +kernel

lemma oddPrimes7_walk : walk 2 9 3 oddPrimes7 witnessesOdd7 = true := by decide +kernel

lemma oddPrimes7_last : ∀ l ∈ oddPrimes7, l ≤ 19 := by decide +kernel

lemma oddPrimes7_cover : ∀ y, (y.Prime ∧ 3 ≤ y) → (∃ l ∈ oddPrimes7, y ≤ l) →
    y ∈ oddPrimes7 := by
  rintro y ⟨hp, h3⟩ ⟨l, hl, hyl⟩
  have hl19 : l ≤ 19 := oddPrimes7_last l hl
  apply walk_sound 9 3 _ _ oddPrimes7_walk y h3 (by omega) _ hp ⟨l, hl, hyl⟩
  have := hp.eq_one_or_self_of_dvd 2
  rcases Nat.even_or_odd y with ⟨m, hm⟩ | ⟨m, hm⟩
  · have := this ⟨m, by omega⟩
    omega
  · omega

lemma oddPrimes7_two_le : ∀ l ∈ oddPrimes7, 2 ≤ l := by decide +kernel

lemma oddPrimes7_length : oddPrimes7.length = 7 := by decide +kernel

lemma oddPrimes7_num : ∀ k ≤ 7, (oddPrimes7.take k).prod + 1 <
    3 * ((oddPrimes7.take k).map fun l : ℕ => l - 1).prod := by decide +kernel

/-- Corollary 2.4: a solution of `φ(n) ∣ n + 1` with `n > 3` and `ω(n) ≤ 7` has
`n + 1 = 2 φ(n)`. -/
theorem quotient_eq_two_of_card_le_seven {n : ℕ} {M : ℤ} (hn : 3 < n)
    (hM : (n : ℤ) + 1 = M * φ n) (hk : n.primeFactors.card ≤ 7) : M = 2 := by
  have hdvd : (φ n : ℤ) ∣ n + 1 := ⟨M, by rw [hM]; ring⟩
  have hε : IsSign 1 := Or.inl rfl
  have hsq := squarefree_of_dvd hε hdvd
  have hodd := odd_of_dvd hε hdvd (by omega)
  have hc := not_prime_of_dvd_add_one hdvd hn
  have h2M := two_le_quotient hε (by omega) hc hM
  have hgood : ∀ p ∈ n.primeFactors, p.Prime ∧ 3 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, ?_⟩
    have h2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
    have := hpp.two_le
    omega
  have hlt := quotient_lt_three hε hsq hM (fun y => y.Prime ∧ 3 ≤ y) oddPrimes7
    (pairwise_of_increasing oddPrimes7_increasing) oddPrimes7_two_le oddPrimes7_cover hgood
    (by rw [oddPrimes7_length]; exact hk) (oddPrimes7_num _ hk)
  omega

/-! ### Lemma 2.2: the bound `1540` -/

lemma primesMod6_increasing : increasing primesMod6 = true := by decide +kernel

lemma primesMod6_walk : walk 6 4657 5 primesMod6 witnessesMod6 = true := by decide +kernel

lemma primesMod6_last : ∀ l ∈ primesMod6, l ≤ 27941 := by decide +kernel

lemma primesMod6_cover : ∀ y, (y.Prime ∧ y % 6 = 5) → (∃ l ∈ primesMod6, y ≤ l) →
    y ∈ primesMod6 := by
  rintro y ⟨hp, h5⟩ ⟨l, hl, hyl⟩
  have := primesMod6_last l hl
  exact walk_sound 4657 5 _ _ primesMod6_walk y (by omega) (by omega)
    (by omega) hp ⟨l, hl, hyl⟩

lemma primesMod6_two_le : ∀ l ∈ primesMod6, 2 ≤ l := by decide +kernel

lemma primesMod6_length : primesMod6.length = 1538 := by decide +kernel

/-- `(3/2) ∏ q / (q - 1) ≤ 4` over the first 1538 primes `q ≡ 2 (mod 3)` from `5` on. -/
lemma primesMod6_num : 3 * primesMod6.prod ≤ 8 * (primesMod6.map fun l : ℕ => l - 1).prod := by
  decide +kernel

/-- Lemma 2.2, last part: if `3 ∣ n` and `n / φ(n) > 4`, then `ω(n) ≥ 1540`. -/
theorem card_ge_of_three_dvd {n : ℕ} {ε : ℤ} (hε : IsSign ε) (hn : 2 < n)
    (h : (φ n : ℤ) ∣ n + ε) (h3 : 3 ∣ n) (h4 : 4 < (n : ℚ) / φ n) :
    1540 ≤ n.primeFactors.card := by
  have hsq := squarefree_of_dvd hε h
  have hodd := odd_of_dvd hε h hn
  have hn0 : n ≠ 0 := by omega
  have h3S : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, hn0⟩
  set S' := n.primeFactors.erase 3
  have hgood : ∀ p ∈ S', p.Prime ∧ p % 6 = 5 := by
    intro p hp
    obtain ⟨hp3, hpS⟩ := mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpS
    have hpn := Nat.dvd_of_mem_primeFactors hpS
    have hmod := mod_three_of_three_dvd hε h h3 hpp hpn hp3
    have h2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn)
    have hpodd : p % 2 = 1 := by
      rcases Nat.even_or_odd p with ⟨m, hm⟩ | ⟨m, hm⟩
      · have := hpp.eq_one_or_self_of_dvd 2 ⟨m, by omega⟩
        omega
      · omega
    refine ⟨hpp, by omega⟩
  by_contra hlt
  push Not at hlt
  have hcard : S'.card ≤ primesMod6.length := by
    rw [primesMod6_length, card_erase_of_mem h3S]
    omega
  have h2S : ∀ p ∈ S', 2 ≤ p := fun p hp => (hgood p hp).1.two_le
  obtain ⟨hP, -⟩ := prod_bound (fun y => y.Prime ∧ y % 6 = 5) primesMod6
    (pairwise_of_increasing primesMod6_increasing) primesMod6_two_le primesMod6_cover S'
    hgood h2S hcard
  have hmono := PL_take_le primesMod6 primesMod6_two_le S'.card
  have hnum : PL primesMod6 ≤ 8 / 3 := by
    rw [PL_eq _ primesMod6_two_le]
    have hQ : (0 : ℚ) < ((primesMod6.map fun l : ℕ => l - 1).prod : ℕ) := by
      have : 0 < (primesMod6.map fun l : ℕ => l - 1).prod := by
        apply List.prod_pos
        intro x hx
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
        have := primesMod6_two_le l hl
        omega
      exact_mod_cast this
    rw [div_le_iff₀ hQ]
    have : (3 : ℚ) * (primesMod6.prod : ℚ) ≤
        8 * ((primesMod6.map fun l : ℕ => l - 1).prod : ℚ) := by
      exact_mod_cast primesMod6_num
    linarith
  -- `n / φ(n) = (3/2) P S'`
  have hsplit : P n.primeFactors = (3 : ℚ) / 2 * P S' := by
    unfold P
    rw [← mul_prod_erase _ _ h3S]
    congr 1
    norm_num
  rw [← P_eq_div hsq, hsplit] at h4
  linarith

/-- Lemma 2.2: if `3 ∣ n` then `2 M ≡ ε (mod 3)`; hence `M ≥ 4` for `ε = -1`, `M = 2` or `M ≥ 5`
for `ε = 1`, and `ω(n) ≥ 1540` when `M ≥ 4`. -/
theorem three_dvd_consequences {n : ℕ} {ε M : ℤ} (hε : IsSign ε) (hn : 1 < n)
    (hc : ¬ n.Prime) (hM : (n : ℤ) + ε = M * φ n) (h3 : 3 ∣ n) :
    (ε = -1 → 4 ≤ M) ∧ (ε = 1 → M = 2 ∨ 5 ≤ M) ∧ (4 ≤ M → 1540 ≤ n.primeFactors.card) := by
  have hdvd : (φ n : ℤ) ∣ n + ε := ⟨M, by rw [hM]; ring⟩
  have hn2 : 2 < n := by
    by_contra h
    interval_cases n
    exact hc Nat.prime_two
  have h2M := two_le_quotient hε hn hc hM
  have hz := quotient_mod_three hε (by omega) hM h3
  have h3M : (3 : ℤ) ∣ 2 * M - ε := by
    have : ((2 * M - ε : ℤ) : ZMod 3) = 0 := by
      push_cast
      rw [hz]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp this
  refine ⟨fun he => by subst he; omega, fun he => by subst he; omega, fun h4 => ?_⟩
  apply card_ge_of_three_dvd hε hn2 hdvd h3
  have hsq := squarefree_of_dvd hε hdvd
  have hφ := totient_pos_of_squarefree hsq
  have hPM := P_eq_quotient hsq hM
  rw [← P_eq_div hsq, hPM]
  rcases hε with rfl | rfl
  · -- `ε = 1`: `M ≥ 5` and `1 / φ(n) ≤ 1/2`
    have h5 : (5 : ℚ) ≤ M := by exact_mod_cast (show 5 ≤ M by omega)
    have hφ2 : (2 : ℚ) ≤ φ n := by
      have := Nat.totient_even hn2
      have hpos : 0 < φ n := Nat.totient_pos.mpr (by omega)
      obtain ⟨m, hm⟩ := this
      exact_mod_cast (show 2 ≤ φ n by omega)
    have : ((1 : ℤ) : ℚ) / φ n ≤ 1 / 2 := by
      push_cast
      exact one_div_le_one_div_of_le (by norm_num) hφ2
    linarith
  · have h4' : (4 : ℚ) ≤ M := by exact_mod_cast h4
    have : 0 < (1 : ℚ) / φ n := by positivity
    push_cast
    rw [neg_div, sub_neg_eq_add]
    linarith

/-! ### Quotient at least 3 -/

/-- The product bounds for a quotient at least 3: a solution of `φ(n) ∣ n + 1` with `n > 3` and
`(n + 1) / φ(n) ≥ 3` has `ω(n) ≥ 33`, and `ω(n) ≥ 1540` if `3 ∣ n`.  Theorem 1.5 of the paper improves
both bounds with the search of Proposition 2.5, which is not formalised. -/
theorem theorem_quotient {n : ℕ} {M : ℤ} (hn : 3 < n) (hM : (n : ℤ) + 1 = M * φ n)
    (h3M : 3 ≤ M) : 33 ≤ n.primeFactors.card ∧ (3 ∣ n → 1540 ≤ n.primeFactors.card) := by
  have hdvd : (φ n : ℤ) ∣ n + 1 := ⟨M, by rw [hM]; ring⟩
  have hc := not_prime_of_dvd_add_one hdvd hn
  have hε : IsSign 1 := Or.inl rfl
  have h1540 : 3 ∣ n → 1540 ≤ n.primeFactors.card := by
    intro h3
    obtain ⟨-, h2, h4⟩ := three_dvd_consequences hε (by omega) hc hM h3
    rcases h2 rfl with h | h
    · omega
    · exact h4 (by omega)
  refine ⟨?_, h1540⟩
  by_cases h3 : 3 ∣ n
  · have := h1540 h3
    omega
  · by_contra hk
    push Not at hk
    have := quotient_eq_two_of_not_three_dvd hε (by omega) hc hM h3 (by omega)
    omega

end LehmerTotient
