import LehmerTotient.Product
import LehmerTotient.Search
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin

/-!
# A finite universe for each factor count, with an explicit unproved endpoint

This file does not prove Lehmer's conjecture.  Its endpoint is an equivalence
with emptiness of a specified finite set for EVERY natural factor count.
The bound is a corollary of the existing Cook--Nielsen product argument,
not a newly claimed analytic bound.  It does not formalise the Python DFS.
-/

open Nat Finset

namespace LehmerFollowup

def Counterexample (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ φ n ∣ n - 1

instance (n : ℕ) : Decidable (Counterexample n) :=
  inferInstanceAs (Decidable (1 < n ∧ ¬ n.Prime ∧ φ n ∣ n - 1))

def bound (k : ℕ) : ℕ := 2 ^ (2 ^ k)

/-- A sorted squarefree factorisation transfers the existing product bound
to the actual totient equation, for every possible number of factors. -/
theorem counterexample_lt_bound {n : ℕ} (hn : Counterexample n) :
    n < bound n.primeFactors.card := by
  obtain ⟨hn1, hcomp, M, hM⟩ := hn
  have hM' : n - 1 = M * φ n := by simpa [Nat.mul_comm] using hM
  have heq : n = M * φ n + 1 := by omega
  have heqZ : (n : ℤ) + (-1 : ℤ) = (M : ℤ) * φ n := by
    have : (n : ℤ) = (M : ℤ) * φ n + 1 := by exact_mod_cast heq
    omega
  have hdivZ : (φ n : ℤ) ∣ (n : ℤ) + (-1 : ℤ) := by
    exact ⟨(M : ℤ), by nlinarith [heqZ]⟩
  have hsign : LehmerTotient.IsSign (-1 : ℤ) := Or.inr rfl
  have hsq := LehmerTotient.squarefree_of_dvd hsign hdivZ
  have hM2Z := LehmerTotient.two_le_quotient hsign hn1 hcomp heqZ
  have hM2 : 2 ≤ M := by exact_mod_cast hM2Z
  let k := n.primeFactors.card
  let e : Fin k ↪o ℕ := n.primeFactors.orderEmbOfFin rfl
  let p : ℕ → ℕ := fun i => if hi : i < k then e ⟨i, hi⟩ else 2
  have hprod (f : ℕ → ℕ) :
      (∏ i ∈ range k, f (p i)) = ∏ q ∈ n.primeFactors, f q := by
    rw [Finset.prod_range]
    calc
      (∏ i : Fin k, f (p i)) = ∏ i : Fin k, f (e i) := by
        apply Finset.prod_congr rfl
        intro i _
        simp [p, i.isLt]
      _ = ∏ q ∈ n.primeFactors, f q := by
        have he := n.primeFactors.map_orderEmbOfFin_univ (k := k) rfl
        have hh := congrArg (fun s : Finset ℕ => ∏ q ∈ s, f q) he
        simpa only [Finset.prod_map, RelEmbedding.coe_toEmbedding] using hh
  have hX : LehmerTotient.Product.X p k = n := by
    change (∏ i ∈ range k, p i) = n
    calc
      _ = ∏ q ∈ n.primeFactors, q := hprod id
      _ = n := Nat.prod_primeFactors_of_squarefree hsq
  have hY : LehmerTotient.Product.Y p k = φ n := by
    change (∏ i ∈ range k, (p i - 1)) = φ n
    calc
      _ = ∏ q ∈ n.primeFactors, (q - 1) := hprod (fun q => q - 1)
      _ = φ n := (LehmerTotient.totient_eq_prod_of_squarefree hsq).symm
  have hk : 1 ≤ k := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hn1)
  have hp : ∀ i < k, 2 ≤ p i := by
    intro i hi
    have hi' := n.primeFactors.orderEmbOfFin_mem (k := k) rfl ⟨i, hi⟩
    have hprime := Nat.prime_of_mem_primeFactors hi'
    simpa [p, hi, e] using hprime.two_le
  have hmono : ∀ i, i + 1 < k → p i ≤ p (i + 1) := by
    intro i hi
    have hi0 : i < k := by omega
    have hh := e.monotone (show (⟨i, hi0⟩ : Fin k) ≤ ⟨i + 1, hi⟩ from by
      exact Nat.le_succ i)
    simp [p, hi, hi0, hh]
  have heq' : LehmerTotient.Product.X p k = M * LehmerTotient.Product.Y p k + 1 := by
    simpa [hX, hY] using heq
  have hbound := (LehmerTotient.Product.size_bounds hk hM2 hp hmono heq'
    (j := 0) (by omega)).1
  rw [hX] at hbound
  have hreal : (n : ℝ) < (2 : ℝ) ^ (2 ^ k) := by
    norm_num [LehmerTotient.Product.X] at hbound
    exact hbound
  change n < 2 ^ (2 ^ k)
  exact_mod_cast hreal

/-- A mathematical finite enumeration, NOT the released faster Python search.
It is deliberately unoptimised and impractical for large k. -/
def fixedCount (k : ℕ) : Finset ℕ :=
  (range (bound k)).filter fun n => Counterexample n ∧ n.primeFactors.card = k

theorem mem_fixedCount_iff (n k : ℕ) :
    n ∈ fixedCount k ↔ Counterexample n ∧ n.primeFactors.card = k := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · rintro ⟨hn, hk⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hn, hk⟩
    simpa [hk] using counterexample_lt_bound hn

/-- This is an EQUIVALENCE, not a proof of either universal assertion.
No theorem below asserts that all these sets are empty. -/
theorem conjecture_iff_all_fixedCount_empty :
    (∀ n, ¬ Counterexample n) ↔ ∀ k, fixedCount k = ∅ := by
  constructor
  · intro h k
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact h n ((mem_fixedCount_iff n k).mp hn).1
  · intro h n hn
    have hm := (mem_fixedCount_iff n n.primeFactors.card).mpr ⟨hn, rfl⟩
    rw [h] at hm
    exact Finset.notMem_empty n hm

/-- The conventional conjecture is exactly the missing universal emptiness
statement.  The proof here establishes only this equivalence. -/
theorem standard_conjecture_iff_all_fixedCount_empty :
    (∀ n : ℕ, 1 < n → φ n ∣ n - 1 → n.Prime) ↔ ∀ k, fixedCount k = ∅ := by
  rw [← conjecture_iff_all_fixedCount_empty]
  constructor
  · intro h n hn
    exact hn.2.1 (h n hn.1 hn.2.2)
  · intro h n hn hd
    by_contra hc
    exact h n ⟨hn, hc, hd⟩

/-- Small kernel-evaluated controls, not a substitute for the universal endpoint. -/
theorem first_three_counts_empty :
    fixedCount 0 = ∅ ∧ fixedCount 1 = ∅ ∧ fixedCount 2 = ∅ := by decide +kernel

/-- The actual forced-last-entry equation; no primality is inferred. -/
theorem last_entry_equation (A C q : ℤ) :
    A * q - 1 = C * (q - 1) ↔ (C - A) * q = C - 1 := by
  constructor <;> intro h <;> nlinarith only [h]

theorem last_entry_unique (A C q r : ℤ) (hD : C - A ≠ 0)
    (hq : A * q - 1 = C * (q - 1)) (hr : A * r - 1 = C * (r - 1)) :
    q = r := by
  apply mul_left_cancel₀ hD
  exact ((last_entry_equation A C q).mp hq).trans
    ((last_entry_equation A C r).mp hr).symm

/-- A useful but limited universal prune: deficit one forces the last
entry to equal the prefix product.  It does not cover larger deficits. -/
theorem unit_deficit_forces_prefix_product (A C q : ℤ) (hD : C - A = 1)
    (hq : A * q - 1 = C * (q - 1)) : q = A := by
  have h := (last_entry_equation A C q).mp hq
  rw [hD, one_mul] at h
  omega

theorem unit_deficit_excludes_prime_tail {A C q : ℕ} (hC : C = A + 1)
    (hA : ¬ A.Prime) (hq1 : 1 ≤ q) (heq : A * q = C * (q - 1) + 1) :
    ¬ q.Prime := by
  have heqZ : (A : ℤ) * q - 1 = (C : ℤ) * ((q : ℤ) - 1) := by
    have hcast : (A : ℤ) * q = (C : ℤ) * ((q - 1 : ℕ) : ℤ) + 1 := by
      exact_mod_cast heq
    rw [Nat.cast_sub hq1] at hcast
    push_cast at hcast
    nlinarith only [hcast]
  have hCZ : (C : ℤ) = (A : ℤ) + 1 := by exact_mod_cast hC
  have hqA := unit_deficit_forces_prefix_product (A : ℤ) C q (by omega) heqZ
  have hqA' : q = A := by exact_mod_cast hqA
  simpa [hqA'] using hA

/-- Exact two-entry divisor identity.  A different divisor pair need not
recover ordered primes, so this identity alone is not a descent. -/
theorem two_entry_identity (A C p q : ℤ) :
    ((C - A) * p - C) * ((C - A) * q - C) - (A * C - (C - A)) =
      (C - A) * (C * (p - 1) * (q - 1) - A * p * q + 1) := by ring

#print axioms counterexample_lt_bound
#print axioms mem_fixedCount_iff
#print axioms conjecture_iff_all_fixedCount_empty
#print axioms standard_conjecture_iff_all_fixedCount_empty
#print axioms first_three_counts_empty
#print axioms last_entry_equation
#print axioms last_entry_unique
#print axioms unit_deficit_forces_prefix_product
#print axioms unit_deficit_excludes_prime_tail
#print axioms two_entry_identity
#print Counterexample
#print bound
#print fixedCount

end LehmerFollowup
