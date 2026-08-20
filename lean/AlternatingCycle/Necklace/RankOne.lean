import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Real.Basic

/-!
# The rank-one normal form

Let `𝒜` be a unital `ℝ`-algebra, `k j : 𝒜`, and suppose `j` behaves like a rank-one projector
against the powers of `k`:

```
  j * k ^ b * j = μ b • j.
```

Then the signed word `Q n = ∏_{i<n} (j + ε i • k)` collapses into the two-index normal form

```
  Q n = α n • k ^ n + ∑_{a,b} c n a b • (k ^ a * j * k ^ b),
```

where `α` and `c` are given by an explicit recursion (`alphaC`, `coeff`) depending only on the sign
pattern `ε` and the numbers `μ`.  Nothing else about `𝒜` is used — in particular no trace, no
module, no vectors — so the identity is available verbatim for matrices (`Necklace/MatrixInstance`)
and for kernels, which is the whole point: the two instantiations produce the *same* numbers.

The recursion is driven by four rewrite rules,

```
  k ^ n * j            = k ^ n * j * k ^ 0
  k ^ n * (ε • k)      = ε • k ^ (n+1)
  (k ^ a * j * k ^ b) * j       = μ b • (k ^ a * j * k ^ 0)     -- this is `hjk`
  (k ^ a * j * k ^ b) * (ε • k) = ε • (k ^ a * j * k ^ (b+1))
```
-/

namespace AlternatingCycle.RankOne

open Finset

variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℝ 𝒜]

/-- The signed word `Q n = (j + ε 0 • k) * ⋯ * (j + ε (n-1) • k)`, multiplied left to right. -/
def word (ε : ℕ → ℝ) (j k : 𝒜) : ℕ → 𝒜
  | 0 => 1
  | n + 1 => word ε j k n * (j + ε n • k)

@[simp] lemma word_zero (ε : ℕ → ℝ) (j k : 𝒜) : word ε j k 0 = 1 := rfl

lemma word_succ (ε : ℕ → ℝ) (j k : 𝒜) (n : ℕ) :
    word ε j k (n + 1) = word ε j k n * (j + ε n • k) := rfl

/-- The coefficient of the pure power `k ^ n`: the product `∏_{i<n} ε i`. -/
def alphaC (ε : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ε n * alphaC ε n

@[simp] lemma alphaC_zero (ε : ℕ → ℝ) : alphaC ε 0 = 1 := rfl

lemma alphaC_succ (ε : ℕ → ℝ) (n : ℕ) : alphaC ε (n + 1) = ε n * alphaC ε n := rfl

/-- The coefficient of `k ^ a * j * k ^ b` in the normal form of `word ε j k n`. -/
def coeff (ε μ : ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | n + 1, a, 0 =>
      (if a = n then alphaC ε n else 0) + ∑ b ∈ range (n + 1), coeff ε μ n a b * μ b
  | n + 1, a, b + 1 => ε n * coeff ε μ n a b

@[simp] lemma coeff_zero (ε μ : ℕ → ℝ) (a b : ℕ) : coeff ε μ 0 a b = 0 := rfl

lemma coeff_succ_zero (ε μ : ℕ → ℝ) (n a : ℕ) :
    coeff ε μ (n + 1) a 0 =
      (if a = n then alphaC ε n else 0) + ∑ b ∈ range (n + 1), coeff ε μ n a b * μ b := rfl

lemma coeff_succ_succ (ε μ : ℕ → ℝ) (n a b : ℕ) :
    coeff ε μ (n + 1) a (b + 1) = ε n * coeff ε μ n a b := rfl

/-- A normal-form monomial of `word ε j k n` has total degree at most `n`, so its left exponent is
smaller than `n`. -/
lemma coeff_eq_zero_of_le_left (ε μ : ℕ → ℝ) :
    ∀ (n a b : ℕ), n ≤ a → coeff ε μ n a b = 0
  | 0, _, _, _ => rfl
  | n + 1, a, 0, h => by
      rw [coeff_succ_zero, if_neg (by omega)]
      have : ∀ b ∈ range (n + 1), coeff ε μ n a b * μ b = 0 := fun b _ => by
        rw [coeff_eq_zero_of_le_left ε μ n a b (by omega), zero_mul]
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero, add_zero]
  | n + 1, a, b + 1, h => by
      rw [coeff_succ_succ, coeff_eq_zero_of_le_left ε μ n a b (by omega), mul_zero]

/-- Likewise for the right exponent. -/
lemma coeff_eq_zero_of_le_right (ε μ : ℕ → ℝ) :
    ∀ (n a b : ℕ), n ≤ b → coeff ε μ n a b = 0
  | 0, _, _, _ => rfl
  | n + 1, _, 0, h => absurd h (by omega)
  | n + 1, a, b + 1, h => by
      rw [coeff_succ_succ, coeff_eq_zero_of_le_right ε μ n a b (by omega), mul_zero]

/-- **Total degree.**  A monomial of `word ε j k n` carries one `j` and at most `n−1` factors `k`,
so only `μ_g` with `g < n` can occur. -/
lemma coeff_eq_zero_of_le_add (ε μ : ℕ → ℝ) :
    ∀ (n a b : ℕ), n ≤ a + b → coeff ε μ n a b = 0
  | 0, _, _, _ => rfl
  | n + 1, a, 0, h => by
      rw [coeff_succ_zero, if_neg (by omega)]
      have hz : ∀ b ∈ range (n + 1), coeff ε μ n a b * μ b = 0 := fun b _ => by
        rw [coeff_eq_zero_of_le_add ε μ n a b (by omega), zero_mul]
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, add_zero]
  | n + 1, a, b + 1, h => by
      rw [coeff_succ_succ, coeff_eq_zero_of_le_add ε μ n a b (by omega), mul_zero]

/-- The coefficients depend on the moments only through `μ_0, …, μ_{n−1}`. -/
lemma coeff_congr (ε : ℕ → ℝ) {μ ν : ℕ → ℝ} :
    ∀ (n : ℕ), (∀ g, g < n → μ g = ν g) → ∀ (a b : ℕ), coeff ε μ n a b = coeff ε ν n a b
  | 0, _, _, _ => rfl
  | n + 1, h, a, 0 => by
      rw [coeff_succ_zero, coeff_succ_zero]
      congr 1
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [coeff_congr ε n (fun g hg => h g (by omega)) a b,
        h b (by simpa using Finset.mem_range.mp hb)]
  | n + 1, h, a, b + 1 => by
      rw [coeff_succ_succ, coeff_succ_succ, coeff_congr ε n (fun g hg => h g (by omega)) a b]

section NormalForm

variable (ε μ : ℕ → ℝ) (j k : 𝒜)

/-- The third rewrite rule: `j` swallows everything to its right. -/
lemma term_mul_j (hjk : ∀ b : ℕ, j * k ^ b * j = μ b • j) (a b : ℕ) :
    (k ^ a * j * k ^ b) * j = μ b • (k ^ a * j * k ^ 0) := by
  rw [pow_zero, mul_one, mul_assoc, mul_assoc, ← mul_assoc (j) (k ^ b) j, hjk b,
    mul_smul_comm]

omit [Algebra ℝ 𝒜] in
/-- The fourth rewrite rule: `k` piles up on the right. -/
lemma term_mul_k (a b : ℕ) :
    (k ^ a * j * k ^ b) * k = k ^ a * j * k ^ (b + 1) := by
  rw [pow_succ, mul_assoc]

/-- **The normal form.**  Every signed word is a multiple of `k ^ n` plus a two-index combination
of the monomials `k ^ a * j * k ^ b`, with coefficients given by `alphaC` and `coeff`. -/
theorem word_eq (hjk : ∀ b : ℕ, j * k ^ b * j = μ b • j) :
    ∀ n : ℕ,
      word ε j k n =
        alphaC ε n • k ^ n
          + ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
              coeff ε μ n a b • (k ^ a * j * k ^ b)
  | 0 => by simp
  | n + 1 => by
    have ih := word_eq hjk n
    -- the two pieces of the inductive normal form
    set S : 𝒜 := ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
      coeff ε μ n a b • (k ^ a * j * k ^ b) with hS
    -- `S * j`: every monomial loses its right tail
    have hSj : S * j
        = ∑ a ∈ range (n + 1),
            (∑ b ∈ range (n + 1), coeff ε μ n a b * μ b) • (k ^ a * j * k ^ 0) := by
      rw [hS, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul, Finset.sum_smul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_mul_assoc, term_mul_j μ j k hjk a b, smul_smul]
    -- `S * k`: every monomial grows its right tail
    have hSk : S * k
        = ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
            coeff ε μ n a b • (k ^ a * j * k ^ (b + 1)) := by
      rw [hS, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_mul_assoc, term_mul_k j k a b]
    -- expand the target: split the `b`-sum at `b = 0`, then drop the vanishing `a = n + 1` row
    have htarget :
        ∑ a ∈ range (n + 1 + 1), ∑ b ∈ range (n + 1 + 1),
            coeff ε μ (n + 1) a b • (k ^ a * j * k ^ b)
          = (∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
                coeff ε μ n a b • (ε n • (k ^ a * j * k ^ (b + 1))))
            + (alphaC ε n • (k ^ n * j * k ^ 0)
              + ∑ a ∈ range (n + 1),
                  (∑ b ∈ range (n + 1), coeff ε μ n a b * μ b) • (k ^ a * j * k ^ 0)) := by
      have hrow : ∀ a ∈ range (n + 2),
          ∑ b ∈ range (n + 2), coeff ε μ (n + 1) a b • (k ^ a * j * k ^ b)
            = (∑ b ∈ range (n + 1),
                coeff ε μ n a b • (ε n • (k ^ a * j * k ^ (b + 1))))
              + ((if a = n then alphaC ε n else 0) • (k ^ a * j * k ^ 0)
                + (∑ b ∈ range (n + 1), coeff ε μ n a b * μ b) • (k ^ a * j * k ^ 0)) := by
        intro a _
        rw [Finset.sum_range_succ' (fun b => coeff ε μ (n + 1) a b • (k ^ a * j * k ^ b)) (n + 1),
          coeff_succ_zero, add_smul]
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [coeff_succ_succ, mul_comm, mul_smul]
      rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_range_succ (fun a => ∑ b ∈ range (n + 1),
          coeff ε μ n a b • (ε n • (k ^ a * j * k ^ (b + 1)))) (n + 1),
        Finset.sum_range_succ
          (fun a => (if a = n then alphaC ε n else 0) • (k ^ a * j * k ^ 0)) (n + 1),
        Finset.sum_range_succ
          (fun a => (∑ b ∈ range (n + 1), coeff ε μ n a b * μ b) • (k ^ a * j * k ^ 0)) (n + 1)]
      -- the `a = n + 1` row vanishes: no monomial of degree `n` reaches exponent `n + 1`
      have hz : ∀ b, coeff ε μ n (n + 1) b = 0 := fun b =>
        coeff_eq_zero_of_le_left ε μ n (n + 1) b (by omega)
      simp only [hz, zero_smul, zero_mul, Finset.sum_const_zero, add_zero,
        if_neg (by omega : n + 1 ≠ n), zero_smul]
      -- and the surviving `if` picks out `a = n`
      have hpick : ∑ x ∈ range (n + 1), (if x = n then alphaC ε n else 0) • (k ^ x * j * k ^ 0)
          = alphaC ε n • (k ^ n * j * k ^ 0) := by
        rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg hb, zero_smul])
          (fun h => absurd (Finset.self_mem_range_succ n) h), if_pos rfl]
      rw [hpick]
    rw [word_succ, ih, add_mul, mul_add, mul_add, alphaC_succ, htarget]
    have h1 : alphaC ε n • k ^ n * j = alphaC ε n • (k ^ n * j * k ^ 0) := by
      rw [pow_zero, mul_one, smul_mul_assoc]
    have h2 : alphaC ε n • k ^ n * (ε n • k) = (ε n * alphaC ε n) • k ^ (n + 1) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ, mul_comm (alphaC ε n)]
    have h3 : S * (ε n • k)
        = ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
            coeff ε μ n a b • (ε n • (k ^ a * j * k ^ (b + 1))) := by
      rw [mul_smul_comm, hSk, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [smul_comm]
    rw [h1, h2, h3, hSj]
    abel

end NormalForm

end AlternatingCycle.RankOne
