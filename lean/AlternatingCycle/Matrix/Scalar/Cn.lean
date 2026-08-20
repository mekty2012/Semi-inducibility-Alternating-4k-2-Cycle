import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# The polynomials `c_n`

`eq:def-cn-quotient`–`lem:cn` of `alternating_cycles_schur_proof.tex`.  For `n ≥ 0`,

```
  c_n(x,y) = ∑_{r=0}^{2n} (-1)^r x^{2n-r} y^r = (x^{2n+1} + y^{2n+1}) / (x + y),
```

the second expression read by continuity at `x + y = 0`.  These are the coefficients of the
partial-fraction expansion `eq:cn-generating`, and the two facts the proof needs about them are

* `cn_nonneg` (`eq:cn-positive`): `c_n ≥ 0`, because `c_n` is a difference quotient of the
  increasing function `t ↦ t^{2n+1}`;
* `cn_recurrence` (`eq:cn-recurrence`): `(x²+y²) c_n − c_{n+1} = x²y² c_{n-1}` for `n ≥ 1`,
  whence `cn_le_mul`: `c_{n+1} ≤ (x²+y²) c_n`.

Everything is derived from the single "peeling" identity `cn_succ`, which strips the top two terms
of the alternating sum; after that no `Finset` manipulation occurs and every step is `ring` or
`linear_combination`.
-/

namespace AlternatingCycle

open Finset

/-- `c_n(x,y) = ∑_{r=0}^{2n} (-1)^r x^{2n-r} y^r`; this is `eq:def-cn-polynomial`. -/
def cn (n : ℕ) (x y : ℝ) : ℝ := ∑ i ∈ range (2 * n + 1), (-1) ^ i * x ^ (2 * n - i) * y ^ i

@[simp] lemma cn_zero (x y : ℝ) : cn 0 x y = 1 := by simp [cn]

/-- **Peeling.**  Splitting off the top two terms of the alternating sum expresses `c_{n+1}` through
`c_n`.  Every later lemma in this file is a `ring` consequence of this one. -/
lemma cn_succ (n : ℕ) (x y : ℝ) :
    cn (n + 1) x y = x ^ 2 * cn n x y + y ^ (2 * n + 2) - x * y ^ (2 * n + 1) := by
  have hr : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
  rw [cn, hr, Finset.sum_range_succ, Finset.sum_range_succ]
  have hmain : ∑ i ∈ range (2 * n + 1), (-1 : ℝ) ^ i * x ^ (2 * (n + 1) - i) * y ^ i
      = x ^ 2 * cn n x y := by
    rw [cn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ 2 * n := by
      have := Finset.mem_range.mp hi; omega
    have hx : 2 * (n + 1) - i = 2 + (2 * n - i) := by omega
    rw [hx, pow_add]
    ring
  rw [hmain]
  have h1 : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [pow_succ, pow_mul]; norm_num
  have h2 : (-1 : ℝ) ^ (2 * n + 1 + 1) = 1 := by
    rw [pow_succ, h1]; norm_num
  have h3 : 2 * (n + 1) - (2 * n + 1) = 1 := by omega
  have h4 : 2 * (n + 1) - (2 * n + 1 + 1) = 0 := by omega
  rw [h1, h2, h3, h4]
  ring

lemma cn_one (x y : ℝ) : cn 1 x y = x ^ 2 - x * y + y ^ 2 := by
  have := cn_succ 0 x y
  simp only [cn_zero] at this
  rw [this]; ring

/-- `eq:def-cn-quotient`: `(x+y) c_n(x,y) = x^{2n+1} + y^{2n+1}`. -/
lemma add_mul_cn (n : ℕ) (x y : ℝ) :
    (x + y) * cn n x y = x ^ (2 * n + 1) + y ^ (2 * n + 1) := by
  induction n with
  | zero => simp [cn]
  | succ n ih =>
      rw [cn_succ]
      linear_combination x ^ 2 * ih

/-- The two sides of `add_mul_cn` have the same sign, because `t ↦ t^{2n+1}` is increasing. -/
lemma add_mul_odd_pow_nonneg (n : ℕ) (x y : ℝ) :
    0 ≤ (x + y) * (x ^ (2 * n + 1) + y ^ (2 * n + 1)) := by
  have hodd : Odd (2 * n + 1) := ⟨n, by ring⟩
  have hmono : StrictMono fun a : ℝ => a ^ (2 * n + 1) := hodd.strictMono_pow
  have hneg : (-y) ^ (2 * n + 1) = -y ^ (2 * n + 1) := hodd.neg_pow y
  rcases le_total (-y) x with h | h
  · have := hmono.le_iff_le.mpr h
    simp only [hneg] at this
    have h1 : (0 : ℝ) ≤ x + y := by linarith
    have h2 : (0 : ℝ) ≤ x ^ (2 * n + 1) + y ^ (2 * n + 1) := by linarith
    exact mul_nonneg h1 h2
  · have := hmono.le_iff_le.mpr h
    simp only [hneg] at this
    have h1 : x + y ≤ 0 := by linarith
    have h2 : x ^ (2 * n + 1) + y ^ (2 * n + 1) ≤ 0 := by linarith
    nlinarith [mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr h2)]

/-- The value on the antidiagonal `y = -x`, where the quotient `eq:def-cn-quotient` is read by
continuity: `c_n(x,-x) = (2n+1) x^{2n}`. -/
lemma cn_neg (n : ℕ) (x : ℝ) : cn n x (-x) = (2 * n + 1) * x ^ (2 * n) := by
  induction n with
  | zero => simp [cn]
  | succ n ih =>
      have hev : (-x) ^ (2 * n + 2) = x ^ (2 * n + 2) := by
        rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, pow_mul, neg_sq]
      have hodd : Odd (2 * n + 1) := ⟨n, by ring⟩
      have hod : (-x) ^ (2 * n + 1) = -x ^ (2 * n + 1) := hodd.neg_pow x
      rw [cn_succ, ih, hev, hod]
      push_cast
      ring

/-- **`eq:cn-positive`.**  `c_n` is nonnegative on all of `ℝ²`. -/
lemma cn_nonneg (n : ℕ) (x y : ℝ) : 0 ≤ cn n x y := by
  rcases eq_or_ne (x + y) 0 with h | h
  · have hy : y = -x := by linarith
    subst hy
    rw [cn_neg]
    have : (0 : ℝ) ≤ x ^ (2 * n) := by rw [pow_mul]; positivity
    have hn : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := by positivity
    exact mul_nonneg hn this
  · have hsq : 0 < (x + y) ^ 2 := by positivity
    have hprod : 0 ≤ (x + y) ^ 2 * cn n x y := by
      have h1 := add_mul_odd_pow_nonneg n x y
      have h2 := add_mul_cn n x y
      calc (0 : ℝ) ≤ (x + y) * (x ^ (2 * n + 1) + y ^ (2 * n + 1)) := h1
        _ = (x + y) ^ 2 * cn n x y := by rw [← h2]; ring
    exact le_of_mul_le_mul_left (by simpa using hprod) hsq

/-- **`eq:cn-recurrence`.**  Stated at `n+1` so that the right-hand side never mentions `c_{-1}`. -/
lemma cn_recurrence (n : ℕ) (x y : ℝ) :
    (x ^ 2 + y ^ 2) * cn (n + 1) x y - cn (n + 2) x y = x ^ 2 * y ^ 2 * cn n x y := by
  rw [cn_succ (n + 1), cn_succ n]
  ring

/-- The contraction step of `lem:beta-monotone` for an off-diagonal pair. -/
lemma cn_le_mul (n : ℕ) (x y : ℝ) :
    cn (n + 2) x y ≤ (x ^ 2 + y ^ 2) * cn (n + 1) x y := by
  have h := cn_recurrence n x y
  nlinarith [cn_nonneg n x y, sq_nonneg (x * y)]

/-! ### The convolution form

The coefficients `β_n` arise from a Cauchy product, so `c_n` is needed in the shape
`∑_{p+q=n} x^{2p}y^{2q} − xy ∑_{p+q=n-1} x^{2p}y^{2q}` (`eq:partial-fraction` expanded).  Both sides
satisfy the peeling recursion `cn_succ`, so a single induction identifies them. -/

/-- `S_n(x,y) = ∑_{p+q=n} x^{2p} y^{2q}`. -/
def Sconv (n : ℕ) (x y : ℝ) : ℝ := ∑ p ∈ Finset.antidiagonal n, x ^ (2 * p.1) * y ^ (2 * p.2)

@[simp] lemma Sconv_zero (x y : ℝ) : Sconv 0 x y = 1 := by simp [Sconv]

lemma Sconv_succ (n : ℕ) (x y : ℝ) :
    Sconv (n + 1) x y = y ^ (2 * n + 2) + x ^ 2 * Sconv n x y := by
  rw [Sconv, Finset.Nat.sum_antidiagonal_succ, Sconv, Finset.mul_sum]
  congr 1
  · norm_num
    ring_nf
  · exact Finset.sum_congr rfl fun p _ => by ring

lemma cn_succ_eq_Sconv (n : ℕ) (x y : ℝ) :
    cn (n + 1) x y = Sconv (n + 1) x y - x * y * Sconv n x y := by
  induction n with
  | zero => rw [cn_succ, cn_zero, Sconv_succ, Sconv_zero]; ring
  | succ n ih =>
      rw [cn_succ, ih, Sconv_succ (n + 1), Sconv_succ n]
      ring

/-- On the diagonal the divided difference degenerates to a single power. -/
lemma cn_diag (n : ℕ) (x : ℝ) : cn n x x = x ^ (2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [cn_succ, ih]
      ring

end AlternatingCycle
