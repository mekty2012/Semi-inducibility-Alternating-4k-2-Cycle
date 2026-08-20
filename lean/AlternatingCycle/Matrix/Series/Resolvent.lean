import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import AlternatingCycle.Matrix.Scalar.LogDeriv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# The formal resolvent of a real matrix

The note derives its trace identities from `−log det(I − zM) = ∑_{r≥1} Tr(M^r) z^r/r`, which for a
general (non-self-adjoint) matrix would require complexification and triangularization.  We never
need it: the *resolvent* carries the same information and is elementary.

For a real matrix `M` put

```
  resolvent M := ∑_{r≥0} z^r M^r ∈ Matrix ι ι ℝ⟦X⟧,
```

defined entrywise by `PowerSeries.mk`.  Then

* `one_sub_smul_mul_resolvent` / `resolvent_mul_one_sub_smul`: it really is a two-sided inverse of
  `1 − z·M`;
* `trace_resolvent`: its trace is the generating function `∑_r Tr(M^r) z^r`.

Nothing here is specific to the alternating-cycle problem.
-/

namespace AlternatingCycle

open PowerSeries Matrix Finset

noncomputable section

/-- Entrywise embedding `Matrix m n ℝ → Matrix m n ℝ⟦X⟧`. -/
def toPS {m n : Type*} (M : Matrix m n ℝ) : Matrix m n ℝ⟦X⟧ := M.map (C : ℝ →+* ℝ⟦X⟧)

@[simp] lemma toPS_apply {m n : Type*} (M : Matrix m n ℝ) (i : m) (j : n) :
    toPS M i j = C (M i j) := rfl

lemma toPS_mul {m n p : Type*} [Fintype n] (M : Matrix m n ℝ) (N : Matrix n p ℝ) :
    toPS (M * N) = toPS M * toPS N := by
  refine Matrix.ext fun i j => ?_
  rw [toPS_apply, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, toPS_apply, toPS_apply]

lemma toPS_add {m n : Type*} (M N : Matrix m n ℝ) : toPS (M + N) = toPS M + toPS N :=
  Matrix.ext fun i j => by simp [toPS]

lemma toPS_neg {m n : Type*} (M : Matrix m n ℝ) : toPS (-M) = -toPS M :=
  Matrix.ext fun i j => by simp [toPS]

/-- Entrywise formal derivative of a matrix of power series. -/
def matDeriv {m n : Type*} (M : Matrix m n ℝ⟦X⟧) : Matrix m n ℝ⟦X⟧ := M.map (d⁄dX ℝ)

@[simp] lemma matDeriv_apply {m n : Type*} (M : Matrix m n ℝ⟦X⟧) (i : m) (j : n) :
    matDeriv M i j = d⁄dX ℝ (M i j) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The formal resolvent `∑_{r≥0} z^r M^r`, defined coefficientwise. -/
def resolvent (M : Matrix ι ι ℝ) : Matrix ι ι ℝ⟦X⟧ :=
  Matrix.of fun i j => PowerSeries.mk fun r => (M ^ r) i j

@[simp] lemma coeff_resolvent (M : Matrix ι ι ℝ) (i j : ι) (r : ℕ) :
    coeff r (resolvent M i j) = (M ^ r) i j := by
  simp [resolvent]

lemma toPS_mul_resolvent (M : Matrix ι ι ℝ) (i j : ι) :
    (toPS M * resolvent M) i j = PowerSeries.mk fun r => (M ^ (r + 1)) i j := by
  ext r
  rw [Matrix.mul_apply, map_sum, coeff_mk, pow_succ', Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [toPS_apply, coeff_C_mul, coeff_resolvent]

lemma resolvent_mul_toPS (M : Matrix ι ι ℝ) (i j : ι) :
    (resolvent M * toPS M) i j = PowerSeries.mk fun r => (M ^ (r + 1)) i j := by
  ext r
  rw [Matrix.mul_apply, map_sum, coeff_mk, pow_succ, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [toPS_apply, coeff_mul_C, coeff_resolvent]

/-- The two-sided inverse property, left version. -/
lemma one_sub_smul_mul_resolvent (M : Matrix ι ι ℝ) :
    (1 - (X : ℝ⟦X⟧) • toPS M) * resolvent M = 1 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  ext i j r
  rw [Matrix.sub_apply, Matrix.smul_apply, toPS_mul_resolvent, smul_eq_mul]
  cases r with
  | zero =>
      rw [map_sub, coeff_resolvent, pow_zero]
      simp [Matrix.one_apply]
  | succ q =>
      rw [map_sub, coeff_resolvent, coeff_succ_X_mul, coeff_mk, sub_self, Matrix.one_apply]
      split_ifs <;> simp

/-- The two-sided inverse property, right version. -/
lemma resolvent_mul_one_sub_smul (M : Matrix ι ι ℝ) :
    resolvent M * (1 - (X : ℝ⟦X⟧) • toPS M) = 1 := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  ext i j r
  rw [Matrix.sub_apply, Matrix.smul_apply, resolvent_mul_toPS, smul_eq_mul]
  cases r with
  | zero =>
      rw [map_sub, coeff_resolvent, pow_zero]
      simp [Matrix.one_apply]
  | succ q =>
      rw [map_sub, coeff_resolvent, coeff_succ_X_mul, coeff_mk, sub_self, Matrix.one_apply]
      split_ifs <;> simp

/-- **`N + z·N' = N²`.**  The one differential identity the Schur reduction needs; here it is a
statement about coefficients, `(r+1)·M^r` on both sides. -/
lemma resolvent_sq (M : Matrix ι ι ℝ) :
    resolvent M * resolvent M = resolvent M + (X : ℝ⟦X⟧) • matDeriv (resolvent M) := by
  ext i j r
  rw [Matrix.add_apply, Matrix.smul_apply, matDeriv_apply, smul_eq_mul, map_add,
    coeff_resolvent, coeff_X_mul_derivative, Matrix.mul_apply, map_sum]
  have hstep : ∀ k : ι, coeff r (resolvent M i k * resolvent M k j)
      = ∑ p ∈ Finset.antidiagonal r, (M ^ p.1) i k * (M ^ p.2) k j := by
    intro k
    rw [coeff_mul]
    exact Finset.sum_congr rfl fun p _ => by rw [coeff_resolvent, coeff_resolvent]
  rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_comm]
  have : ∀ p ∈ Finset.antidiagonal r, ∑ k, (M ^ p.1) i k * (M ^ p.2) k j = (M ^ r) i j := by
    intro p hp
    rw [← Matrix.mul_apply, ← pow_add, Finset.mem_antidiagonal.mp hp]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_antidiagonal, nsmul_eq_mul,
    coeff_resolvent]
  push_cast
  ring

/-- The trace generating function `∑_{r≥0} Tr(M^r) z^r`. -/
def traceSeries (M : Matrix ι ι ℝ) : ℝ⟦X⟧ := PowerSeries.mk fun r => Matrix.trace (M ^ r)

@[simp] lemma coeff_traceSeries (M : Matrix ι ι ℝ) (r : ℕ) :
    coeff r (traceSeries M) = Matrix.trace (M ^ r) := by
  simp [traceSeries]

/-- **The trace of the resolvent is the trace generating function.**  This replaces
`−log det(I − zM) = ∑ Tr(M^r)z^r/r` throughout. -/
lemma trace_resolvent (M : Matrix ι ι ℝ) :
    Matrix.trace (resolvent M) = traceSeries M := by
  ext r
  rw [Matrix.trace, map_sum, coeff_traceSeries, Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => by simp [Matrix.diag_apply]

end

end AlternatingCycle
