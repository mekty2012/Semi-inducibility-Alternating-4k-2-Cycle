import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# The logarithmic-derivative operator on `ℝ⟦X⟧`

A logarithmic derivative captures the required trace identities without introducing a formal
logarithm.  Every use is of the shape
`m · [z^m](−log A)`, and

```
  m · [z^m](−log A) = [z^m] (−z · A' / A).
```

So we define

```
  Λ A := −(X · d⁄dX A · A⁻¹)
```

on `ℝ⟦X⟧`, a rational operation, and use only

* `logDeriv_mul` — `Λ(AB) = Λ A + Λ B` for `A, B` with constant coefficient `1`;
* `coeff_logDeriv_one_add_X` — `[z^m] Λ(1+X) = −1` for odd `m` (`[z^m] log(1+z) = 1/m`);
* `coeff_logDeriv_one_sub_eq_sum` — the expansion of `Λ(1−H)` in powers of `H`, for `H` with zero
  constant coefficient.

No `PowerSeries.log`, no `Real.log`, no convergence.
-/

namespace AlternatingCycle

open PowerSeries Finset

noncomputable section

/-- `Λ A = −(X · A' · A⁻¹)`.  For `A` with constant coefficient `1` this is `X · d⁄dX (−log A)`,
so `coeff m (Λ A) = m · [z^m](−log A)`. -/
def logDeriv (A : ℝ⟦X⟧) : ℝ⟦X⟧ := -(X * (d⁄dX ℝ A) * A⁻¹)

lemma mul_inv_of_constantCoeff_one {A : ℝ⟦X⟧} (h : constantCoeff A = 1) : A * A⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel A (by rw [h]; exact one_ne_zero)

/-- The logarithmic derivative turns products into sums. -/
lemma logDeriv_mul {A B : ℝ⟦X⟧} (hA : constantCoeff A = 1) (hB : constantCoeff B = 1) :
    logDeriv (A * B) = logDeriv A + logDeriv B := by
  have hA' := mul_inv_of_constantCoeff_one hA
  have hB' := mul_inv_of_constantCoeff_one hB
  have hd : d⁄dX ℝ (A * B) = A * (d⁄dX ℝ B) + B * (d⁄dX ℝ A) := by
    rw [Derivation.leibniz]; simp [smul_eq_mul]
  simp only [logDeriv, hd, PowerSeries.mul_inv_rev]
  linear_combination (-(X * (d⁄dX ℝ B) * B⁻¹)) * hA' + (-(X * (d⁄dX ℝ A) * A⁻¹)) * hB'

/-! ### Coefficient extraction -/

/-- Multiplying by `X` after differentiating multiplies the `m`-th coefficient by `m`. -/
lemma coeff_X_mul_derivative (Φ : ℝ⟦X⟧) (m : ℕ) :
    coeff m (X * (d⁄dX ℝ Φ)) = m * coeff m Φ := by
  cases m with
  | zero => simp
  | succ k =>
      rw [coeff_succ_X_mul, coeff_derivative]
      push_cast
      ring

/-- The inverse of `1 + X` is the alternating geometric series. -/
lemma inv_one_add_X : (1 + X : ℝ⟦X⟧)⁻¹ = PowerSeries.mk fun n => (-1 : ℝ) ^ n := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp)]
  ext n
  cases n with
  | zero => simp
  | succ k =>
      rw [mul_add, map_add, mul_one, coeff_mk, mul_comm (PowerSeries.mk _) X, coeff_succ_X_mul,
        coeff_mk]
      simp [pow_succ]

/-- `[z^m] Λ(1+z) = −1` for odd `m`; this is `[z^m] log(1+z) = 1/m`. -/
lemma coeff_logDeriv_one_add_X {m : ℕ} (hm : Odd m) :
    coeff m (logDeriv (1 + X : ℝ⟦X⟧)) = -1 := by
  obtain ⟨k, hk⟩ := hm
  have hd : d⁄dX ℝ (1 + X : ℝ⟦X⟧) = 1 := by simp
  have hpow : (-1 : ℝ) ^ (2 * k) = 1 := by
    rw [pow_mul]; norm_num
  rw [logDeriv, hd, mul_one, inv_one_add_X, map_neg, hk]
  rw [show 2 * k + 1 = 2 * k + 1 from rfl, coeff_succ_X_mul, coeff_mk, hpow]

/-! ### Powers of a series with vanishing constant coefficient -/

lemma coeff_mul_pow_eq_zero {H : ℝ⟦X⟧} (hH : constantCoeff H = 0) (T : ℝ⟦X⟧) {s j : ℕ}
    (hj : j < s) : coeff j (T * H ^ s) = 0 := by
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr hH
  have : T * H ^ s = X ^ s * (T * g ^ s) := by rw [hg, mul_pow]; ring
  rw [this, coeff_X_pow_mul']
  simp [Nat.not_le.mpr hj]

lemma coeff_pow_eq_zero {H : ℝ⟦X⟧} (hH : constantCoeff H = 0) {s j : ℕ} (hj : j < s) :
    coeff j (H ^ s) = 0 := by
  simpa using coeff_mul_pow_eq_zero hH 1 hj

/-! ### The expansion of `Λ(1 − H)` in powers of `H` -/

/-- One term of the expansion, in division-free form: differentiating `H^{r+1}` produces the
factor `r+1`. -/
lemma coeff_X_mul_deriv_mul_pow (H : ℝ⟦X⟧) (m r : ℕ) :
    ((r : ℝ) + 1) * coeff m (X * (d⁄dX ℝ H) * H ^ r) = m * coeff m (H ^ (r + 1)) := by
  have hd : d⁄dX ℝ (H ^ (r + 1)) = ((r + 1 : ℕ) : ℝ⟦X⟧) * H ^ r * (d⁄dX ℝ H) := by
    simpa using PowerSeries.derivative_pow ℝ H (r + 1)
  have h2 : X * (d⁄dX ℝ (H ^ (r + 1))) = C ((r : ℝ) + 1) * (X * (d⁄dX ℝ H) * H ^ r) := by
    rw [hd]
    have : ((r + 1 : ℕ) : ℝ⟦X⟧) = C ((r : ℝ) + 1) := by
      rw [← map_natCast (C : ℝ →+* ℝ⟦X⟧) (r + 1)]
      push_cast
      rfl
    rw [this]; ring
  have h3 := coeff_X_mul_derivative (H ^ (r + 1)) m
  rw [h2, coeff_C_mul] at h3
  exact h3

/-- The identity `Λ(1 − H) = X · H' · (1−H)⁻¹`, with the resolvent truncated at
level `m` because `H^{m+1}` contributes nothing to the `m`-th coefficient. -/
lemma coeff_logDeriv_one_sub_eq_sum {H : ℝ⟦X⟧} (hH : constantCoeff H = 0) (m : ℕ) :
    coeff m (logDeriv (1 - H)) = ∑ r ∈ range (m + 1), coeff m (X * (d⁄dX ℝ H) * H ^ r) := by
  have hcc : constantCoeff (1 - H : ℝ⟦X⟧) ≠ 0 := by simp [hH]
  set S : ℝ⟦X⟧ := ∑ r ∈ range (m + 1), H ^ r with hS
  have hgeom : S * (1 - H) = 1 - H ^ (m + 1) := geom_sum_mul_neg H (m + 1)
  have hmi : (1 - H : ℝ⟦X⟧)⁻¹ * (1 - H) = 1 := PowerSeries.inv_mul_cancel _ hcc
  have hinv : (1 - H : ℝ⟦X⟧)⁻¹ = S + (1 - H)⁻¹ * H ^ (m + 1) := by
    linear_combination (-(1 - H : ℝ⟦X⟧)⁻¹) * hgeom + S * hmi
  have hL : logDeriv (1 - H) = X * (d⁄dX ℝ H) * S
      + (X * (d⁄dX ℝ H) * (1 - H)⁻¹) * H ^ (m + 1) := by
    have hd : d⁄dX ℝ (1 - H : ℝ⟦X⟧) = -(d⁄dX ℝ H) := by simp
    rw [logDeriv, hd]
    linear_combination (X * (d⁄dX ℝ H)) * hinv
  rw [hL, map_add, coeff_mul_pow_eq_zero hH _ (Nat.lt_succ_self m), add_zero, hS,
    Finset.mul_sum, map_sum]

/-- If every power `H^s` (`s ≥ 1`) has nonpositive
`m`-th coefficient, then so does `Λ(1 − H)`. -/
lemma coeff_logDeriv_one_sub_nonpos {H : ℝ⟦X⟧} (hH : constantCoeff H = 0) (m : ℕ)
    (hpow : ∀ s, 1 ≤ s → coeff m (H ^ s) ≤ 0) :
    coeff m (logDeriv (1 - H)) ≤ 0 := by
  rw [coeff_logDeriv_one_sub_eq_sum hH m]
  refine Finset.sum_nonpos fun r _ => ?_
  have hkey := coeff_X_mul_deriv_mul_pow H m r
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hrhs : (m : ℝ) * coeff m (H ^ (r + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) (hpow (r + 1) (Nat.le_add_left 1 r))
  nlinarith [hkey, hr, hrhs]

end

end AlternatingCycle
