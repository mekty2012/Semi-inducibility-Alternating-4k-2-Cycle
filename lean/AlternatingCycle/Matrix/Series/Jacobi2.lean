import AlternatingCycle.Matrix.Series.Schur
import AlternatingCycle.Matrix.Scalar.LogDeriv

/-!
# Jacobi's formula in size two, and the resulting `Λ` identity

`eq:logdet-trace` of `alternating_cycles_schur_proof.tex` is Jacobi's formula for an `n × n`
matrix.  After the Schur reduction of `Series/Schur.lean` the only determinant left is the `2 × 2`
determinant of `M₂`, and there Jacobi's formula is a two-line computation closed by `ring`:

```
  Tr(adj M · M') = M₁₁ M₀₀' − M₀₁ M₁₀' − M₁₀ M₀₁' + M₀₀ M₁₁' = (M₀₀M₁₁ − M₀₁M₁₀)' = (det M)'.
```

Combining with `det_mul_trace_sub` and the observation `V·N²·U = z · (d⁄dX M₂)` (supplied by the
caller) gives the identity that replaces `eq:logdet-factor` entirely:

```
  Tr Rm − Tr Nm = Λ (det M₂).
```
-/

namespace AlternatingCycle

open PowerSeries Matrix

noncomputable section

/-- **Jacobi's formula, size two.** -/
lemma trace_adjugate_mul_matDeriv (M : Matrix (Fin 2) (Fin 2) ℝ⟦X⟧) :
    Matrix.trace (Matrix.adjugate M * matDeriv M) = d⁄dX ℝ (Matrix.det M) := by
  have a00 : Matrix.adjugate M 0 0 = M 1 1 := by rw [Matrix.adjugate_fin_two]; simp
  have a01 : Matrix.adjugate M 0 1 = -M 0 1 := by rw [Matrix.adjugate_fin_two]; simp
  have a10 : Matrix.adjugate M 1 0 = -M 1 0 := by rw [Matrix.adjugate_fin_two]; simp
  have a11 : Matrix.adjugate M 1 1 = M 0 0 := by rw [Matrix.adjugate_fin_two]; simp
  rw [Matrix.det_fin_two, map_sub, Derivation.leibniz, Derivation.leibniz,
    Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply]
  simp only [smul_eq_mul, Fin.sum_univ_two, matDeriv_apply, a00, a01, a10, a11]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Dm Nm Rinv Rm : Matrix ι ι ℝ⟦X⟧}
variable {U : Matrix ι (Fin 2) ℝ⟦X⟧} {V : Matrix (Fin 2) ι ℝ⟦X⟧}

/-- **The replacement for `eq:logdet-factor`.**  Under the Schur decomposition
`Rinv = Dm + U·V`, the derivative hypothesis `V·Nm²·U = z · (d⁄dX M₂)`, and `det M₂` a unit,
the difference of trace generating functions is exactly `Λ (det M₂)`. -/
theorem trace_sub_eq_logDeriv (hND : Nm * Dm = 1) (hRR : Rinv * Rm = 1)
    (hdec : Rinv = Dm + U * V)
    (hderiv : (V * Nm) * (Nm * U) = (X : ℝ⟦X⟧) • matDeriv (1 + V * Nm * U))
    (hcc : constantCoeff (Matrix.det (1 + V * Nm * U)) = 1) :
    Matrix.trace Rm - Matrix.trace Nm = logDeriv (Matrix.det (1 + V * Nm * U)) := by
  set M₂ : Matrix (Fin 2) (Fin 2) ℝ⟦X⟧ := 1 + V * Nm * U with hM₂
  have hmain := det_mul_trace_sub (V := V) hND hRR hdec
  have hrw : Matrix.trace (Matrix.adjugate M₂ * (V * Nm) * (Nm * U))
      = X * d⁄dX ℝ (Matrix.det M₂) := by
    rw [Matrix.mul_assoc, hderiv, Matrix.mul_smul, Matrix.trace_smul,
      trace_adjugate_mul_matDeriv, smul_eq_mul]
  rw [hrw] at hmain
  have hunit : Matrix.det M₂ * (Matrix.det M₂)⁻¹ = 1 := mul_inv_of_constantCoeff_one hcc
  calc Matrix.trace Rm - Matrix.trace Nm
      = Matrix.det M₂ * (Matrix.det M₂)⁻¹ * (Matrix.trace Rm - Matrix.trace Nm) := by
        rw [hunit, one_mul]
    _ = Matrix.det M₂ * (Matrix.trace Rm - Matrix.trace Nm) * (Matrix.det M₂)⁻¹ := by ring
    _ = -(X * d⁄dX ℝ (Matrix.det M₂)) * (Matrix.det M₂)⁻¹ := by rw [hmain]
    _ = logDeriv (Matrix.det M₂) := by rw [logDeriv]; ring

end

end AlternatingCycle
