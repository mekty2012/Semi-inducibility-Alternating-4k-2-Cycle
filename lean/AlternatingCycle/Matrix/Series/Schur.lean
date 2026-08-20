import AlternatingCycle.Matrix.Series.Resolvent
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The rank-`κ` Schur reduction of a resolvent trace

`lem:det-factor` of `alternating_cycles_schur_proof.tex` removes the rank-one projection `P` from
`I − zL` by the matrix determinant lemma.  We do the same on the *resolvent* instead, which keeps
everything on the trace side and avoids any `n × n` determinant.

Abstract setting: `Rinv = Dm + U * V` with `U : ι × κ`, `V : κ × ι`, and explicit two-sided
inverses `Nm` of `Dm` and `Rm` of `Rinv`.  Writing

```
  M₂ := 1 + V · Nm · U        (a κ × κ matrix)
```

three elementary identities follow:

* `resolvent_shift` — `Rm − Nm = −Nm·U·(V·Rm)`, the resolvent identity;
* `schur_eq` — `M₂ · (V·Rm) = V·Nm`, obtained by multiplying the previous line by `V`;
* `det_mul_trace_sub` — `det M₂ · (Tr Rm − Tr Nm) = −Tr(adj M₂ · (V·Nm) · (Nm·U))`.

The last line is division-free, so no invertibility of `M₂` is needed here; in the application
`det M₂ = 1 − zF(z)` is a unit and dividing by it produces `Λ(det M₂)`.

Only `κ = Fin 2` is used below, but nothing here depends on the size.
-/

namespace AlternatingCycle

open PowerSeries Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {Dm Nm Rinv Rm : Matrix ι ι ℝ⟦X⟧} {U : Matrix ι κ ℝ⟦X⟧} {V : Matrix κ ι ℝ⟦X⟧}

omit [DecidableEq κ] in
/-- The resolvent identity for a rank-`κ` perturbation. -/
lemma resolvent_shift (hND : Nm * Dm = 1) (hRR : Rinv * Rm = 1) (hdec : Rinv = Dm + U * V) :
    Nm * U * (V * Rm) = Nm - Rm := by
  have h2 : Rinv - Dm = U * V := by rw [hdec]; abel
  have h1 : Nm * (Rinv - Dm) * Rm = Nm - Rm := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hRR, Matrix.mul_one, hND,
      Matrix.one_mul]
  rw [h2] at h1
  rw [← h1]
  simp only [Matrix.mul_assoc]

/-- **The Schur equation.**  `M₂ · (V·Rm) = V·Nm` with `M₂ = 1 + V·Nm·U`. -/
lemma schur_eq (hND : Nm * Dm = 1) (hRR : Rinv * Rm = 1) (hdec : Rinv = Dm + U * V) :
    (1 + V * Nm * U) * (V * Rm) = V * Nm := by
  have hres := resolvent_shift hND hRR hdec
  have h1 : Rm + Nm * U * (V * Rm) = Nm := by rw [hres]; abel
  calc (1 + V * Nm * U) * (V * Rm)
      = V * Rm + V * (Nm * U * (V * Rm)) := by
        rw [Matrix.add_mul, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
    _ = V * (Rm + Nm * U * (V * Rm)) := by rw [Matrix.mul_add]
    _ = V * Nm := by rw [h1]

omit [DecidableEq κ] in
/-- The trace of the perturbation, moved onto the small index set `κ`. -/
lemma trace_sub_eq (hND : Nm * Dm = 1) (hRR : Rinv * Rm = 1) (hdec : Rinv = Dm + U * V) :
    Matrix.trace Rm - Matrix.trace Nm = -Matrix.trace ((V * Rm) * (Nm * U)) := by
  have hres := resolvent_shift hND hRR hdec
  have h : Matrix.trace (Nm * U * (V * Rm)) = Matrix.trace Nm - Matrix.trace Rm := by
    rw [hres, Matrix.trace_sub]
  rw [Matrix.trace_mul_comm] at h
  rw [h]
  abel

/-- **The division-free Schur trace identity.** -/
theorem det_mul_trace_sub (hND : Nm * Dm = 1) (hRR : Rinv * Rm = 1)
    (hdec : Rinv = Dm + U * V) :
    Matrix.det (1 + V * Nm * U) * (Matrix.trace Rm - Matrix.trace Nm)
      = -Matrix.trace (Matrix.adjugate (1 + V * Nm * U) * (V * Nm) * (Nm * U)) := by
  set M₂ : Matrix κ κ ℝ⟦X⟧ := 1 + V * Nm * U with hM₂
  have hkey : Matrix.det M₂ • (V * Rm) = Matrix.adjugate M₂ * (V * Nm) := by
    have h := congrArg (fun A => Matrix.adjugate M₂ * A) (schur_eq (V := V) hND hRR hdec)
    simp only [hM₂] at h
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h
    exact h
  have hstep : Matrix.det M₂ * Matrix.trace ((V * Rm) * (Nm * U))
      = Matrix.trace (Matrix.adjugate M₂ * (V * Nm) * (Nm * U)) := by
    calc Matrix.det M₂ * Matrix.trace ((V * Rm) * (Nm * U))
        = Matrix.trace (Matrix.det M₂ • ((V * Rm) * (Nm * U))) := by
          rw [Matrix.trace_smul, smul_eq_mul]
      _ = Matrix.trace ((Matrix.det M₂ • (V * Rm)) * (Nm * U)) := by rw [Matrix.smul_mul]
      _ = Matrix.trace (Matrix.adjugate M₂ * (V * Nm) * (Nm * U)) := by rw [hkey]
  rw [trace_sub_eq hND hRR hdec, mul_neg, hstep]

end AlternatingCycle
