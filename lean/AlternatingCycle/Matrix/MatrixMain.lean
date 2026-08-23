import AlternatingCycle.Matrix.Beta

/-!
# The abstract alternating trace inequality

For a symmetric `X` with `Tr(X²) ≤ 1`, a unit vector `e`, `P = e ⊗ e`,
`L = (P+X)(P−X)`, and **odd** `m`,

```
  Tr(L^m) + Tr(X^{2m}) ≤ 1.
```

The proof combines three identities:

* `Model.traceSeries_sub` — `∑_r Tr(L^r) z^r − ∑_r Tr((−X²)^r) z^r = Λ(det M₂)`;
* `det_M2` — `det M₂ = 1 − z F(z)` with `F = ∑ (−1)^n β_n z^n`;
* `coeff_logDeriv_betaSeries_le_one` — `[z^m] Λ(1 − zF) ≤ 1` for odd `m`, because
  `1 = β₀ ≥ β₁ ≥ …` (`beta_zero`, `beta_antitone`).

Reading the coefficient of `z^m` and using `Tr((−X²)^m) = −Tr(X^{2m})` for odd `m` gives the
stated trace inequality.
-/

namespace AlternatingCycle

open PowerSeries Matrix

noncomputable section

variable {n : ℕ} (T : Spectrum n)

/-- Coefficient extraction from the trace identity at an odd index. -/
lemma trace_coefficient {m : ℕ} (hm : Odd m) :
    Matrix.trace (T.model.L ^ m) + Matrix.trace (T.model.A ^ (2 * m))
      = coeff m (logDeriv (Matrix.det T.model.M2)) := by
  have hY : T.model.Y ^ m = T.model.A ^ (2 * m) := by
    rw [Model.Y, ← pow_two, ← pow_mul]
  have h2 : coeff m (traceSeries (-T.model.Y)) = -Matrix.trace (T.model.A ^ (2 * m)) := by
    rw [coeff_traceSeries, hm.neg_pow, hY, Matrix.trace_neg]
  have hkey := congrArg (coeff m) T.model.traceSeries_sub
  rw [map_sub, coeff_traceSeries, h2] at hkey
  rw [← hkey]
  ring

/-- The abstract alternating trace inequality. -/
theorem matrix_main {m : ℕ} (hm : Odd m) :
    Matrix.trace (T.model.L ^ m) + Matrix.trace (T.model.A ^ (2 * m)) ≤ 1 := by
  rw [trace_coefficient T hm, det_M2 T]
  exact coeff_logDeriv_betaSeries_le_one T.beta_zero T.beta_antitone hm

end

end AlternatingCycle
