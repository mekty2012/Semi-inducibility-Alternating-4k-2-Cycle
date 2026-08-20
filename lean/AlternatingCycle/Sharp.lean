import AlternatingCycle.Main

/-!
# Sharpness at the constant graphon

For `W ≡ 1/2` on any
probability space the signed kernel `2W − 1` vanishes, so `t(C_{2m}, 2W−1) = 0`, while
`W ∘ (1 − W)` is the constant kernel `1/4` and `Alt_{2m}(W) = 4^{-m}`.  Hence

```
  4^m · Alt_{2m}(W) + t(C_{2m}, 2W − 1) = 1,
```

with equality for every `m ≥ 1`: the coefficient `4^m` in `alt_add_cycle_le_one` cannot be
increased, and the random-like graphon attains `Alt_{2m}(W) = 4^{-m}`.

The balanced complete bipartite graphon gives equality at the other end, and shows the parity
hypothesis cannot be dropped (`Alt_{2m} = 2·4^{-m}` for **even** `m`).  It is not treated here.
-/

open MeasureTheory OddCycleBound

set_option linter.unusedSectionVars false

noncomputable section

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Constant kernels -/

lemma trace_const (a : ℝ) : trace μ (fun _ _ : Ω => a) = a := by
  simp [trace]

lemma comp_const (a b : ℝ) :
    comp μ (fun _ _ : Ω => a) (fun _ _ : Ω => b) = fun _ _ => a * b := by
  funext x y
  simp [comp]

lemma compPow_const (a : ℝ) : ∀ r : ℕ,
    compPow μ (fun _ _ : Ω => a) r = fun _ _ => a ^ (r + 1)
  | 0 => by funext x y; simp [compPow]
  | r + 1 => by
      rw [compPow, compPow_const a r, comp_const]
      funext x y
      ring

/-! ### The constant graphon -/

/-- The random-like graphon `W ≡ 1/2`. -/
def halfGraphon (Ω : Type*) : Ω → Ω → ℝ := fun _ _ => 1 / 2

lemma isGraphon_half : IsGraphon (halfGraphon Ω) μ where
  meas := measurable_const
  nonneg := fun _ _ => by norm_num [halfGraphon]
  le_one := fun _ _ => by norm_num [halfGraphon]
  symm := fun _ _ => rfl

@[simp] lemma sgn_half : sgn (halfGraphon Ω) = fun _ _ => (0 : ℝ) := by
  funext x y; simp [sgn, halfGraphon]

@[simp] lemma cmpl_half : cmpl (halfGraphon Ω) = fun _ _ => (1 / 2 : ℝ) := by
  funext x y; norm_num [cmpl, halfGraphon]

/-- `t(C_r, 2W − 1) = 0`: the signed kernel of the constant graphon vanishes. -/
theorem half_signedCycle (r : ℕ) :
    signedCycleDensity (sgn (halfGraphon Ω)) μ r = 0 := by
  rw [signedCycleDensity, sgn_half, compPow_const, trace_const]
  simp

/-- `Alt_{2m}(W) = 4^{-m}` at the constant graphon. -/
theorem half_alt {m : ℕ} (hm : 0 < m) :
    altDensity (halfGraphon Ω) μ m = (1 / 4 : ℝ) ^ m := by
  rw [altDensity]
  have hcomp : comp μ (halfGraphon Ω) (cmpl (halfGraphon Ω)) = fun _ _ : Ω => (1 / 4 : ℝ) := by
    rw [cmpl_half]
    show comp μ (fun _ _ : Ω => (1 / 2 : ℝ)) (fun _ _ : Ω => (1 / 2 : ℝ)) = _
    rw [comp_const]
    norm_num
  rw [hcomp, compPow_const, trace_const, Nat.sub_add_cancel hm]

/-- **Sharpness.**  `alt_add_cycle_le_one` is an equality at `W ≡ 1/2`, for every `m ≥ 1`. -/
theorem half_sharp {m : ℕ} (hm : 0 < m) :
    4 ^ m * altDensity (halfGraphon Ω) μ m
        + signedCycleDensity (sgn (halfGraphon Ω)) μ (2 * m) = 1 := by
  rw [half_alt hm, half_signedCycle, add_zero, ← mul_pow]
  norm_num

end AlternatingCycle
