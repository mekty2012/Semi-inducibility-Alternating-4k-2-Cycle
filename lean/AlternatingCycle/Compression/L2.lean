import AlternatingCycle.Necklace.KernelInstance

/-!
# The signed kernel as an operator on `L²`

`Foundation/GraphonL2Operator.lean` provides the kernel operator on all of `L²` for a graphon,
`kernelOpCLM`, together with `kernelOpCLM_isSymmetric`.  The kernel needed here, `K = 2W − 1`, is
not a graphon but a bounded measurable kernel, and is obtained from that operator by

```
  X := 2 • kernelOpCLM hW − P,        P f = ⟨1, f⟩ • 1,
```

where `P` is the rank-one projection onto the constants.  `P` is symmetric by inspection, so `X` is
symmetric by linearity, and — the point — `X` acts by the kernel `2W − 1`:

```
  (X f)(x) = 2∫ W(x,y) f(y) dy − ∫ f(y) dy = ∫ (2W − 1)(x,y) f(y) dy      (a.e.)
```

so its rows are exactly `K(x, ·)`.  That identity (`coeFn_opX`) is what `Compression/HSBound.lean` uses
for Bessel's inequality and what makes the iterates `X^g 1` the kernel iterates of `K`.

The file ends with `inner_oneL2_opX_pow_oneL2`: the `L²` vector moments `⟨1, X^g 1⟩` are the
algebraic moments `kMoment` of `Necklace/KernelInstance.lean`, the numbers in which Fact A expresses
both densities.
-/

open MeasureTheory OddCycleBound OddCycleBound.Spectral.L2Kernel
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ}

/-! ### The rank-one projection onto the constants -/

/-- `P f = ⟨1, f⟩ • 1`. -/
def oneProj (μ : Measure Ω) [IsProbabilityMeasure μ] : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (innerSL ℝ (oneL2 μ)).smulRight (oneL2 μ)

lemma oneProj_apply (f : Lp ℝ 2 μ) : oneProj μ f = (inner ℝ (oneL2 μ) f) • oneL2 μ := rfl

/-- Pairing against the constant function is integration. -/
lemma inner_oneL2_eq_integral (f : Lp ℝ 2 μ) : inner ℝ (oneL2 μ) f = ∫ y, f y ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [oneL2_ae_eq_one (mu := μ)] with y hy
  rw [hy]
  simp [RCLike.inner_apply]

lemma oneProj_isSymmetric : ((oneProj μ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := by
  intro f g
  show inner ℝ (oneProj μ f) g = inner ℝ f (oneProj μ g)
  rw [oneProj_apply, oneProj_apply, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm f (oneL2 μ)]
  ring

/-! ### The operator of the signed kernel -/

/-- `X = 2 · T_W − P`, the `L²` operator of the signed kernel `K = 2W − 1`. -/
def opX (hW : IsGraphon W μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (2 : ℝ) • kernelOpCLM hW - oneProj μ

lemma opX_apply (hW : IsGraphon W μ) (f : Lp ℝ 2 μ) :
    opX hW f = (2 : ℝ) • kernelOpCLM hW f - oneProj μ f := rfl

/-- `X` is symmetric: `T_W` is, and `P` is by inspection. -/
theorem opX_isSymmetric (hW : IsGraphon W μ) :
    ((opX hW : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := by
  intro f g
  have hT : inner ℝ (kernelOpCLM (mu := μ) hW f) g = inner ℝ f (kernelOpCLM (mu := μ) hW g) :=
    kernelOpCLM_isSymmetric (mu := μ) hW f g
  have hP : inner ℝ (oneProj μ f) g = inner ℝ f (oneProj μ g) :=
    oneProj_isSymmetric (μ := μ) f g
  show inner ℝ ((2 : ℝ) • kernelOpCLM hW f - oneProj μ f) g
      = inner ℝ f ((2 : ℝ) • kernelOpCLM hW g - oneProj μ g)
  rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hT, hP]

/-! ### `X` acts by the kernel `2W − 1` -/

lemma integrable_row_mul_l2 {K : Ω → Ω → ℝ} (hK : GoodK K) (f : Lp ℝ 2 μ) (x : Ω) :
    Integrable (fun y => K x y * f y) μ := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  have hf : Integrable (fun y : Ω => f y) μ := (Lp.memLp f).integrable (by norm_num)
  refine Integrable.mono' (hf.norm.const_mul C) ?_ ?_
  · exact (((hK.meas.comp measurable_prodMk_left).stronglyMeasurable).mul
      (Lp.stronglyMeasurable f)).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x y) (abs_nonneg _)

/-- The pointwise identity behind the whole file: `2·(W-transform) − (mean)` is the
`(2W−1)`-transform. -/
lemma kernelOp_sgn_apply (hW : IsGraphon W μ) (f : Lp ℝ 2 μ) (x : Ω) :
    kernelOp (sgn W) μ (fun y => f y) x
      = 2 * kernelOp W μ (fun y => f y) x - ∫ y, f y ∂μ := by
  have hWf := integrable_row_mul_l2 (goodK_of_isGraphon hW) f x
  have hf : Integrable (fun y : Ω => f y) μ := (Lp.memLp f).integrable (by norm_num)
  show (∫ y, (2 * W x y - 1) * f y ∂μ) = 2 * (∫ y, W x y * f y ∂μ) - ∫ y, f y ∂μ
  rw [← integral_const_mul, ← integral_sub (hWf.const_mul 2) hf]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  ring

/-- **`X` is the operator of `K = 2W − 1`.**  Its rows are `K(x, ·)`. -/
theorem coeFn_opX (hW : IsGraphon W μ) (f : Lp ℝ 2 μ) :
    (opX hW f : Ω → ℝ) =ᵐ[μ] kernelOp (sgn W) μ (fun y => f y) := by
  have hT : (kernelOpCLM (mu := μ) hW f : Ω → ℝ) =ᵐ[μ] kernelOp W μ (fun y => f y) := by
    rw [kernelOpCLM_eq_kernelOpL2OfL2_apply (mu := μ) hW f]
    exact goodL2_ae_eq (mu := μ) (good_kernelOp_l2 (mu := μ) hW f)
  have hP : (oneProj μ f : Ω → ℝ) =ᵐ[μ] fun _ => ∫ y, f y ∂μ := by
    rw [oneProj_apply, inner_oneL2_eq_integral]
    filter_upwards [Lp.coeFn_smul (∫ y, f y ∂μ) (oneL2 μ), oneL2_ae_eq_one (mu := μ)]
      with x hx hone
    rw [hx, Pi.smul_apply, hone]
    simp
  filter_upwards [Lp.coeFn_sub ((2 : ℝ) • kernelOpCLM hW f) (oneProj μ f),
    Lp.coeFn_smul (2 : ℝ) (kernelOpCLM (mu := μ) hW f), hT, hP] with x hsub hsmul hTx hPx
  show (opX hW f : Ω → ℝ) x = _
  rw [opX_apply, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hTx, hPx, kernelOp_sgn_apply hW f x]
  simp

/-- On a bounded representative, `X` is the `Good`-level kernel transform. -/
lemma opX_goodL2 (hW : IsGraphon W μ) {f : Ω → ℝ} (hf : Good f) :
    opX hW (goodL2 (mu := μ) hf)
      = goodL2 (mu := μ) (good_kernelOp_goodK (mu := μ) (goodK_sgn hW) hf) := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_opX hW (goodL2 (mu := μ) hf),
    goodL2_ae_eq (mu := μ) (good_kernelOp_goodK (mu := μ) (goodK_sgn hW) hf),
    goodL2_ae_eq (mu := μ) hf] with x hX hgood hf'
  rw [hX, hgood]
  show kernelOp (sgn W) μ (fun y => (goodL2 (mu := μ) hf : Ω → ℝ) y) x = kernelOp (sgn W) μ f x
  exact congrFun (kernelOpGoodK_congr_ae (mu := μ) (K := sgn W) (goodL2_ae_eq (mu := μ) hf)) x

/-! ### The vector moments of `X` are the algebraic moments -/

/-- `X^g 1` is the `g`-fold kernel iterate of the constant function. -/
theorem opX_pow_oneL2 (hW : IsGraphon W μ) : ∀ g : ℕ,
    (opX hW ^ g) (oneL2 μ)
      = goodL2 (mu := μ) (good_kernelOpIter_goodK (mu := μ) (goodK_sgn hW) good_one g)
  | 0 => by rw [pow_zero]; exact (goodL2_one_eq_oneL2 (mu := μ)).symm
  | g + 1 => by
      have hstep : (opX hW ^ (g + 1)) (oneL2 μ) = opX hW ((opX hW ^ g) (oneL2 μ)) := by
        rw [pow_succ' (opX hW) g]; rfl
      rw [hstep, opX_pow_oneL2 hW g, opX_goodL2 hW]
      rfl

/-- **The moment identity.**  The `L²` vector moments of `X` at the constant function are the
algebraic moments `φ (k ^ g)` of `Necklace/KernelInstance.lean`. -/
theorem inner_oneL2_opX_pow_oneL2 (hW : IsGraphon W μ) (g : ℕ) :
    inner ℝ (oneL2 μ) ((opX hW ^ g) (oneL2 μ)) = kMoment hW g := by
  rw [opX_pow_oneL2 hW g, ← goodL2_one_eq_oneL2 (mu := μ),
    inner_goodL2_eq_integral_mul (mu := μ) good_one
      (good_kernelOpIter_goodK (mu := μ) (goodK_sgn hW) good_one g)]
  simp only [one_mul]
  cases g with
  | zero => simp [kernelOpIter, kMoment, KAlg.phi, doubleMean]
  | succ r =>
      have hiter : kernelOpIter μ (sgn W) (r + 1) (fun _ => 1)
          = kernelOp (compPow μ (sgn W) r) μ (fun _ => 1) :=
        (kernelOp_compPow_eq_kernelOpIter_succ (mu := μ) (goodK_sgn hW) good_one r).symm
      rw [hiter]
      show (∫ x, (∫ y, compPow μ (sgn W) r x y * 1 ∂μ) ∂μ) = kMoment hW (r + 1)
      simp only [mul_one]
      rw [kMoment, kU, inr_pow]
      show doubleMean μ (compPow μ (sgn W) r) = 0 + doubleMean μ (compPow μ (sgn W) r)
      rw [zero_add]

end AlternatingCycle
