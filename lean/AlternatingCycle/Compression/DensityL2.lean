import AlternatingCycle.Compression.L2

/-!
# The normalized centered kernel on `L²`

The operator in this module acts by the kernel `(W-p)/s`, where `s²=p(1-p)`.  It is symmetric,
and the constant vector has zero first moment when `p` is the edge density of `W`.
-/

open MeasureTheory OddCycleBound OddCycleBound.Spectral.L2Kernel
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ}

/-- The continuous linear operator with kernel `(W-p)/s`. -/
def centeredOp (hW : IsGraphon W μ) (D : DensityParams) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  D.s⁻¹ • kernelOpCLM hW - (D.p / D.s) • oneProj μ

lemma centeredOp_apply (hW : IsGraphon W μ) (D : DensityParams) (f : Lp ℝ 2 μ) :
    centeredOp hW D f = D.s⁻¹ • kernelOpCLM hW f - (D.p / D.s) • oneProj μ f := rfl

/-- The normalized centered operator is symmetric. -/
theorem centeredOp_isSymmetric (hW : IsGraphon W μ) (D : DensityParams) :
    ((centeredOp hW D : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := by
  intro f g
  have hT : inner ℝ (kernelOpCLM (mu := μ) hW f) g =
      inner ℝ f (kernelOpCLM (mu := μ) hW g) :=
    kernelOpCLM_isSymmetric (mu := μ) hW f g
  have hP : inner ℝ (oneProj μ f) g = inner ℝ f (oneProj μ g) :=
    oneProj_isSymmetric (μ := μ) f g
  show inner ℝ (D.s⁻¹ • kernelOpCLM hW f - (D.p / D.s) • oneProj μ f) g =
    inner ℝ f (D.s⁻¹ • kernelOpCLM hW g - (D.p / D.s) • oneProj μ g)
  rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right, hT, hP]

lemma kernelOp_normalizedCentered_apply (hW : IsGraphon W μ) (D : DensityParams)
    (f : Lp ℝ 2 μ) (x : Ω) :
    kernelOp (normalizedCentered W D.p D.s) μ (fun y => f y) x =
      D.s⁻¹ * kernelOp W μ (fun y => f y) x - (D.p / D.s) * ∫ y, f y ∂μ := by
  have hWf := integrable_row_mul_l2 (goodK_of_isGraphon hW) f x
  have hf : Integrable (fun y : Ω => f y) μ := (Lp.memLp f).integrable (by norm_num)
  have hpf : Integrable (fun y : Ω => D.p * f y) μ := hf.const_mul D.p
  show (∫ y, ((W x y - D.p) / D.s) * f y ∂μ) = _
  rw [show (fun y => ((W x y - D.p) / D.s) * f y) =
      fun y => D.s⁻¹ * (W x y * f y - D.p * f y) by
        funext y; field_simp [ne_of_gt D.s_pos],
    integral_const_mul, integral_sub hWf hpf, integral_const_mul]
  simp only [kernelOp]
  field_simp [ne_of_gt D.s_pos]

/-- Pointwise, `centeredOp` is the integral operator of the normalized centered kernel. -/
theorem coeFn_centeredOp (hW : IsGraphon W μ) (D : DensityParams) (f : Lp ℝ 2 μ) :
    (centeredOp hW D f : Ω → ℝ) =ᵐ[μ]
      kernelOp (normalizedCentered W D.p D.s) μ (fun y => f y) := by
  have hT : (kernelOpCLM (mu := μ) hW f : Ω → ℝ) =ᵐ[μ]
      kernelOp W μ (fun y => f y) := by
    rw [kernelOpCLM_eq_kernelOpL2OfL2_apply (mu := μ) hW f]
    exact goodL2_ae_eq (mu := μ) (good_kernelOp_l2 (mu := μ) hW f)
  have hP : (oneProj μ f : Ω → ℝ) =ᵐ[μ] fun _ => ∫ y, f y ∂μ := by
    rw [oneProj_apply, inner_oneL2_eq_integral]
    filter_upwards [Lp.coeFn_smul (∫ y, f y ∂μ) (oneL2 μ), oneL2_ae_eq_one (mu := μ)]
      with x hx hone
    rw [hx, Pi.smul_apply, hone]
    simp
  filter_upwards
      [Lp.coeFn_sub (D.s⁻¹ • kernelOpCLM hW f) ((D.p / D.s) • oneProj μ f),
        Lp.coeFn_smul D.s⁻¹ (kernelOpCLM (mu := μ) hW f),
        Lp.coeFn_smul (D.p / D.s) (oneProj μ f), hT, hP]
      with x hsub hsT hsP hTx hPx
  show (centeredOp hW D f : Ω → ℝ) x = _
  rw [centeredOp_apply, hsub, Pi.sub_apply, hsT, hsP, Pi.smul_apply, Pi.smul_apply,
    hTx, hPx, kernelOp_normalizedCentered_apply hW D f x]
  simp only [smul_eq_mul]

/-- Prescribing the edge density makes the normalized centered first moment vanish. -/
lemma inner_oneL2_centeredOp_oneL2 (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) :
    inner ℝ (oneL2 μ) (centeredOp hW D (oneL2 μ)) = 0 := by
  rw [centeredOp_apply, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    kernelOpCLM_one_eq_degreeL2 hW, inner_oneL2_degreeL2_eq_edgeDensity hW, hp,
    oneProj_apply, inner_oneL2_oneL2]
  simp only [one_smul, inner_oneL2_oneL2]
  field_simp [ne_of_gt D.s_pos]
  ring

lemma centeredOp_goodL2 (hW : IsGraphon W μ) (D : DensityParams)
    {f : Ω → ℝ} (hf : Good f) :
    centeredOp hW D (goodL2 (mu := μ) hf) =
      goodL2 (mu := μ)
        (good_kernelOp_goodK (mu := μ) (goodK_normalizedCentered hW D.p D.s) hf) := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_centeredOp hW D (goodL2 (mu := μ) hf),
    goodL2_ae_eq (mu := μ)
      (good_kernelOp_goodK (mu := μ) (goodK_normalizedCentered hW D.p D.s) hf),
    goodL2_ae_eq (mu := μ) hf] with x hT hgood hf'
  rw [hT, hgood]
  show kernelOp (normalizedCentered W D.p D.s) μ
      (fun y => (goodL2 (mu := μ) hf : Ω → ℝ) y) x =
    kernelOp (normalizedCentered W D.p D.s) μ f x
  exact congrFun
    (kernelOpGoodK_congr_ae (mu := μ) (K := normalizedCentered W D.p D.s)
      (goodL2_ae_eq (mu := μ) hf)) x

/-- Iterating `centeredOp` on the constant vector agrees with concrete normalized-kernel
iteration. -/
theorem centeredOp_pow_oneL2 (hW : IsGraphon W μ) (D : DensityParams) : ∀ g : ℕ,
    (centeredOp hW D ^ g) (oneL2 μ) =
      goodL2 (mu := μ)
        (good_kernelOpIter_goodK (mu := μ) (goodK_normalizedCentered hW D.p D.s) good_one g)
  | 0 => by rw [pow_zero]; exact (goodL2_one_eq_oneL2 (mu := μ)).symm
  | g + 1 => by
      have hstep : (centeredOp hW D ^ (g + 1)) (oneL2 μ) =
          centeredOp hW D ((centeredOp hW D ^ g) (oneL2 μ)) := by
        rw [pow_succ' (centeredOp hW D) g]
        rfl
      rw [hstep, centeredOp_pow_oneL2 hW D g, centeredOp_goodL2 hW D]
      rfl

/-- The `L²` vector moments of the normalized centered operator are its algebraic kernel
moments. -/
theorem inner_oneL2_centeredOp_pow_oneL2 (hW : IsGraphon W μ) (D : DensityParams) (g : ℕ) :
    inner ℝ (oneL2 μ) ((centeredOp hW D ^ g) (oneL2 μ)) = densityKMoment hW D g := by
  rw [centeredOp_pow_oneL2 hW D g, ← goodL2_one_eq_oneL2 (mu := μ),
    inner_goodL2_eq_integral_mul (mu := μ) good_one
      (good_kernelOpIter_goodK (mu := μ) (goodK_normalizedCentered hW D.p D.s) good_one g)]
  simp only [one_mul]
  cases g with
  | zero => simp [kernelOpIter, densityKMoment, KAlg.phi, doubleMean]
  | succ r =>
      have hiter : kernelOpIter μ (normalizedCentered W D.p D.s) (r + 1) (fun _ => 1) =
          kernelOp (compPow μ (normalizedCentered W D.p D.s) r) μ (fun _ => 1) :=
        (kernelOp_compPow_eq_kernelOpIter_succ (mu := μ)
          (goodK_normalizedCentered hW D.p D.s) good_one r).symm
      rw [hiter]
      show (∫ x, ∫ y, compPow μ (normalizedCentered W D.p D.s) r x y * 1 ∂μ ∂μ) =
        densityKMoment hW D (r + 1)
      simp only [mul_one]
      rw [densityKMoment, densityKU, inr_pow]
      show doubleMean μ (compPow μ (normalizedCentered W D.p D.s) r) =
        0 + doubleMean μ (compPow μ (normalizedCentered W D.p D.s) r)
      rw [zero_add]

lemma densityKMoment_one_eq_zero (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) : densityKMoment hW D 1 = 0 := by
  rw [← inner_oneL2_centeredOp_pow_oneL2 hW D 1, pow_one]
  exact inner_oneL2_centeredOp_oneL2 hW D hp

end AlternatingCycle
