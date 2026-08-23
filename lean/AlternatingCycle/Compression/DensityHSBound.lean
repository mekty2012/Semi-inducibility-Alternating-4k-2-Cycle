import AlternatingCycle.Compression.DensityL2
import AlternatingCycle.Compression.HSBound

/-!
# Hilbert--Schmidt bound for the normalized centered operator

At prescribed edge density `p`, the centered kernel has square mass at most `p(1-p)`.  After
normalization by `s²=p(1-p)`, finite Bessel sums for the associated operator are therefore at most
one.
-/

open MeasureTheory OddCycleBound OddCycleBound.Spectral.L2Kernel Finset
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ}

lemma integrable_uncurry_of_goodK {K : Ω → Ω → ℝ} (hK : GoodK K) :
    Integrable (Function.uncurry K) (μ.prod μ) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  refine (integrable_const C).mono' hK.meas.stronglyMeasurable.aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  exact hC z.1 z.2

/-- The unnormalized centered kernel has square mass at most its Bernoulli variance. -/
theorem kernelSqNorm_centered_le (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) :
    kernelSqNorm μ (centered W D.p) ≤ D.p * D.q := by
  let U : Ω → Ω → ℝ := fun x y => (1 - 2 * D.p) * W x y + D.p ^ 2
  have hU : GoodK U := by
    refine ⟨?_, |1 - 2 * D.p| + D.p ^ 2, by positivity, fun x y => ?_⟩
    · exact (measurable_const.mul hW.meas).add measurable_const
    · change |(1 - 2 * D.p) * W x y + D.p ^ 2| ≤ _
      calc
        |(1 - 2 * D.p) * W x y + D.p ^ 2| ≤
            |(1 - 2 * D.p) * W x y| + |D.p ^ 2| := abs_add_le _ _
        _ = |1 - 2 * D.p| * |W x y| + |D.p ^ 2| := by rw [abs_mul]
        _ ≤ |1 - 2 * D.p| * 1 + D.p ^ 2 := by
          have hWabs : |W x y| ≤ 1 := by
            rw [abs_of_nonneg (hW.nonneg x y)]
            exact hW.le_one x y
          rw [abs_of_nonneg (sq_nonneg D.p)]
          exact add_le_add (mul_le_mul_of_nonneg_left hWabs (abs_nonneg _)) le_rfl
        _ = |1 - 2 * D.p| + D.p ^ 2 := by ring
  have hpoint : ∀ z : Ω × Ω,
      centered W D.p z.1 z.2 * centered W D.p z.1 z.2 ≤ U z.1 z.2 := by
    intro z
    have h0 := hW.nonneg z.1 z.2
    have h1 := hW.le_one z.1 z.2
    simp only [centered, U]
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have hcenter := goodK_centered hW D.p
  rw [kernelSqNorm_eq_integral_prod_of_goodK hcenter]
  calc
    (∫ z : Ω × Ω,
        centered W D.p z.1 z.2 * centered W D.p z.1 z.2 ∂(μ.prod μ)) ≤
        ∫ z : Ω × Ω, U z.1 z.2 ∂(μ.prod μ) :=
      integral_mono (integrable_uncurry_mul_self_of_goodK hcenter)
        (integrable_uncurry_of_goodK hU) hpoint
    _ = doubleMean μ U := by
      unfold doubleMean
      exact integral_prod (Function.uncurry U) (integrable_uncurry_of_goodK hU)
    _ = (1 - 2 * D.p) * edgeDensity W μ + D.p ^ 2 := by
      unfold doubleMean
      have hdeg : Integrable (degree W μ) μ := (good_degree hW).integrable
      have hinner : (fun x => ∫ y, U x y ∂μ) =
          fun x => (1 - 2 * D.p) * degree W μ x + D.p ^ 2 := by
        funext x
        rw [show (fun y => U x y) =
            fun y => (1 - 2 * D.p) * W x y + D.p ^ 2 by rfl,
          integral_add ((goodK_row (goodK_of_isGraphon hW) x).integrable.const_mul _)
            (integrable_const _), integral_const_mul, integral_const]
        simp [degree]
      rw [hinner, integral_add (hdeg.const_mul _) (integrable_const _), integral_const_mul,
        integral_const]
      simp [edgeDensity, mean]
    _ = D.p * D.q := by rw [hp, D.q_eq]; ring

/-- Normalization by `s²=pq` gives a unit squared-kernel-norm bound. -/
theorem kernelSqNorm_normalizedCentered_le_one (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) :
    kernelSqNorm μ (normalizedCentered W D.p D.s) ≤ 1 := by
  have hcenter := goodK_centered hW D.p
  have hnorm := goodK_normalizedCentered hW D.p D.s
  rw [kernelSqNorm_eq_integral_prod_of_goodK hnorm,
    show (fun z : Ω × Ω =>
      normalizedCentered W D.p D.s z.1 z.2 * normalizedCentered W D.p D.s z.1 z.2) =
      fun z => (D.s⁻¹) ^ 2 *
        (centered W D.p z.1 z.2 * centered W D.p z.1 z.2) by
      funext z
      simp only [normalizedCentered, centered]
      field_simp [ne_of_gt D.s_pos],
    integral_const_mul]
  calc
    (D.s⁻¹) ^ 2 *
        ∫ z : Ω × Ω, centered W D.p z.1 z.2 * centered W D.p z.1 z.2 ∂(μ.prod μ) =
      (D.s⁻¹) ^ 2 * kernelSqNorm μ (centered W D.p) := by
        rw [kernelSqNorm_eq_integral_prod_of_goodK hcenter]
    _ ≤ (D.s⁻¹) ^ 2 * (D.p * D.q) :=
      mul_le_mul_of_nonneg_left (kernelSqNorm_centered_le hW D hp) (sq_nonneg _)
    _ = 1 := by rw [← D.s_sq, inv_pow]; field_simp [ne_of_gt D.s_pos]

lemma good_kernelOp_normalizedCentered_l2 (hW : IsGraphon W μ) (D : DensityParams)
    (f : Lp ℝ 2 μ) :
    Good (kernelOp (normalizedCentered W D.p D.s) μ (fun y => f y)) := by
  have h : kernelOp (normalizedCentered W D.p D.s) μ (fun y => f y) =
      fun x => D.s⁻¹ * kernelOp W μ (fun y => f y) x -
        (D.p / D.s) * ∫ y, f y ∂μ :=
    funext (kernelOp_normalizedCentered_apply hW D f)
  rw [h]
  exact good_sub (good_smul D.s⁻¹ (good_kernelOp_l2 (mu := μ) hW f)) (good_const _)

lemma densityRowInner_eq (hW : IsGraphon W μ) (D : DensityParams)
    (f : Lp ℝ 2 μ) (x : Ω) :
    inner ℝ
        (goodL2 (mu := μ) (goodK_row (goodK_normalizedCentered hW D.p D.s) x)) f =
      kernelOp (normalizedCentered W D.p D.s) μ (fun y => f y) x :=
  inner_goodK_row_l2_eq_kernelOp (mu := μ)
    (goodK_normalizedCentered hW D.p D.s) f x

lemma integrable_densityRowInner_sq (hW : IsGraphon W μ) (D : DensityParams)
    (f : Lp ℝ 2 μ) :
    Integrable (fun x =>
      (inner ℝ
        (goodL2 (mu := μ) (goodK_row (goodK_normalizedCentered hW D.p D.s) x)) f) ^ 2) μ := by
  have hgood : Good (fun x : Ω =>
      kernelOp (normalizedCentered W D.p D.s) μ (fun y => f y) x *
        kernelOp (normalizedCentered W D.p D.s) μ (fun y => f y) x) :=
    (good_kernelOp_normalizedCentered_l2 hW D f).mul
      (good_kernelOp_normalizedCentered_l2 hW D f)
  refine hgood.integrable.congr (ae_of_all _ fun x => ?_)
  change kernelOp (normalizedCentered W D.p D.s) μ (fun y => f y) x *
      kernelOp (normalizedCentered W D.p D.s) μ (fun y => f y) x =
    (inner ℝ
      (goodL2 (mu := μ) (goodK_row (goodK_normalizedCentered hW D.p D.s) x)) f) ^ 2
  rw [densityRowInner_eq hW D f x, sq]

/-- The output norm is the integrated square of the normalized centered row functional. -/
theorem norm_centeredOp_sq_eq (hW : IsGraphon W μ) (D : DensityParams) (f : Lp ℝ 2 μ) :
    ‖centeredOp hW D f‖ ^ 2 =
      ∫ x, (inner ℝ
        (goodL2 (mu := μ) (goodK_row (goodK_normalizedCentered hW D.p D.s) x)) f) ^ 2 ∂μ := by
  rw [norm_sq_eq_integral_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_centeredOp hW D f] with x hx
  rw [hx, densityRowInner_eq hW D f x, sq]

/-- The normalized centered operator has Hilbert--Schmidt squared norm at most one on every
finite orthonormal family. -/
theorem sum_norm_centeredOp_sq_le (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) {ι : Type*} [Fintype ι] {v : ι → Lp ℝ 2 μ}
    (hv : Orthonormal ℝ v) : ∑ i, ‖centeredOp hW D (v i)‖ ^ 2 ≤ 1 := by
  classical
  let hK := goodK_normalizedCentered hW D.p D.s
  set row : Ω → Lp ℝ 2 μ := fun x => goodL2 (mu := μ) (goodK_row hK x) with hrow
  have hterm : ∀ i, ‖centeredOp hW D (v i)‖ ^ 2 =
      ∫ x, (inner ℝ (row x) (v i)) ^ 2 ∂μ :=
    fun i => norm_centeredOp_sq_eq hW D (v i)
  have hint : ∀ i, Integrable (fun x => (inner ℝ (row x) (v i)) ^ 2) μ :=
    fun i => integrable_densityRowInner_sq hW D (v i)
  have hbessel : ∀ x : Ω, ∑ i, (inner ℝ (row x) (v i)) ^ 2 ≤ ‖row x‖ ^ 2 := by
    intro x
    have h := hv.sum_inner_products_le (s := (univ : Finset ι)) (row x)
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (row x) (v i), Real.norm_eq_abs, sq_abs]
  have hnormrow : Integrable (fun x => ‖row x‖ ^ 2) μ := by
    refine (integrable_goodK_row_inner_self (mu := μ) hK).congr
      (ae_of_all _ fun x => ?_)
    exact real_inner_self_eq_norm_sq _
  calc
    ∑ i, ‖centeredOp hW D (v i)‖ ^ 2 =
        ∑ i, ∫ x, (inner ℝ (row x) (v i)) ^ 2 ∂μ :=
      Finset.sum_congr rfl fun i _ => hterm i
    _ = ∫ x, ∑ i, (inner ℝ (row x) (v i)) ^ 2 ∂μ :=
      (integral_finsetSum _ fun i _ => hint i).symm
    _ ≤ ∫ x, ‖row x‖ ^ 2 ∂μ :=
      integral_mono (integrable_finsetSum _ fun i _ => hint i) hnormrow hbessel
    _ = kernelSqNorm μ (normalizedCentered W D.p D.s) := by
      refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_))
        (integral_goodK_row_inner_self_eq_kernelSqNorm (mu := μ) hK)
      exact (real_inner_self_eq_norm_sq _).symm
    _ ≤ 1 := kernelSqNorm_normalizedCentered_le_one hW D hp

end AlternatingCycle
