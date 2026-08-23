import AlternatingCycle.Compression.DensityCubic
import AlternatingCycle.Necklace.MatrixInstance
import AlternatingCycle.Matrix.DensityCoefficients
import AlternatingCycle.Positivity
import AlternatingCycle.Fubini
import AlternatingCycle.Sharp

/-!
# Alternating-cycle inequality at fixed edge density

The normalized centered kernel is compressed to a finite diagonal spectrum.  Exact moment
agreement transfers the period-two kernel word to the diagonal matrix inequality.
-/

open MeasureTheory OddCycleBound Finset Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace AlternatingCycle

namespace Spectrum

variable {n : ℕ} (T : Spectrum n)

lemma matMoment_model (g : ℕ) :
    matMoment T.model.A T.e g = ∑ i, T.e i ^ 2 * T.lam i ^ g := by
  rw [matMoment, model_A, Matrix.diagonal_pow]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.pow_apply, pow_two]
  exact Finset.sum_congr rfl fun i _ => by ring

end Spectrum

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ}

/-- The fixed-density inequality in normalized form. -/
theorem fixedDensity_normalized_le_one (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    (D.p * D.q)⁻¹ ^ m * altDensity W μ m +
      (D.p * D.q)⁻¹ ^ m * signedCycleDensity (centered W D.p) μ (2 * m) ≤ 1 := by
  classical
  obtain ⟨N, T, hnu0, hhead, hmom⟩ := exists_fixedDensity_spectrum_cubic hW D hp hm3
  have hmatrix := T.matrix_fixedDensity_diagonal D.a D.b D.delta D.ab_eq D.delta_eq
    D.abs_delta_le_one hnu0 hhead hm
  change Matrix.trace
      (((Matrix.vecMulVec T.e T.e + D.a • T.model.A) *
        (Matrix.vecMulVec T.e T.e - D.b • T.model.A)) ^ m) +
      Matrix.trace (T.model.A ^ (2 * m)) ≤ 1 at hmatrix
  rw [trace_colorPattern_matrix_add D.a D.b D.ab_eq T.model.A T.e hm] at hmatrix
  have hagree : ∀ g, g < 2 * m →
      densityKMoment hW D g = matMoment T.model.A T.e g := by
    intro g hg
    rw [T.matMoment_model, hmom g (le_of_lt hg)]
  have hterm : ∀ x ∈ range (2 * m + 1), ∀ y ∈ range (2 * m + 1),
      RankOne.coeff (RankOne.colorPattern D.a D.b) (densityKMoment hW D)
          (2 * m) x y * densityKMoment hW D (x + y) =
        RankOne.coeff (RankOne.colorPattern D.a D.b)
          (matMoment T.model.A T.e) (2 * m) x y *
            matMoment T.model.A T.e (x + y) := by
    intro x _ y _
    by_cases hxy : x + y < 2 * m
    · rw [RankOne.coeff_congr (RankOne.colorPattern D.a D.b) (2 * m) hagree x y,
        hagree (x + y) hxy]
    · rw [RankOne.coeff_eq_zero_of_le_add (RankOne.colorPattern D.a D.b)
          (densityKMoment hW D) (2 * m) x y (by omega),
        RankOne.coeff_eq_zero_of_le_add (RankOne.colorPattern D.a D.b)
          (matMoment T.model.A T.e) (2 * m) x y (by omega), zero_mul, zero_mul]
  rw [normalized_alt_add_centeredCycle_eq_necklace hW D hm]
  exact le_trans
    (le_of_eq (Finset.sum_congr rfl fun x hx =>
      Finset.sum_congr rfl fun y hy => hterm x hx y hy)) hmatrix

/-- The fixed-density inequality with the centered even-cycle term, conditional on edge density
`D.p`. -/
theorem fixedDensity_alt_add_centeredCycle_le_params (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    altDensity W μ m + signedCycleDensity (centered W D.p) μ (2 * m) ≤
      (D.p * D.q) ^ m := by
  have hnorm := fixedDensity_normalized_le_one hW D hp hm hm3
  have hpq : 0 < D.p * D.q := mul_pos D.p_pos D.q_pos
  have hpow : 0 < (D.p * D.q) ^ m := pow_pos hpq m
  have hcancel : (D.p * D.q) ^ m * (D.p * D.q)⁻¹ ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hpq), one_pow]
  calc
    altDensity W μ m + signedCycleDensity (centered W D.p) μ (2 * m) =
        (D.p * D.q) ^ m *
          ((D.p * D.q)⁻¹ ^ m * altDensity W μ m +
            (D.p * D.q)⁻¹ ^ m * signedCycleDensity (centered W D.p) μ (2 * m)) := by
      rw [mul_add, ← mul_assoc, hcancel, one_mul, ← mul_assoc, hcancel, one_mul]
    _ ≤ (D.p * D.q) ^ m * 1 :=
      mul_le_mul_of_nonneg_left hnorm (le_of_lt hpow)
    _ = (D.p * D.q) ^ m := mul_one _

/-- The alternating-cycle profile bound at fixed edge density. -/
theorem fixedDensity_alt_le_params (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    altDensity W μ m ≤ (D.p * D.q) ^ m := by
  have hmain := fixedDensity_alt_add_centeredCycle_le_params hW D hp hm hm3
  have hpos : 0 ≤ signedCycleDensity (centered W D.p) μ (2 * m) := by
    have h := signedCycleDensity_nonneg (μ := μ) (goodK_centered hW D.p)
      (centered_symm hW D.p) (m - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
    exact h
  linarith

/-- The fixed-density inequality with the centered even-cycle term under the polynomial condition
on `p`. -/
theorem fixedDensity_alt_add_centeredCycle_le_of_central (hW : IsGraphon W μ) {p : ℝ}
    (hp : edgeDensity W μ = p) (hcentral : CentralDensity p)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    altDensity W μ m + signedCycleDensity (centered W p) μ (2 * m) ≤
      (p * (1 - p)) ^ m := by
  let D := DensityParams.ofCentral p hcentral
  simpa [D, DensityParams.ofCentral] using
    fixedDensity_alt_add_centeredCycle_le_params hW D hp hm hm3

/-- The fixed-density inequality with the centered even-cycle term, conditional on edge density
`p` in the stated closed interval. -/
theorem fixedDensity_alt_add_centeredCycle_le (hW : IsGraphon W μ) {p : ℝ}
    (hp : edgeDensity W μ = p)
    (hlow : (5 - Real.sqrt 5) / 10 ≤ p)
    (hupp : p ≤ (5 + Real.sqrt 5) / 10)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    altDensity W μ m + signedCycleDensity (centered W p) μ (2 * m) ≤
      (p * (1 - p)) ^ m :=
  fixedDensity_alt_add_centeredCycle_le_of_central hW hp
    ((centralDensity_iff_interval p).2 ⟨hlow, hupp⟩) hm hm3

/-- The profile bound conditional on edge density `p` in the stated closed interval. -/
theorem fixedDensity_alt_le (hW : IsGraphon W μ) {p : ℝ}
    (hp : edgeDensity W μ = p)
    (hlow : (5 - Real.sqrt 5) / 10 ≤ p)
    (hupp : p ≤ (5 + Real.sqrt 5) / 10)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    altDensity W μ m ≤ (p * (1 - p)) ^ m := by
  let D := DensityParams.ofCentral p ((centralDensity_iff_interval p).2 ⟨hlow, hupp⟩)
  simpa [D, DensityParams.ofCentral] using fixedDensity_alt_le_params hW D hp hm hm3

/-- The fixed-density inequality with the centered even-cycle term, written as cyclic integrals. -/
theorem fixedDensity_alt_add_centeredCycle_le_integral (hW : IsGraphon W μ) {p : ℝ}
    (hp : edgeDensity W μ = p)
    (hlow : (5 - Real.sqrt 5) / 10 ≤ p)
    (hupp : p ≤ (5 + Real.sqrt 5) / 10)
    (s : ℕ) (hs : 1 ≤ s) :
    (∫ v : Fin (2 * (2 * s) + 2) → Ω,
        ∏ i, altKernels W (2 * s) i (v i) (v (i + 1)) ∂(Measure.pi fun _ => μ)) +
      (∫ v : Fin (2 * (2 * s) + 2) → Ω,
        ∏ i, centered W p (v i) (v (i + 1)) ∂(Measure.pi fun _ => μ)) ≤
      (p * (1 - p)) ^ (2 * s + 1) := by
  have h := fixedDensity_alt_add_centeredCycle_le hW hp hlow hupp
    (⟨s, rfl⟩ : Odd (2 * s + 1)) (by omega)
  have hlen : 2 * (2 * s + 1) = 2 * (2 * s) + 1 + 1 := by ring
  rw [altDensity_eq_integral hW (2 * s), hlen,
    signedCycleDensity_eq_integral (goodK_centered hW p) (2 * (2 * s) + 1)] at h
  exact h

/-- The fixed-density profile bound written as a cyclic integral. -/
theorem fixedDensity_alt_le_integral (hW : IsGraphon W μ) {p : ℝ}
    (hp : edgeDensity W μ = p)
    (hlow : (5 - Real.sqrt 5) / 10 ≤ p)
    (hupp : p ≤ (5 + Real.sqrt 5) / 10)
    (s : ℕ) (hs : 1 ≤ s) :
    (∫ v : Fin (2 * (2 * s) + 2) → Ω,
        ∏ i, altKernels W (2 * s) i (v i) (v (i + 1)) ∂(Measure.pi fun _ => μ)) ≤
      (p * (1 - p)) ^ (2 * s + 1) := by
  have h := fixedDensity_alt_le hW hp hlow hupp
    (⟨s, rfl⟩ : Odd (2 * s + 1)) (by omega)
  rw [altDensity_eq_integral hW (2 * s)] at h
  exact h

/-! ### Constant graphons -/

/-- The constant graphon with value `p`. -/
def constantGraphon (p : ℝ) (Ω : Type*) : Ω → Ω → ℝ := fun _ _ => p

lemma isGraphon_constant {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsGraphon (constantGraphon p Ω) μ where
  meas := measurable_const
  nonneg := fun _ _ => hp0
  le_one := fun _ _ => hp1
  symm := fun _ _ => rfl

@[simp] lemma cmpl_constant (p : ℝ) :
    cmpl (constantGraphon p Ω) = constantGraphon (1 - p) Ω := rfl

@[simp] lemma centered_constant_self (p : ℝ) :
    centered (constantGraphon p Ω) p = constantGraphon 0 Ω := by
  funext x y
  simp [centered, constantGraphon]

/-- The alternating density of a constant graphon attains the profile value. -/
theorem constant_altDensity (p : ℝ) {m : ℕ} (hm : 0 < m) :
    altDensity (constantGraphon p Ω) μ m = (p * (1 - p)) ^ m := by
  rw [altDensity]
  have hcomp : comp μ (constantGraphon p Ω) (cmpl (constantGraphon p Ω)) =
      constantGraphon (p * (1 - p)) Ω := by
    rw [cmpl_constant]
    change comp μ (fun _ _ : Ω => p) (fun _ _ : Ω => 1 - p) =
      fun _ _ : Ω => p * (1 - p)
    rw [comp_const]
  rw [hcomp]
  change trace μ (compPow μ (fun _ _ : Ω => p * (1 - p)) (m - 1)) = _
  rw [compPow_const, trace_const, Nat.sub_add_cancel hm]

/-- The centered even-cycle term vanishes for a constant graphon. -/
theorem constant_centeredCycle (p : ℝ) (r : ℕ) :
    signedCycleDensity (centered (constantGraphon p Ω) p) μ r = 0 := by
  rw [centered_constant_self, signedCycleDensity]
  change trace μ (compPow μ (fun _ _ : Ω => (0 : ℝ)) (r - 1)) = 0
  rw [compPow_const, trace_const]
  simp

/-- Equality in the fixed-density inequality with the centered even-cycle term at every constant
graphon. -/
theorem constant_fixedDensity_sharp (p : ℝ) {m : ℕ} (hm : 0 < m) :
    altDensity (constantGraphon p Ω) μ m +
        signedCycleDensity (centered (constantGraphon p Ω) p) μ (2 * m) =
      (p * (1 - p)) ^ m := by
  rw [constant_altDensity p hm, constant_centeredCycle, add_zero]

end AlternatingCycle
