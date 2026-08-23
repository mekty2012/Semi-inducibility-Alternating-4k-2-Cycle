import AlternatingCycle.Compression.DensityHSBound
import AlternatingCycle.Compression.Krylov
import AlternatingCycle.Matrix.Spectral

/-!
# Krylov spectrum of the normalized centered operator

The finite diagonal spectrum in this module preserves normalized centered kernel moments through
the requested cutoff and inherits the unit spectral bound.
-/

open MeasureTheory OddCycleBound OddCycleBound.Spectral.L2Kernel Finset Matrix
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ}

/-- The Krylov space of the normalized centered operator at the constant vector. -/
def densityKryV (hW : IsGraphon W μ) (D : DensityParams) (m : ℕ) : Submodule ℝ (Lp ℝ 2 μ) :=
  krylov (centeredOp hW D) (oneL2 μ) (2 * m)

/-- The orthogonal compression to the normalized centered Krylov space. -/
def densityKryC (hW : IsGraphon W μ) (D : DensityParams) (m : ℕ) :
    densityKryV hW D m →L[ℝ] densityKryV hW D m :=
  krylovComp (centeredOp hW D) (oneL2 μ) (2 * m)

lemma densityKryC_isSymmetric (hW : IsGraphon W μ) (D : DensityParams) (m : ℕ) :
    ((densityKryC hW D m : densityKryV hW D m →L[ℝ] densityKryV hW D m) :
      densityKryV hW D m →ₗ[ℝ] densityKryV hW D m).IsSymmetric :=
  krylovComp_isSymmetric _ _ _ (centeredOp_isSymmetric hW D)

instance densityKryV_finiteDimensional (hW : IsGraphon W μ) (D : DensityParams) (m : ℕ) :
    FiniteDimensional ℝ (densityKryV hW D m) := by
  unfold densityKryV
  infer_instance

/-- A finite diagonal spectrum preserving every centered moment through degree `2m`. -/
theorem exists_fixedDensity_spectrum (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) (m : ℕ) :
    ∃ (N : ℕ) (T : Spectrum N),
      ∀ j ≤ 2 * m, ∑ i, T.e i ^ 2 * T.lam i ^ j = densityKMoment hW D j := by
  classical
  have hCsymm := densityKryC_isSymmetric hW D m
  set N := Module.finrank ℝ (densityKryV hW D m) with hN
  set b := hCsymm.eigenvectorBasis (n := N) rfl with hb
  set lam : Fin N → ℝ := atomEigen hCsymm with hlam
  set g : densityKryV hW D m :=
    krylovVec (centeredOp hW D) (oneL2 μ) (2 * m) with hg
  set e : Fin N → ℝ := atomCoord hCsymm g with he
  have hmom : ∀ j : ℕ, ∑ i, e i ^ 2 * lam i ^ j =
      inner ℝ g
        (((densityKryC hW D m : densityKryV hW D m →ₗ[ℝ] densityKryV hW D m) ^ j) g) := by
    intro j
    exact (inner_pow_eq_sum hCsymm g j).symm
  have heunit : ∑ i, e i ^ 2 = 1 := by
    have h0 := hmom 0
    simp only [pow_zero, mul_one] at h0
    have hgg : inner ℝ g
        (((densityKryC hW D m : densityKryV hW D m →ₗ[ℝ] densityKryV hW D m) ^ 0) g) = 1 := by
      show inner ℝ g g = 1
      rw [real_inner_self_eq_norm_sq]
      show ‖oneL2 (Omega := Ω) μ‖ ^ 2 = 1
      exact norm_oneL2_sq_eq_one
    exact h0.trans (by simpa using hgg)
  have htau : ∑ i, lam i ^ 2 ≤ 1 := by
    have hcoe : Orthonormal ℝ (fun i => ((b i : densityKryV hW D m) : Lp ℝ 2 μ)) := by
      constructor
      · intro i
        exact b.orthonormal.1 i
      · intro i j hij
        exact b.orthonormal.2 hij
    have hstep : ∀ i,
        lam i ^ 2 ≤ ‖centeredOp hW D ((b i : densityKryV hW D m) : Lp ℝ 2 μ)‖ ^ 2 := by
      intro i
      have heig : densityKryC hW D m (b i) = lam i • b i :=
        hCsymm.apply_eigenvectorBasis rfl i
      have hnorm : ‖densityKryC hW D m (b i)‖ = |lam i| := by
        rw [heig, norm_smul, Real.norm_eq_abs, b.orthonormal.1 i, mul_one]
      have hle : ‖densityKryC hW D m (b i)‖ ≤
          ‖centeredOp hW D ((b i : densityKryV hW D m) : Lp ℝ 2 μ)‖ :=
        (densityKryV hW D m).norm_orthogonalProjectionOnto_apply_le
          (centeredOp hW D ((b i : densityKryV hW D m) : Lp ℝ 2 μ))
      rw [hnorm] at hle
      nlinarith [abs_nonneg (lam i), hle, sq_abs (lam i)]
    calc
      ∑ i, lam i ^ 2 ≤
          ∑ i, ‖centeredOp hW D ((b i : densityKryV hW D m) : Lp ℝ 2 μ)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hstep i
      _ ≤ 1 := sum_norm_centeredOp_sq_le hW D hp hcoe
  let T : Spectrum N := ⟨lam, e, heunit, htau⟩
  refine ⟨N, T, ?_⟩
  intro j hj
  change ∑ i, e i ^ 2 * lam i ^ j = densityKMoment hW D j
  rw [hmom j, coeLinear_pow (densityKryC hW D m) g j]
  show inner ℝ
      (krylovVec (centeredOp hW D) (oneL2 μ) (2 * m))
      ((krylovComp (centeredOp hW D) (oneL2 μ) (2 * m) ^ j)
        (krylovVec (centeredOp hW D) (oneL2 μ) (2 * m))) = densityKMoment hW D j
  rw [inner_pow_krylovComp (centeredOp hW D) (oneL2 μ) hj,
    inner_oneL2_centeredOp_pow_oneL2 hW D j]

/-- For a positive cutoff, the diagonal spectrum is centered and retains the full moment
agreement needed by the fixed-density coefficient theorem. -/
theorem exists_fixedDensity_spectrum_mean_zero (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) {m : ℕ} (hm1 : 1 ≤ m) :
    ∃ (N : ℕ) (T : Spectrum N), T.nu 0 = 0 ∧
      ∀ j ≤ 2 * m, ∑ i, T.e i ^ 2 * T.lam i ^ j = densityKMoment hW D j := by
  obtain ⟨N, T, hmom⟩ := exists_fixedDensity_spectrum hW D hp m
  refine ⟨N, T, ?_, hmom⟩
  rw [Spectrum.nu]
  rw [hmom 1 (by omega), densityKMoment_one_eq_zero hW D hp]

end AlternatingCycle
