import Mathlib

/-!
# Integral-form graphon foundations

This file builds the relevant objects directly from a graphon defined as an **integral**,
over an abstract probability space — no operator model, no Hilbert space.

* `U : Ω → Ω → ℝ` is the (symmetric, `[0,1]`-valued) complement kernel `1 − W` (`IsGraphon`).
* `kernelOp U μ f x = ∫ y, U x y * f y` is the kernel form, `mean μ f = ∫ f`.
* `degree = kernelOp 1`, `edgeDensity = mean degree`, `degCentered = degree − edgeDensity` (the mean-zero degree part).
* `compress f = kernelOp f − mean (kernelOp f)` is the compression to the mean-zero subspace,
  `compressIter k = Aᵏ g`, and `specMoment j = ∫ g · compressIter j = ⟪g, Aʲ g⟫` are the spectral moments.

The key facts proved here — **with no Hilbert space and no operator-norm theory** — are:

* `kernelOp_symm` — the kernel form is symmetric (Fubini + symmetry of `U`);
* `compress_symm` — the compression is symmetric on mean-zero functions;
* `moment` — `∫ hᵢ · hⱼ = s_{i+j}` (the moment identity for the compression iterates);
* `sos1` — the degree-`1` sum-of-squares certificate in the `s_j` (the C₅ engine);
* `edge_deletion` — a representative edge-deletion bound.

These are the analytic foundations discharged from the integral definition.  The degree-`2`
SOS (for C₇) is in `MomentSOS.lean`; Lemma 2.4 in `PathDensity.lean`; the cyclic
inclusion–exclusion in `Kernel.lean`/`Cycle.lean`/`Necklace.lean`.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A graphon (here, the complement kernel `U = 1 − W`): symmetric, measurable, `[0,1]`-valued. -/
structure IsGraphon (U : Ω → Ω → ℝ) (μ : Measure Ω) : Prop where
  meas : Measurable (Function.uncurry U)
  nonneg : ∀ x y, 0 ≤ U x y
  le_one : ∀ x y, U x y ≤ 1
  symm : ∀ x y, U x y = U y x

private lemma abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans (le_of_eq (by rw [abs_neg]))

/-- Bounded, strongly measurable real functions: the working space. -/
structure Good (f : Ω → ℝ) : Prop where
  meas : StronglyMeasurable f
  bdd : ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C

lemma Good.integrable {f : Ω → ℝ} (hf : Good f) : Integrable f μ := by
  obtain ⟨C, _, hC⟩ := hf.bdd
  refine (integrable_const C).mono' hf.meas.aestronglyMeasurable (ae_of_all _ ?_)
  intro x; simpa [Real.norm_eq_abs] using hC x

lemma Good.mul {f k : Ω → ℝ} (hf : Good f) (hk : Good k) : Good (fun x => f x * k x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Ck, hCk0, hCk⟩ := hk.bdd
  refine ⟨hf.meas.mul hk.meas, ⟨Cf * Ck, mul_nonneg hCf0 hCk0, fun x => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hCf x) (hCk x) (abs_nonneg _) hCf0

variable {U : Ω → Ω → ℝ}

/-- The kernel form `kernelOp U f x = ∫ y, U x y * f y`. -/
noncomputable def kernelOp (U : Ω → Ω → ℝ) (μ : Measure Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => ∫ y, U x y * f y ∂μ

/-- The mean of a function. -/
noncomputable def mean (μ : Measure Ω) (f : Ω → ℝ) : ℝ := ∫ x, f x ∂μ

lemma mean_const (c : ℝ) : mean μ (fun _ => c) = c := by simp [mean]

lemma good_kernelOp (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) : Good (kernelOp U μ f) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨?_, ⟨C, hC0, fun x => ?_⟩⟩
  · have hSM : StronglyMeasurable (fun p : Ω × Ω => U p.1 p.2 * f p.2) :=
      (hU.meas.stronglyMeasurable).mul (hf.meas.comp_measurable measurable_snd)
    exact hSM.integral_prod_right'
  · have hmx : Measurable (fun y => U x y) := hU.meas.comp measurable_prodMk_left
    have hint : Integrable (fun y => U x y * f y) μ :=
      (Good.mul ⟨hmx.stronglyMeasurable, ⟨1, zero_le_one, fun y => by
        rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y⟩⟩ hf).integrable
    calc |kernelOp U μ f x| ≤ ∫ y, |U x y * f y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _y, C ∂μ := by
          refine integral_mono hint.abs (integrable_const C) (fun y => ?_)
          rw [abs_mul, abs_of_nonneg (hU.nonneg x y)]
          calc U x y * |f y| ≤ 1 * |f y| :=
                mul_le_mul_of_nonneg_right (hU.le_one x y) (abs_nonneg _)
            _ = |f y| := one_mul _
            _ ≤ C := hC y
      _ = C := by simp

/-- The degree function `degree = kernelOp 1`. -/
noncomputable def degree (U : Ω → Ω → ℝ) (μ : Measure Ω) : Ω → ℝ := fun x => ∫ y, U x y ∂μ

/-- The edge density of `U`, `edgeDensity = mean degree`. -/
noncomputable def edgeDensity (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℝ := mean μ (degree U μ)

/-- The mean-zero degree part `degCentered = degree − edgeDensity`. -/
noncomputable def degCentered (U : Ω → Ω → ℝ) (μ : Measure Ω) : Ω → ℝ :=
  fun x => degree U μ x - edgeDensity U μ

/-- The compression `compress f = kernelOp f − mean (kernelOp f)`. -/
noncomputable def compress (U : Ω → Ω → ℝ) (μ : Measure Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => kernelOp U μ f x - mean μ (kernelOp U μ f)

/-- The iterated functions `compressIter k = Aᵏ g`. -/
noncomputable def compressIter (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℕ → (Ω → ℝ)
  | 0 => degCentered U μ
  | (n + 1) => compress U μ (compressIter U μ n)

/-- The spectral moments `specMoment j = ∫ g · (Aʲ g)`. -/
noncomputable def specMoment (U : Ω → Ω → ℝ) (μ : Measure Ω) (j : ℕ) : ℝ :=
  ∫ x, degCentered U μ x * compressIter U μ j x ∂μ

lemma good_degree (hU : IsGraphon U μ) : Good (degree U μ) := by
  have h : degree U μ = kernelOp U μ (fun _ => 1) := by funext x; simp [degree, kernelOp]
  rw [h]; exact good_kernelOp hU ⟨stronglyMeasurable_const, ⟨1, zero_le_one, fun _ => by norm_num⟩⟩

lemma good_degCentered (hU : IsGraphon U μ) : Good (degCentered U μ) := by
  obtain ⟨C, hC0, hC⟩ := (good_degree hU).bdd
  refine ⟨(good_degree hU).meas.sub stronglyMeasurable_const,
    ⟨C + |edgeDensity U μ|, add_nonneg hC0 (abs_nonneg _), fun x => ?_⟩⟩
  exact (abs_sub_le' _ _).trans (by linarith [hC x])

lemma good_compress (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) : Good (compress U μ f) := by
  obtain ⟨C, hC0, hC⟩ := (good_kernelOp hU hf).bdd
  refine ⟨(good_kernelOp hU hf).meas.sub stronglyMeasurable_const,
    ⟨C + |mean μ (kernelOp U μ f)|, add_nonneg hC0 (abs_nonneg _), fun x => ?_⟩⟩
  exact (abs_sub_le' _ _).trans (by linarith [hC x])

lemma good_compressIter (hU : IsGraphon U μ) : ∀ k, Good (compressIter U μ k)
  | 0 => good_degCentered hU
  | (k + 1) => good_compress hU (good_compressIter hU k)

/-- `mean (compressIter k) = 0` for every `k`. -/
lemma mean_compressIter (hU : IsGraphon U μ) : ∀ k, mean μ (compressIter U μ k) = 0
  | 0 => by
      show ∫ x, degCentered U μ x ∂μ = 0
      simp only [degCentered]
      rw [integral_sub (good_degree hU).integrable (integrable_const _)]
      show mean μ (degree U μ) - mean μ (fun _ => edgeDensity U μ) = 0
      rw [mean_const, edgeDensity]; ring
  | (k + 1) => by
      show ∫ x, compress U μ (compressIter U μ k) x ∂μ = 0
      simp only [compress]
      rw [integral_sub (good_kernelOp hU (good_compressIter hU k)).integrable (integrable_const _)]
      show mean μ (kernelOp U μ (compressIter U μ k)) - mean μ (fun _ => mean μ (kernelOp U μ (compressIter U μ k))) = 0
      rw [mean_const]; ring

/-- **Symmetry of the kernel form** (Fubini + symmetry of `U`). -/
lemma kernelOp_symm (hU : IsGraphon U μ) {f k : Ω → ℝ} (hf : Good f) (hk : Good k) :
    ∫ x, kernelOp U μ f x * k x ∂μ = ∫ x, f x * kernelOp U μ k x ∂μ := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Ck, hCk0, hCk⟩ := hk.bdd
  have hSM : StronglyMeasurable (Function.uncurry fun x y => U x y * f y * k x) := by
    have h1 : StronglyMeasurable (fun p : Ω × Ω => U p.1 p.2) := hU.meas.stronglyMeasurable
    have h2 : StronglyMeasurable (fun p : Ω × Ω => f p.2) := hf.meas.comp_measurable measurable_snd
    have h3 : StronglyMeasurable (fun p : Ω × Ω => k p.1) := hk.meas.comp_measurable measurable_fst
    exact (h1.mul h2).mul h3
  have hInt : Integrable (Function.uncurry fun x y => U x y * f y * k x) (μ.prod μ) := by
    refine (integrable_const (1 * Cf * Ck)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨x, y⟩
    simp only [Function.uncurry, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (hU.nonneg x y)]
    refine mul_le_mul (mul_le_mul (hU.le_one x y) (hCf y) (abs_nonneg _) (by norm_num)) (hCk x)
      (abs_nonneg _) (mul_nonneg zero_le_one hCf0)
  have hL : ∀ x, kernelOp U μ f x * k x = ∫ y, U x y * f y * k x ∂μ := fun x => by
    rw [kernelOp, integral_mul_const]
  have hR : ∀ y, f y * kernelOp U μ k y = ∫ x, U x y * f y * k x ∂μ := fun y => by
    rw [kernelOp, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show f y * (U y x * k x) = U x y * f y * k x
    rw [hU.symm y x]; ring
  calc ∫ x, kernelOp U μ f x * k x ∂μ
      = ∫ x, ∫ y, U x y * f y * k x ∂μ ∂μ := by simp_rw [hL]
    _ = ∫ y, ∫ x, U x y * f y * k x ∂μ ∂μ := integral_integral_swap hInt
    _ = ∫ y, f y * kernelOp U μ k y ∂μ := by simp_rw [hR]

/-- **Symmetry of the compression** on mean-zero functions. -/
lemma compress_symm (hU : IsGraphon U μ) {f k : Ω → ℝ} (hf : Good f) (hk : Good k)
    (hf0 : mean μ f = 0) (hk0 : mean μ k = 0) :
    ∫ x, compress U μ f x * k x ∂μ = ∫ x, f x * compress U μ k x ∂μ := by
  have e1 : ∫ x, compress U μ f x * k x ∂μ = ∫ x, kernelOp U μ f x * k x ∂μ := by
    have h1 : Integrable (fun x => kernelOp U μ f x * k x) μ := ((good_kernelOp hU hf).mul hk).integrable
    have h2 : Integrable (fun x => mean μ (kernelOp U μ f) * k x) μ := hk.integrable.const_mul _
    calc ∫ x, compress U μ f x * k x ∂μ
        = ∫ x, (kernelOp U μ f x * k x - mean μ (kernelOp U μ f) * k x) ∂μ := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_); simp only [compress]; ring
      _ = (∫ x, kernelOp U μ f x * k x ∂μ) - mean μ (kernelOp U μ f) * ∫ x, k x ∂μ := by
            rw [integral_sub h1 h2, integral_const_mul]
      _ = ∫ x, kernelOp U μ f x * k x ∂μ := by
            have hk0' : ∫ x, k x ∂μ = 0 := hk0
            rw [hk0']; ring
  have e2 : ∫ x, f x * compress U μ k x ∂μ = ∫ x, f x * kernelOp U μ k x ∂μ := by
    have h1 : Integrable (fun x => f x * kernelOp U μ k x) μ := (hf.mul (good_kernelOp hU hk)).integrable
    have h2 : Integrable (fun x => f x * mean μ (kernelOp U μ k)) μ := hf.integrable.mul_const _
    calc ∫ x, f x * compress U μ k x ∂μ
        = ∫ x, (f x * kernelOp U μ k x - f x * mean μ (kernelOp U μ k)) ∂μ := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_); simp only [compress]; ring
      _ = (∫ x, f x * kernelOp U μ k x ∂μ) - (∫ x, f x ∂μ) * mean μ (kernelOp U μ k) := by
            rw [integral_sub h1 h2, integral_mul_const]
      _ = ∫ x, f x * kernelOp U μ k x ∂μ := by
            have hf0' : ∫ x, f x ∂μ = 0 := hf0
            rw [hf0']; ring
  rw [e1, e2, kernelOp_symm hU hf hk]

/-- **Moment identity** `∫ hᵢ · hⱼ = s_{i+j}` for the compression iterates `hₖ = Aᵏg`. -/
lemma moment (hU : IsGraphon U μ) : ∀ (j i : ℕ),
    ∫ x, compressIter U μ i x * compressIter U μ j x ∂μ = specMoment U μ (i + j) := by
  intro j
  induction j with
  | zero =>
      intro i
      rw [Nat.add_zero]
      show ∫ x, compressIter U μ i x * degCentered U μ x ∂μ = ∫ x, degCentered U μ x * compressIter U μ i x ∂μ
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      ring
  | succ n ih =>
      intro i
      have key : ∫ x, compressIter U μ i x * compressIter U μ (n + 1) x ∂μ
          = ∫ x, compressIter U μ (i + 1) x * compressIter U μ n x ∂μ := by
        show ∫ x, compressIter U μ i x * compress U μ (compressIter U μ n) x ∂μ
            = ∫ x, compress U μ (compressIter U μ i) x * compressIter U μ n x ∂μ
        exact (compress_symm hU (good_compressIter hU i) (good_compressIter hU n) (mean_compressIter hU i) (mean_compressIter hU n)).symm
      rw [key, ih (i + 1)]
      congr 1; omega

/-- **Degree-1 sum-of-squares certificate** (the C₅ engine), proved as `∫ (square) ≥ 0`. -/
lemma sos1 (hU : IsGraphon U μ) (c1 c0 : ℝ) :
    0 ≤ c1 ^ 2 * specMoment U μ 2 + 2 * c1 * c0 * specMoment U μ 1 + c0 ^ 2 * specMoment U μ 0 := by
  have hnn : 0 ≤ ∫ x, (c1 * compressIter U μ 1 x + c0 * compressIter U μ 0 x) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have m11 := moment hU 1 1
  have m10 := moment hU 0 1
  have m00 := moment hU 0 0
  have hi11 : Integrable (fun x => compressIter U μ 1 x * compressIter U μ 1 x) μ :=
    ((good_compressIter hU 1).mul (good_compressIter hU 1)).integrable
  have hi10 : Integrable (fun x => compressIter U μ 1 x * compressIter U μ 0 x) μ :=
    ((good_compressIter hU 1).mul (good_compressIter hU 0)).integrable
  have hi00 : Integrable (fun x => compressIter U μ 0 x * compressIter U μ 0 x) μ :=
    ((good_compressIter hU 0).mul (good_compressIter hU 0)).integrable
  have hA : Integrable (fun x => c1 ^ 2 * (compressIter U μ 1 x * compressIter U μ 1 x)) μ := hi11.const_mul _
  have hB : Integrable (fun x => 2 * c1 * c0 * (compressIter U μ 1 x * compressIter U μ 0 x)) μ := hi10.const_mul _
  have hC : Integrable (fun x => c0 ^ 2 * (compressIter U μ 0 x * compressIter U μ 0 x)) μ := hi00.const_mul _
  have hAB : Integrable (fun x => c1 ^ 2 * (compressIter U μ 1 x * compressIter U μ 1 x)
      + 2 * c1 * c0 * (compressIter U μ 1 x * compressIter U μ 0 x)) μ := hA.add hB
  have hexp : ∫ x, (c1 * compressIter U μ 1 x + c0 * compressIter U μ 0 x) ^ 2 ∂μ
      = c1 ^ 2 * specMoment U μ 2 + 2 * c1 * c0 * specMoment U μ 1 + c0 ^ 2 * specMoment U μ 0 := by
    calc ∫ x, (c1 * compressIter U μ 1 x + c0 * compressIter U μ 0 x) ^ 2 ∂μ
        = ∫ x, (c1 ^ 2 * (compressIter U μ 1 x * compressIter U μ 1 x)
              + 2 * c1 * c0 * (compressIter U μ 1 x * compressIter U μ 0 x)
              + c0 ^ 2 * (compressIter U μ 0 x * compressIter U μ 0 x)) ∂μ := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_); ring
      _ = c1 ^ 2 * (∫ x, compressIter U μ 1 x * compressIter U μ 1 x ∂μ)
            + 2 * c1 * c0 * (∫ x, compressIter U μ 1 x * compressIter U μ 0 x ∂μ)
            + c0 ^ 2 * (∫ x, compressIter U μ 0 x * compressIter U μ 0 x ∂μ) := by
            rw [integral_add hAB hC, integral_add hA hB,
                integral_const_mul, integral_const_mul, integral_const_mul]
      _ = c1 ^ 2 * specMoment U μ 2 + 2 * c1 * c0 * specMoment U μ 1 + c0 ^ 2 * specMoment U μ 0 := by
            rw [m11, m10, m00]
  rw [hexp] at hnn; exact hnn

/-- **Edge-deletion (representative case).**  With `0 ≤ U ≤ 1`, dropping a closing factor
`U y x ∈ [0,1]` only increases the (nonnegative) integrand: the `2`-cycle density is at most
the single-edge density.  This is the integral form of `c_m ≤ x_{m-1}`. -/
lemma edge_deletion (hU : IsGraphon U μ) :
    ∫ p : Ω × Ω, U p.1 p.2 * U p.2 p.1 ∂(μ.prod μ)
      ≤ ∫ p : Ω × Ω, U p.1 p.2 ∂(μ.prod μ) := by
  have hSM1 : StronglyMeasurable (fun p : Ω × Ω => U p.1 p.2 * U p.2 p.1) :=
    hU.meas.stronglyMeasurable.mul (hU.meas.comp measurable_swap).stronglyMeasurable
  have hSM2 : StronglyMeasurable (fun p : Ω × Ω => U p.1 p.2) := hU.meas.stronglyMeasurable
  have hi1 : Integrable (fun p : Ω × Ω => U p.1 p.2 * U p.2 p.1) (μ.prod μ) :=
    (integrable_const 1).mono' hSM1.aestronglyMeasurable (ae_of_all _ fun p => by
      simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_of_nonneg (hU.nonneg _ _), abs_of_nonneg (hU.nonneg _ _)]
      nlinarith [hU.nonneg p.1 p.2, hU.le_one p.1 p.2, hU.nonneg p.2 p.1, hU.le_one p.2 p.1])
  have hi2 : Integrable (fun p : Ω × Ω => U p.1 p.2) (μ.prod μ) :=
    (integrable_const 1).mono' hSM2.aestronglyMeasurable (ae_of_all _ fun p => by
      simp only [Real.norm_eq_abs]; rw [abs_of_nonneg (hU.nonneg _ _)]; exact hU.le_one _ _)
  refine integral_mono hi1 hi2 (fun p => ?_)
  calc U p.1 p.2 * U p.2 p.1 ≤ U p.1 p.2 * 1 :=
        mul_le_mul_of_nonneg_left (hU.le_one _ _) (hU.nonneg _ _)
    _ = U p.1 p.2 := mul_one _

end OddCycleBound
