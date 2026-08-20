import AlternatingCycle.Foundation.Graphon

/-!
# Path densities and Lemma 2.4 (integral form)

Building on `Graphon.lean`, we define the path homomorphism densities `x_j = t(P_j, U)` as the
nested integral `pathDensity j = mean (kernelOpʲ 1)` and prove the **path-density formulae of Lemma 2.4**
(`x₂ = q² + s₀`, `x₃ = q³ + 2q s₀ + s₁`, `x₄ = q⁴ + 3q² s₀ + 2q s₁ + s₀² + s₂`) entirely from
the integral definitions, so Lemma 2.4 leaves the *trusted* list.

Engine: the key identity `kernelOp (hₖ) = sₖ·1 + h_{k+1}`, pointwise `kernelOp`-linearity, and the
decomposition `pathIter n = xₙ·1 + (mean-zero combination of the hₖ)`, from which `xₙ` is read
off by taking `mean` (the mean-zero part drops out).
-/

open MeasureTheory

-- A few lemmas do not use the section variable `[IsProbabilityMeasure μ]`; keep the declarations uniform.
set_option linter.unusedSectionVars false

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- The constant function `1` is `Good`. -/
lemma good_one : Good (fun _ : Ω => (1 : ℝ)) :=
  ⟨stronglyMeasurable_const, ⟨1, zero_le_one, fun _ => by norm_num⟩⟩

lemma good_smul (c : ℝ) {f : Ω → ℝ} (hf : Good f) : Good (c • f) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨hf.meas.const_smul c, ⟨|c| * C, mul_nonneg (abs_nonneg _) hC0, fun x => ?_⟩⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

lemma good_add {f g : Ω → ℝ} (hf : Good f) (hg : Good g) : Good (f + g) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bdd
  refine ⟨hf.meas.add hg.meas, ⟨Cf + Cg, by linarith, fun x => ?_⟩⟩
  rw [Pi.add_apply]
  exact (abs_add_le _ _).trans (by linarith [hCf x, hCg x])

/-- Integrability of `y ↦ U x y * f y` for `Good f`. -/
lemma integrable_Uf (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) (x : Ω) :
    Integrable (fun y => U x y * f y) μ := by
  have hmx : Measurable (fun y => U x y) := hU.meas.comp measurable_prodMk_left
  exact (Good.mul ⟨hmx.stronglyMeasurable, ⟨1, zero_le_one, fun y => by
    rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y⟩⟩ hf).integrable

lemma kernelOp_one (_hU : IsGraphon U μ) : kernelOp U μ (fun _ => 1) = degree U μ := by
  funext x; simp [kernelOp, degree]

lemma degree_eq (x : Ω) : degree U μ x = edgeDensity U μ + degCentered U μ x := by simp [degCentered]

lemma compressIter_zero : compressIter U μ 0 = degCentered U μ := rfl

lemma degree_eq' (x : Ω) : degree U μ x = edgeDensity U μ + compressIter U μ 0 x := by rw [degree_eq, compressIter_zero]

/-- Pointwise additivity of `kernelOp` on `Good` functions. -/
lemma kernelOp_add' (hU : IsGraphon U μ) {f g : Ω → ℝ} (hf : Good f) (hg : Good g) (x : Ω) :
    kernelOp U μ (f + g) x = kernelOp U μ f x + kernelOp U μ g x := by
  simp only [kernelOp, Pi.add_apply]
  rw [← integral_add (integrable_Uf hU hf x) (integrable_Uf hU hg x)]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/-- Pointwise homogeneity of `kernelOp`. -/
lemma kernelOp_smul' (c : ℝ) (f : Ω → ℝ) (x : Ω) : kernelOp U μ (c • f) x = c * kernelOp U μ f x := by
  simp only [kernelOp, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/-- `mean (kernelOp (hₖ)) = sₖ`. -/
lemma mean_kernelOp_compressIter (hU : IsGraphon U μ) (k : ℕ) :
    mean μ (kernelOp U μ (compressIter U μ k)) = specMoment U μ k := by
  have h1 : mean μ (kernelOp U μ (compressIter U μ k)) = ∫ x, kernelOp U μ (compressIter U μ k) x * 1 ∂μ := by simp [mean]
  rw [h1, kernelOp_symm hU (good_compressIter hU k) good_one, kernelOp_one hU]
  have hcongr : ∀ x, compressIter U μ k x * degree U μ x
      = edgeDensity U μ * compressIter U μ k x + degCentered U μ x * compressIter U μ k x := fun x => by rw [degree_eq]; ring
  rw [integral_congr_ae (ae_of_all _ hcongr),
    integral_add ((good_compressIter hU k).integrable.const_mul _) ((good_degCentered hU).mul (good_compressIter hU k)).integrable,
    integral_const_mul]
  have : ∫ x, compressIter U μ k x ∂μ = 0 := mean_compressIter hU k
  rw [this, mul_zero, zero_add]
  rfl

/-- **The key recursion** `kernelOp (hₖ) = sₖ·1 + h_{k+1}`. -/
lemma kernelOp_compressIter (hU : IsGraphon U μ) (k : ℕ) :
    kernelOp U μ (compressIter U μ k) = fun x => specMoment U μ k + compressIter U μ (k + 1) x := by
  funext x
  have hdef : compressIter U μ (k + 1) x = kernelOp U μ (compressIter U μ k) x - mean μ (kernelOp U μ (compressIter U μ k)) := by
    simp only [compressIter, compress]
  rw [mean_kernelOp_compressIter hU k] at hdef
  linarith [hdef]

lemma kernelOp_compressIter' (hU : IsGraphon U μ) (k : ℕ) (x : Ω) :
    kernelOp U μ (compressIter U μ k) x = specMoment U μ k + compressIter U μ (k + 1) x := congrFun (kernelOp_compressIter hU k) x

/-- Path-density iterate `pathIter j = kernelOpʲ 1`. -/
noncomputable def pathIter (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℕ → (Ω → ℝ)
  | 0 => fun _ => 1
  | (k + 1) => kernelOp U μ (pathIter U μ k)

/-- The path density `x_j = t(P_j, U) = mean (kernelOpʲ 1)`. -/
noncomputable def pathDensity (U : Ω → Ω → ℝ) (μ : Measure Ω) (j : ℕ) : ℝ := mean μ (pathIter U μ j)

/-! ### `mean` is linear; constants and `hₖ` evaluate cleanly. -/

lemma mean_one : mean μ (fun _ : Ω => (1:ℝ)) = 1 := mean_const 1

lemma mean_smul (c : ℝ) (f : Ω → ℝ) : mean μ (c • f) = c * mean μ f := by
  simp only [mean, Pi.smul_apply, smul_eq_mul]; rw [integral_const_mul]

lemma mean_add {f g : Ω → ℝ} (hf : Good f) (hg : Good g) :
    mean μ (f + g) = mean μ f + mean μ g := by
  simp only [mean, Pi.add_apply]; exact integral_add hf.integrable hg.integrable

/-- For a constant times `1` plus a mean-zero `Good` function, the mean is the constant. -/
lemma mean_const_add (C : ℝ) {w : Ω → ℝ} (hw : Good w) (hw0 : mean μ w = 0) :
    mean μ (C • (fun _ : Ω => (1:ℝ)) + w) = C := by
  rw [mean_add (good_smul C good_one) hw, mean_smul, mean_one, hw0]; ring

/-! ### Decompositions `pathIter k = xₖ·1 + (mean-zero combination of hₖ)` -/

lemma decomp1 (hU : IsGraphon U μ) :
    pathIter U μ 1 = edgeDensity U μ • (fun _ : Ω => (1:ℝ)) + compressIter U μ 0 := by
  have h1 : pathIter U μ 1 = degree U μ := by
    show kernelOp U μ (fun _ => 1) = degree U μ; exact kernelOp_one hU
  rw [h1]; funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  exact degree_eq' x

lemma decomp2 (hU : IsGraphon U μ) :
    pathIter U μ 2 = (edgeDensity U μ ^ 2 + specMoment U μ 0) • (fun _ : Ω => (1:ℝ))
      + (edgeDensity U μ • compressIter U μ 0 + compressIter U μ 1) := by
  funext x
  show kernelOp U μ (pathIter U μ 1) x = _
  rw [decomp1 hU, kernelOp_add' hU (good_smul _ good_one) (good_compressIter hU 0), kernelOp_smul', kernelOp_one hU, kernelOp_compressIter' hU 0,
    degree_eq']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma decomp3 (hU : IsGraphon U μ) :
    pathIter U μ 3 = (edgeDensity U μ ^ 3 + 2 * edgeDensity U μ * specMoment U μ 0 + specMoment U μ 1) • (fun _ : Ω => (1:ℝ))
      + ((edgeDensity U μ ^ 2 + specMoment U μ 0) • compressIter U μ 0 + (edgeDensity U μ • compressIter U μ 1 + compressIter U μ 2)) := by
  funext x
  show kernelOp U μ (pathIter U μ 2) x = _
  rw [decomp2 hU,
    kernelOp_add' hU (good_smul _ good_one) (good_add (good_smul _ (good_compressIter hU 0)) (good_compressIter hU 1)),
    kernelOp_smul', kernelOp_one hU,
    kernelOp_add' hU (good_smul _ (good_compressIter hU 0)) (good_compressIter hU 1), kernelOp_smul', kernelOp_compressIter' hU 0, kernelOp_compressIter' hU 1,
    degree_eq']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma decomp4 (hU : IsGraphon U μ) :
    pathIter U μ 4 = (edgeDensity U μ ^ 4 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 0 + 2 * edgeDensity U μ * specMoment U μ 1
        + specMoment U μ 0 ^ 2 + specMoment U μ 2) • (fun _ : Ω => (1:ℝ))
      + ((edgeDensity U μ ^ 3 + 2 * edgeDensity U μ * specMoment U μ 0 + specMoment U μ 1) • compressIter U μ 0
          + ((edgeDensity U μ ^ 2 + specMoment U μ 0) • compressIter U μ 1 + (edgeDensity U μ • compressIter U μ 2 + compressIter U μ 3))) := by
  funext x
  show kernelOp U μ (pathIter U μ 3) x = _
  rw [decomp3 hU,
    kernelOp_add' hU (good_smul _ good_one)
      (good_add (good_smul _ (good_compressIter hU 0)) (good_add (good_smul _ (good_compressIter hU 1)) (good_compressIter hU 2))),
    kernelOp_smul', kernelOp_one hU,
    kernelOp_add' hU (good_smul _ (good_compressIter hU 0)) (good_add (good_smul _ (good_compressIter hU 1)) (good_compressIter hU 2)),
    kernelOp_smul',
    kernelOp_add' hU (good_smul _ (good_compressIter hU 1)) (good_compressIter hU 2), kernelOp_smul',
    kernelOp_compressIter' hU 0, kernelOp_compressIter' hU 1, kernelOp_compressIter' hU 2, degree_eq']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Lemma 2.4 for `x₂, x₃, x₄` (read off by taking `mean`) -/

lemma pathDensity_two (hU : IsGraphon U μ) : pathDensity U μ 2 = edgeDensity U μ ^ 2 + specMoment U μ 0 := by
  rw [pathDensity, decomp2 hU]
  refine mean_const_add _ (good_add (good_smul _ (good_compressIter hU 0)) (good_compressIter hU 1)) ?_
  rw [mean_add (good_smul _ (good_compressIter hU 0)) (good_compressIter hU 1), mean_smul, mean_compressIter hU, mean_compressIter hU]
  ring

lemma pathDensity_three (hU : IsGraphon U μ) :
    pathDensity U μ 3 = edgeDensity U μ ^ 3 + 2 * edgeDensity U μ * specMoment U μ 0 + specMoment U μ 1 := by
  rw [pathDensity, decomp3 hU]
  refine mean_const_add _
    (good_add (good_smul _ (good_compressIter hU 0)) (good_add (good_smul _ (good_compressIter hU 1)) (good_compressIter hU 2))) ?_
  rw [mean_add (good_smul _ (good_compressIter hU 0)) (good_add (good_smul _ (good_compressIter hU 1)) (good_compressIter hU 2)),
    mean_add (good_smul _ (good_compressIter hU 1)) (good_compressIter hU 2),
    mean_smul, mean_smul, mean_compressIter hU, mean_compressIter hU, mean_compressIter hU]
  ring

lemma pathDensity_four (hU : IsGraphon U μ) :
    pathDensity U μ 4 = edgeDensity U μ ^ 4 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 0 + 2 * edgeDensity U μ * specMoment U μ 1
      + specMoment U μ 0 ^ 2 + specMoment U μ 2 := by
  rw [pathDensity, decomp4 hU]
  refine mean_const_add _
    (good_add (good_smul _ (good_compressIter hU 0))
      (good_add (good_smul _ (good_compressIter hU 1)) (good_add (good_smul _ (good_compressIter hU 2)) (good_compressIter hU 3)))) ?_
  rw [mean_add (good_smul _ (good_compressIter hU 0))
        (good_add (good_smul _ (good_compressIter hU 1)) (good_add (good_smul _ (good_compressIter hU 2)) (good_compressIter hU 3))),
    mean_add (good_smul _ (good_compressIter hU 1)) (good_add (good_smul _ (good_compressIter hU 2)) (good_compressIter hU 3)),
    mean_add (good_smul _ (good_compressIter hU 2)) (good_compressIter hU 3),
    mean_smul, mean_smul, mean_smul, mean_compressIter hU, mean_compressIter hU, mean_compressIter hU, mean_compressIter hU]
  ring

/-! ### `x₅, x₆` (needed for C₇) -/

/-- Abbreviation for the `Good`ness of the degree-`≤3` `hₖ`-combination in `decomp4`. -/
private lemma good_combo4 (hU : IsGraphon U μ) :
    Good ((edgeDensity U μ ^ 3 + 2 * edgeDensity U μ * specMoment U μ 0 + specMoment U μ 1) • compressIter U μ 0
      + ((edgeDensity U μ ^ 2 + specMoment U μ 0) • compressIter U μ 1 + (edgeDensity U μ • compressIter U μ 2 + compressIter U μ 3))) :=
  good_add (good_smul _ (good_compressIter hU 0))
    (good_add (good_smul _ (good_compressIter hU 1)) (good_add (good_smul _ (good_compressIter hU 2)) (good_compressIter hU 3)))

lemma decomp5 (hU : IsGraphon U μ) :
    pathIter U μ 5 = (edgeDensity U μ ^ 5 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 0 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 1
        + 3 * edgeDensity U μ * specMoment U μ 0 ^ 2 + 2 * edgeDensity U μ * specMoment U μ 2 + 2 * specMoment U μ 0 * specMoment U μ 1
        + specMoment U μ 3) • (fun _ : Ω => (1:ℝ))
      + ((edgeDensity U μ ^ 4 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 0 + 2 * edgeDensity U μ * specMoment U μ 1
            + specMoment U μ 0 ^ 2 + specMoment U μ 2) • compressIter U μ 0
        + ((edgeDensity U μ ^ 3 + 2 * edgeDensity U μ * specMoment U μ 0 + specMoment U μ 1) • compressIter U μ 1
          + ((edgeDensity U μ ^ 2 + specMoment U μ 0) • compressIter U μ 2 + (edgeDensity U μ • compressIter U μ 3 + compressIter U μ 4)))) := by
  funext x
  show kernelOp U μ (pathIter U μ 4) x = _
  rw [decomp4 hU,
    kernelOp_add' hU (good_smul _ good_one) (good_combo4 hU), kernelOp_smul', kernelOp_one hU,
    kernelOp_add' hU (good_smul _ (good_compressIter hU 0))
      (good_add (good_smul _ (good_compressIter hU 1)) (good_add (good_smul _ (good_compressIter hU 2)) (good_compressIter hU 3))),
    kernelOp_smul',
    kernelOp_add' hU (good_smul _ (good_compressIter hU 1)) (good_add (good_smul _ (good_compressIter hU 2)) (good_compressIter hU 3)),
    kernelOp_smul',
    kernelOp_add' hU (good_smul _ (good_compressIter hU 2)) (good_compressIter hU 3), kernelOp_smul',
    kernelOp_compressIter' hU 0, kernelOp_compressIter' hU 1, kernelOp_compressIter' hU 2, kernelOp_compressIter' hU 3, degree_eq']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma good_combo5 (hU : IsGraphon U μ) :
    Good ((edgeDensity U μ ^ 4 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 0 + 2 * edgeDensity U μ * specMoment U μ 1
          + specMoment U μ 0 ^ 2 + specMoment U μ 2) • compressIter U μ 0
      + ((edgeDensity U μ ^ 3 + 2 * edgeDensity U μ * specMoment U μ 0 + specMoment U μ 1) • compressIter U μ 1
        + ((edgeDensity U μ ^ 2 + specMoment U μ 0) • compressIter U μ 2 + (edgeDensity U μ • compressIter U μ 3 + compressIter U μ 4)))) :=
  good_add (good_smul _ (good_compressIter hU 0))
    (good_add (good_smul _ (good_compressIter hU 1))
      (good_add (good_smul _ (good_compressIter hU 2)) (good_add (good_smul _ (good_compressIter hU 3)) (good_compressIter hU 4))))

lemma decomp6 (hU : IsGraphon U μ) :
    pathIter U μ 6 = (edgeDensity U μ ^ 6 + 5 * edgeDensity U μ ^ 4 * specMoment U μ 0 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 1
        + 6 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 2 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 2
        + 6 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 1 + 2 * edgeDensity U μ * specMoment U μ 3
        + specMoment U μ 0 ^ 3 + 2 * specMoment U μ 0 * specMoment U μ 2 + specMoment U μ 1 ^ 2 + specMoment U μ 4)
          • (fun _ : Ω => (1:ℝ))
      + ((edgeDensity U μ ^ 5 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 0 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 1
            + 3 * edgeDensity U μ * specMoment U μ 0 ^ 2 + 2 * edgeDensity U μ * specMoment U μ 2 + 2 * specMoment U μ 0 * specMoment U μ 1
            + specMoment U μ 3) • compressIter U μ 0
        + ((edgeDensity U μ ^ 4 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 0 + 2 * edgeDensity U μ * specMoment U μ 1
              + specMoment U μ 0 ^ 2 + specMoment U μ 2) • compressIter U μ 1
          + ((edgeDensity U μ ^ 3 + 2 * edgeDensity U μ * specMoment U μ 0 + specMoment U μ 1) • compressIter U μ 2
            + ((edgeDensity U μ ^ 2 + specMoment U μ 0) • compressIter U μ 3 + (edgeDensity U μ • compressIter U μ 4 + compressIter U μ 5))))) := by
  funext x
  show kernelOp U μ (pathIter U μ 5) x = _
  rw [decomp5 hU,
    kernelOp_add' hU (good_smul _ good_one) (good_combo5 hU), kernelOp_smul', kernelOp_one hU,
    kernelOp_add' hU (good_smul _ (good_compressIter hU 0))
      (good_add (good_smul _ (good_compressIter hU 1))
        (good_add (good_smul _ (good_compressIter hU 2)) (good_add (good_smul _ (good_compressIter hU 3)) (good_compressIter hU 4)))),
    kernelOp_smul',
    kernelOp_add' hU (good_smul _ (good_compressIter hU 1))
      (good_add (good_smul _ (good_compressIter hU 2)) (good_add (good_smul _ (good_compressIter hU 3)) (good_compressIter hU 4))),
    kernelOp_smul',
    kernelOp_add' hU (good_smul _ (good_compressIter hU 2)) (good_add (good_smul _ (good_compressIter hU 3)) (good_compressIter hU 4)),
    kernelOp_smul',
    kernelOp_add' hU (good_smul _ (good_compressIter hU 3)) (good_compressIter hU 4), kernelOp_smul',
    kernelOp_compressIter' hU 0, kernelOp_compressIter' hU 1, kernelOp_compressIter' hU 2, kernelOp_compressIter' hU 3, kernelOp_compressIter' hU 4, degree_eq']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma pathDensity_five (hU : IsGraphon U μ) :
    pathDensity U μ 5 = edgeDensity U μ ^ 5 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 0 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 1
      + 3 * edgeDensity U μ * specMoment U μ 0 ^ 2 + 2 * edgeDensity U μ * specMoment U μ 2 + 2 * specMoment U μ 0 * specMoment U μ 1
      + specMoment U μ 3 := by
  rw [pathDensity, decomp5 hU]
  refine mean_const_add _ (good_combo5 hU) ?_
  rw [mean_add (good_smul _ (good_compressIter hU 0))
        (good_add (good_smul _ (good_compressIter hU 1))
          (good_add (good_smul _ (good_compressIter hU 2)) (good_add (good_smul _ (good_compressIter hU 3)) (good_compressIter hU 4)))),
    mean_add (good_smul _ (good_compressIter hU 1))
      (good_add (good_smul _ (good_compressIter hU 2)) (good_add (good_smul _ (good_compressIter hU 3)) (good_compressIter hU 4))),
    mean_add (good_smul _ (good_compressIter hU 2)) (good_add (good_smul _ (good_compressIter hU 3)) (good_compressIter hU 4)),
    mean_add (good_smul _ (good_compressIter hU 3)) (good_compressIter hU 4),
    mean_smul, mean_smul, mean_smul, mean_smul,
    mean_compressIter hU, mean_compressIter hU, mean_compressIter hU, mean_compressIter hU, mean_compressIter hU]
  ring

lemma pathDensity_six (hU : IsGraphon U μ) :
    pathDensity U μ 6 = edgeDensity U μ ^ 6 + 5 * edgeDensity U μ ^ 4 * specMoment U μ 0 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 1
      + 6 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 2 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 2
      + 6 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 1 + 2 * edgeDensity U μ * specMoment U μ 3
      + specMoment U μ 0 ^ 3 + 2 * specMoment U μ 0 * specMoment U μ 2 + specMoment U μ 1 ^ 2 + specMoment U μ 4 := by
  rw [pathDensity, decomp6 hU]
  refine mean_const_add _
    (good_add (good_smul _ (good_compressIter hU 0))
      (good_add (good_smul _ (good_compressIter hU 1))
        (good_add (good_smul _ (good_compressIter hU 2))
          (good_add (good_smul _ (good_compressIter hU 3)) (good_add (good_smul _ (good_compressIter hU 4)) (good_compressIter hU 5)))))) ?_
  rw [mean_add (good_smul _ (good_compressIter hU 0))
        (good_add (good_smul _ (good_compressIter hU 1))
          (good_add (good_smul _ (good_compressIter hU 2))
            (good_add (good_smul _ (good_compressIter hU 3)) (good_add (good_smul _ (good_compressIter hU 4)) (good_compressIter hU 5))))),
    mean_add (good_smul _ (good_compressIter hU 1))
      (good_add (good_smul _ (good_compressIter hU 2))
        (good_add (good_smul _ (good_compressIter hU 3)) (good_add (good_smul _ (good_compressIter hU 4)) (good_compressIter hU 5)))),
    mean_add (good_smul _ (good_compressIter hU 2))
      (good_add (good_smul _ (good_compressIter hU 3)) (good_add (good_smul _ (good_compressIter hU 4)) (good_compressIter hU 5))),
    mean_add (good_smul _ (good_compressIter hU 3)) (good_add (good_smul _ (good_compressIter hU 4)) (good_compressIter hU 5)),
    mean_add (good_smul _ (good_compressIter hU 4)) (good_compressIter hU 5),
    mean_smul, mean_smul, mean_smul, mean_smul, mean_smul,
    mean_compressIter hU, mean_compressIter hU, mean_compressIter hU, mean_compressIter hU, mean_compressIter hU, mean_compressIter hU]
  ring

end OddCycleBound
