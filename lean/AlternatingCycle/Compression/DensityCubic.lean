import AlternatingCycle.Compression.DensityKrylov

/-!
# Cubic constraint for the normalized centered kernel

The red and blue normalized graphon kernels give two nonnegative triple products.  Their weighted
sum is exactly the complement of the cubic spectral head.
-/

open MeasureTheory OddCycleBound

set_option linter.unusedSectionVars false

noncomputable section

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

namespace GK

/-- Pointwise nonnegativity of a bounded kernel. -/
def Nonnegative (z : GK μ) : Prop := ∀ x y, 0 ≤ z.ker x y

lemma Nonnegative.smul {z : GK μ} (hz : z.Nonnegative) {c : ℝ} (hc : 0 ≤ c) :
    (c • z).Nonnegative := by
  intro x y
  exact mul_nonneg hc (hz x y)

lemma Nonnegative.mul {x y : GK μ} (hx : x.Nonnegative) (hy : y.Nonnegative) :
    (x * y).Nonnegative := by
  intro p q
  exact integral_nonneg fun z => mul_nonneg (hx p z) (hy z q)

lemma doubleMean_nonneg {z : GK μ} (hz : z.Nonnegative) : 0 ≤ doubleMean μ z.ker := by
  exact integral_nonneg fun x => integral_nonneg fun y => hz x y

end GK

namespace KAlg

/-- The constant-vector functional as a linear map. -/
noncomputable def phiL (μ : Measure Ω) [IsProbabilityMeasure μ] : KAlg μ →ₗ[ℝ] ℝ where
  toFun := phi μ
  map_add' x y := by
    rw [← tau_j_mul, ← tau_j_mul, ← tau_j_mul]
    simp only [mul_add, map_add]
  map_smul' c x := by
    rw [← tau_j_mul, ← tau_j_mul]
    simp only [mul_smul_comm, map_smul]
    rfl

@[simp] lemma phiL_apply (x : KAlg μ) : phiL μ x = phi μ x := rfl

@[simp] lemma phi_j : phi μ (j μ) = 1 := by
  rw [← tau_j_mul]
  simp [j, GK.ones_mul_ones, tau_apply, trace_onesKernel]

lemma j_mul_j : j μ * j μ = j μ := by
  rw [j, ← Unitization.inr_mul, GK.ones_mul_ones]

lemma phi_mul_j (x : KAlg μ) : phi μ (x * j μ) = phi μ x := by
  rw [← tau_j_mul, ← mul_assoc, j_mul_mul_j]
  simp [j, tau_apply, trace_onesKernel]

lemma phi_j_mul (x : KAlg μ) : phi μ (j μ * x) = phi μ x := by
  rw [← tau_j_mul, ← mul_assoc, j_mul_j]
  exact tau_j_mul x

lemma phi_inr_nonneg {z : GK μ} (hz : z.Nonnegative) :
    0 ≤ phi μ (Unitization.inr z) := by
  simpa [phi] using GK.doubleMean_nonneg hz

lemma phi_add (x y : KAlg μ) : phi μ (x + y) = phi μ x + phi μ y :=
  (phiL μ).map_add x y

lemma phi_neg (x : KAlg μ) : phi μ (-x) = -phi μ x :=
  (phiL μ).map_neg x

lemma phi_sub (x y : KAlg μ) : phi μ (x - y) = phi μ x - phi μ y :=
  (phiL μ).map_sub x y

lemma phi_smul (c : ℝ) (x : KAlg μ) : phi μ (c • x) = c * phi μ x := by
  change (phiL μ) (c • x) = c • (phiL μ) x
  exact (phiL μ).map_smul c x

lemma phi_j_mul_mul (x y : KAlg μ) : phi μ (j μ * x * y) = phi μ (x * y) := by
  rw [mul_assoc, phi_j_mul]

lemma phi_mul_j_mul_of_eq_zero (k : KAlg μ) (hk : phi μ k = 0) :
    phi μ (k * j μ * k) = 0 := by
  rw [← tau_j_mul]
  have hreassoc : j μ * (k * j μ * k) = (j μ * k * j μ) * k := by
    simp only [mul_assoc]
  rw [hreassoc, j_mul_mul_j, hk, zero_smul, zero_mul, map_zero]

lemma red_blue_red_expand (k : KAlg μ) (a b : ℝ) :
    (j μ + a • k) * (j μ - b • k) * (j μ + a • k) =
      j μ * j μ * j μ + a • (j μ * j μ * k) - b • (j μ * k * j μ)
        - (a * b) • (j μ * k * k) + a • (k * j μ * j μ)
        + a ^ 2 • (k * j μ * k) - (a * b) • (k * k * j μ)
        - (a ^ 2 * b) • (k * k * k) := by
  simp only [sub_eq_add_neg, mul_add, add_mul, mul_neg, neg_mul, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_neg, smul_smul]
  rw [mul_comm b a]
  noncomm_ring

lemma blue_red_blue_expand (k : KAlg μ) (a b : ℝ) :
    (j μ - b • k) * (j μ + a • k) * (j μ - b • k) =
      j μ * j μ * j μ - b • (j μ * j μ * k) + a • (j μ * k * j μ)
        - (a * b) • (j μ * k * k) - b • (k * j μ * j μ)
        + b ^ 2 • (k * j μ * k) - (a * b) • (k * k * j μ)
        + (a * b ^ 2) • (k * k * k) := by
  simp only [sub_eq_add_neg, mul_add, add_mul, mul_neg, neg_mul, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_neg, smul_smul]
  have hcoeff : b * (a * b) = a * (b * b) := by ring
  rw [mul_comm b a, hcoeff]
  noncomm_ring

lemma phi_red_blue_red (k : KAlg μ) (a b : ℝ) (hk : phi μ k = 0) (hab : a * b = 1) :
    phi μ ((j μ + a • k) * (j μ - b • k) * (j μ + a • k)) =
      1 - 2 * phi μ (k ^ 2) - a * phi μ (k ^ 3) := by
  rw [red_blue_red_expand]
  simp only [phi_add, phi_sub, phi_smul, phi_j_mul_mul, phi_j_mul, phi_mul_j, phi_j,
    phi_mul_j_mul_of_eq_zero k hk, hk, mul_zero, pow_succ, pow_zero, one_mul]
  have hcoeff : a * a * b = a := by rw [mul_assoc, hab, mul_one]
  rw [hab, hcoeff]
  ring

lemma phi_blue_red_blue (k : KAlg μ) (a b : ℝ) (hk : phi μ k = 0) (hab : a * b = 1) :
    phi μ ((j μ - b • k) * (j μ + a • k) * (j μ - b • k)) =
      1 - 2 * phi μ (k ^ 2) + b * phi μ (k ^ 3) := by
  rw [blue_red_blue_expand]
  simp only [phi_add, phi_sub, phi_smul, phi_j_mul_mul, phi_j_mul, phi_mul_j, phi_j,
    phi_mul_j_mul_of_eq_zero k hk, hk, mul_zero, pow_succ, pow_zero, one_mul]
  have hcoeff : a * (b * b) = b := by rw [← mul_assoc, hab, one_mul]
  rw [hab, hcoeff]
  ring

end KAlg

variable {W : Ω → Ω → ℝ}

lemma wElt_nonnegative (hW : IsGraphon W μ) : (wElt hW).Nonnegative := hW.nonneg

lemma uElt_nonnegative (hW : IsGraphon W μ) : (uElt hW).Nonnegative := by
  intro x y
  exact sub_nonneg.mpr (hW.le_one x y)

lemma density_red_triple_nonneg (hW : IsGraphon W μ) (D : DensityParams) :
    0 ≤ KAlg.phi μ
      ((KAlg.j μ + D.a • densityKU hW D) *
        (KAlg.j μ - D.b • densityKU hW D) *
        (KAlg.j μ + D.a • densityKU hW D)) := by
  let R : GK μ := D.p⁻¹ • wElt hW
  let B : GK μ := D.q⁻¹ • uElt hW
  have hR : R.Nonnegative :=
    (wElt_nonnegative hW).smul (inv_nonneg.mpr (le_of_lt D.p_pos))
  have hB : B.Nonnegative :=
    (uElt_nonnegative hW).smul (inv_nonneg.mpr (le_of_lt D.q_pos))
  rw [j_add_densityKU hW D, j_sub_densityKU hW D]
  change 0 ≤ KAlg.phi μ
    (Unitization.inr R * Unitization.inr B * Unitization.inr R)
  rw [← Unitization.inr_mul, ← Unitization.inr_mul]
  exact KAlg.phi_inr_nonneg (hR.mul hB |>.mul hR)

lemma density_blue_triple_nonneg (hW : IsGraphon W μ) (D : DensityParams) :
    0 ≤ KAlg.phi μ
      ((KAlg.j μ - D.b • densityKU hW D) *
        (KAlg.j μ + D.a • densityKU hW D) *
        (KAlg.j μ - D.b • densityKU hW D)) := by
  let R : GK μ := D.p⁻¹ • wElt hW
  let B : GK μ := D.q⁻¹ • uElt hW
  have hR : R.Nonnegative :=
    (wElt_nonnegative hW).smul (inv_nonneg.mpr (le_of_lt D.p_pos))
  have hB : B.Nonnegative :=
    (uElt_nonnegative hW).smul (inv_nonneg.mpr (le_of_lt D.q_pos))
  rw [j_sub_densityKU hW D, j_add_densityKU hW D]
  change 0 ≤ KAlg.phi μ
    (Unitization.inr B * Unitization.inr R * Unitization.inr B)
  rw [← Unitization.inr_mul, ← Unitization.inr_mul]
  exact KAlg.phi_inr_nonneg (hB.mul hR |>.mul hB)

/-- The normalized centered second and third moments satisfy the cubic head constraint. -/
theorem density_cubic_head_le_one (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) :
    2 * densityKMoment hW D 2 - D.delta * densityKMoment hW D 3 ≤ 1 := by
  let k := densityKU hW D
  have hk : KAlg.phi μ k = 0 := by
    simpa only [k, densityKMoment, pow_one] using densityKMoment_one_eq_zero hW D hp
  have hred := density_red_triple_nonneg hW D
  have hblue := density_blue_triple_nonneg hW D
  rw [KAlg.phi_red_blue_red k D.a D.b hk D.ab_eq] at hred
  rw [KAlg.phi_blue_red_blue k D.a D.b hk D.ab_eq] at hblue
  have hweighted :
      0 ≤ D.q * (1 - 2 * KAlg.phi μ (k ^ 2) - D.a * KAlg.phi μ (k ^ 3)) +
        D.p * (1 - 2 * KAlg.phi μ (k ^ 2) + D.b * KAlg.phi μ (k ^ 3)) :=
    add_nonneg (mul_nonneg (le_of_lt D.q_pos) hred)
      (mul_nonneg (le_of_lt D.p_pos) hblue)
  have hpq : D.p + D.q = 1 := by rw [D.q_eq]; ring
  have hpa : D.p * D.a = D.s := by
    rw [D.a_eq]
    field_simp [ne_of_gt D.p_pos]
  have hqb : D.q * D.b = D.s := by
    rw [D.b_eq]
    field_simp [ne_of_gt D.q_pos]
  have hdelta : D.p * D.b - D.q * D.a = D.delta := by
    calc
      D.p * D.b - D.q * D.a = (D.b - D.a) + (D.p * D.a - D.q * D.b) := by
        rw [D.q_eq]
        ring
      _ = D.b - D.a := by rw [hpa, hqb]; ring
      _ = D.delta := D.delta_eq.symm
  have hid :
      D.q * (1 - 2 * KAlg.phi μ (k ^ 2) - D.a * KAlg.phi μ (k ^ 3)) +
          D.p * (1 - 2 * KAlg.phi μ (k ^ 2) + D.b * KAlg.phi μ (k ^ 3)) =
        1 - (2 * KAlg.phi μ (k ^ 2) - D.delta * KAlg.phi μ (k ^ 3)) := by
    calc
      _ = (D.p + D.q) * (1 - 2 * KAlg.phi μ (k ^ 2)) +
          (D.p * D.b - D.q * D.a) * KAlg.phi μ (k ^ 3) := by ring
      _ = 1 * (1 - 2 * KAlg.phi μ (k ^ 2)) +
          D.delta * KAlg.phi μ (k ^ 3) := by rw [hpq, hdelta]
      _ = _ := by ring
  rw [hid] at hweighted
  change 2 * KAlg.phi μ (k ^ 2) - D.delta * KAlg.phi μ (k ^ 3) ≤ 1
  linarith

/-- A finite spectrum preserving the required moments and carrying the cubic head constraint. -/
theorem exists_fixedDensity_spectrum_cubic (hW : IsGraphon W μ) (D : DensityParams)
    (hp : edgeDensity W μ = D.p) {m : ℕ} (hm3 : 3 ≤ m) :
    ∃ (N : ℕ) (T : Spectrum N),
      T.nu 0 = 0 ∧
      2 * T.mu 1 - D.delta * T.nu 1 ≤ 1 ∧
      ∀ j ≤ 2 * m, ∑ i, T.e i ^ 2 * T.lam i ^ j = densityKMoment hW D j := by
  obtain ⟨N, T, hnu0, hmom⟩ :=
    exists_fixedDensity_spectrum_mean_zero hW D hp (by omega : 1 ≤ m)
  have hmu1 : T.mu 1 = densityKMoment hW D 2 := by
    simpa [Spectrum.mu] using hmom 2 (by omega)
  have hnu1 : T.nu 1 = densityKMoment hW D 3 := by
    simpa [Spectrum.nu] using hmom 3 (by omega)
  have hhead := density_cubic_head_le_one hW D hp
  rw [← hmu1, ← hnu1] at hhead
  exact ⟨N, T, hnu0, hhead, hmom⟩

end AlternatingCycle
