import AlternatingCycle.Necklace.Unitize
import AlternatingCycle.Necklace.Trace
import AlternatingCycle.Defs

/-!
# Fact A for kernels

In `KAlg μ` take `j = J` (the all-ones kernel), `k = 2W − 1`, `τ` the extended trace and
`μ_g = φ (k ^ g)`.  The three hypotheses of `Necklace/Trace.lean` are `KAlg.j_mul_mul_j`,
`KAlg.tau_mul_comm` and `KAlg.tau_j_mul`, all proved in `Necklace/Unitize.lean`, so Fact A
transfers with no further work:

```
  τ (((J + K)(J − K)) ^ m) + τ (K ^ (2m)) = ∑ c_{2m}(a,b) · μ_{a+b}          (m odd)
```

The right-hand side is the *same universal expression* as in `Necklace/MatrixInstance.lean`: the
coefficients `coeff alt` are defined once, in `Necklace/RankOne.lean`, from the sign pattern and
the moments alone.  This is what lets the matrix world and the kernel world be compared without an
approximation argument.

Since `J + K = 2W` and `J − K = 2(1 − W)`, the left-hand side unfolds to

```
  4^m · trace (compPow (W ∘ (1−W)) (m−1)) + trace (compPow (2W−1) (2m−1)),
```

which is `4^m Alt_{2m}(W) + t(C_{2m}, 2W−1)` in the trace convention of `Defs.lean`.
-/

open MeasureTheory OddCycleBound Finset

set_option linter.unusedSectionVars false

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Powers in the unitisation -/

namespace GK

/-- The `(r+1)`-fold composition, as an element of `GK μ`. -/
noncomputable def pow (z : GK μ) (r : ℕ) : GK μ := ⟨compPow μ z.ker r, goodK_compPow z.good r⟩

@[simp] lemma pow_ker (z : GK μ) (r : ℕ) : (pow z r).ker = compPow μ z.ker r := rfl

@[simp] lemma pow_zero' (z : GK μ) : pow z 0 = z := rfl

lemma pow_succ' (z : GK μ) (r : ℕ) : pow z (r + 1) = z * pow z r := rfl

/-- Scalars come out of a composition power with the exponent raised by one. -/
lemma pow_smul (c : ℝ) (z : GK μ) : ∀ r : ℕ, pow (c • z) r = (c ^ (r + 1)) • pow z r
  | 0 => by
      refine ext_ker (funext fun p => funext fun q => ?_)
      show c * z.ker p q = c ^ (0 + 1) * z.ker p q
      rw [zero_add, pow_one]
  | r + 1 => by
      refine ext_ker ?_
      have ih : (pow (c • z) r).ker = ((c ^ (r + 1)) • pow z r).ker := congrArg GK.ker (pow_smul c z r)
      show comp μ (fun p q => c * z.ker p q) (pow (c • z) r).ker = _
      rw [ih, smul_ker, pow_ker, OddCycleBound.comp_smul_left, OddCycleBound.comp_smul_right]
      funext p q
      show c * (c ^ (r + 1) * compPow μ z.ker (r + 1) p q)
          = c ^ (r + 1 + 1) * compPow μ z.ker (r + 1) p q
      rw [pow_succ]
      ring

end GK

/-- `(inr z) ^ (r+1) = inr (z ∘ ⋯ ∘ z)`. -/
lemma inr_pow (z : GK μ) : ∀ r : ℕ,
    (Unitization.inr z : KAlg μ) ^ (r + 1) = Unitization.inr (GK.pow z r)
  | 0 => by rw [pow_one, GK.pow_zero']
  | r + 1 => by
      rw [_root_.pow_succ' (Unitization.inr z : KAlg μ) (r + 1), inr_pow z r,
        ← Unitization.inr_mul, GK.pow_succ']

/-! ### The graphon kernels

`sgn W = 2W − 1` and `cmpl W = 1 − W` are defined in `Defs.lean`, with the two densities. -/

variable {W : Ω → Ω → ℝ}

/-- `W` as an element of the kernel algebra. -/
def wElt (hW : IsGraphon W μ) : GK μ := ⟨W, goodK_of_isGraphon hW⟩

/-- `1 − W` as an element of the kernel algebra. -/
def uElt (hW : IsGraphon W μ) : GK μ := ⟨cmpl W, goodK_cmpl hW⟩

/-- `2W − 1` as an element of the kernel algebra. -/
def kElt (hW : IsGraphon W μ) : GK μ := ⟨sgn W, goodK_sgn hW⟩

/-- `k`, in the unitisation. -/
def kU (hW : IsGraphon W μ) : KAlg μ := Unitization.inr (kElt hW)

/-- The normalized centered kernel as a bounded-kernel element. -/
noncomputable def densityKElt (hW : IsGraphon W μ) (D : DensityParams) : GK μ :=
  ⟨normalizedCentered W D.p D.s, goodK_normalizedCentered hW D.p D.s⟩

/-- The centered kernel as a bounded-kernel element. -/
def centeredElt (hW : IsGraphon W μ) (D : DensityParams) : GK μ :=
  ⟨centered W D.p, goodK_centered hW D.p⟩

/-- The normalized centered kernel in the unitized kernel algebra. -/
noncomputable def densityKU (hW : IsGraphon W μ) (D : DensityParams) : KAlg μ :=
  Unitization.inr (densityKElt hW D)

/-- Moments of the normalized centered kernel. -/
noncomputable def densityKMoment (hW : IsGraphon W μ) (D : DensityParams) (g : ℕ) : ℝ :=
  KAlg.phi μ (densityKU hW D ^ g)

/-- The moments `μ_g = φ (k ^ g)`; `μ_0 = 1`. -/
noncomputable def kMoment (hW : IsGraphon W μ) (g : ℕ) : ℝ := KAlg.phi μ (kU hW ^ g)

@[simp] lemma kMoment_zero (hW : IsGraphon W μ) : kMoment hW 0 = 1 := by
  simp [kMoment, KAlg.phi, doubleMean]

/-- `J + K = 2W`. -/
lemma ones_add_kElt (hW : IsGraphon W μ) : GK.ones μ + kElt hW = (2 : ℝ) • wElt hW := by
  ext p q; show (1 : ℝ) + (2 * W p q - 1) = 2 * W p q; ring

/-- `J − K = 2(1 − W)`. -/
lemma ones_sub_kElt (hW : IsGraphon W μ) : GK.ones μ - kElt hW = (2 : ℝ) • uElt hW := by
  ext p q; show (1 : ℝ) - (2 * W p q - 1) = 2 * (1 - W p q); ring

lemma densityKElt_eq_s_inv_smul_centeredElt (hW : IsGraphon W μ) (D : DensityParams) :
    densityKElt hW D = D.s⁻¹ • centeredElt hW D := by
  ext x y
  change (W x y - D.p) / D.s = D.s⁻¹ * (W x y - D.p)
  rw [div_eq_mul_inv, mul_comm]

/-- The red period-two factor is the graphon kernel divided by its density. -/
lemma ones_add_densityKElt (hW : IsGraphon W μ) (D : DensityParams) :
    GK.ones μ + D.a • densityKElt hW D = D.p⁻¹ • wElt hW := by
  ext x y
  change 1 + D.a * ((W x y - D.p) / D.s) = D.p⁻¹ * W x y
  rw [D.a_eq]
  field_simp [ne_of_gt D.p_pos, ne_of_gt D.s_pos]
  ring

/-- The blue period-two factor is the complementary graphon kernel divided by its density. -/
lemma ones_sub_densityKElt (hW : IsGraphon W μ) (D : DensityParams) :
    GK.ones μ - D.b • densityKElt hW D = D.q⁻¹ • uElt hW := by
  have hq : 1 - D.p ≠ 0 := by
    rw [← D.q_eq]
    exact ne_of_gt D.q_pos
  ext x y
  change 1 - D.b * ((W x y - D.p) / D.s) = D.q⁻¹ * (1 - W x y)
  rw [D.b_eq, D.q_eq]
  field_simp [hq, ne_of_gt D.s_pos]
  ring

lemma j_add_densityKU (hW : IsGraphon W μ) (D : DensityParams) :
    KAlg.j μ + D.a • densityKU hW D = Unitization.inr (D.p⁻¹ • wElt hW) := by
  rw [KAlg.j, densityKU, ← Unitization.inr_smul, ← Unitization.inr_add,
    ones_add_densityKElt hW D]

lemma j_sub_densityKU (hW : IsGraphon W μ) (D : DensityParams) :
    KAlg.j μ - D.b • densityKU hW D = Unitization.inr (D.q⁻¹ • uElt hW) := by
  rw [KAlg.j, densityKU, ← Unitization.inr_smul, ← Unitization.inr_sub,
    ones_sub_densityKElt hW D]

/-- The period-two product is the alternating graphon product scaled by `(p*q)⁻¹`. -/
lemma density_factor (hW : IsGraphon W μ) (D : DensityParams) :
    (KAlg.j μ + D.a • densityKU hW D) * (KAlg.j μ - D.b • densityKU hW D) =
      Unitization.inr ((D.p * D.q)⁻¹ • (wElt hW * uElt hW)) := by
  rw [j_add_densityKU hW D, j_sub_densityKU hW D, ← Unitization.inr_mul,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 2
  field_simp [ne_of_gt D.p_pos, ne_of_gt D.q_pos]

/-- The alternating product `(J + K)(J − K)` is `4 · (W ∘ U)`. -/
lemma alt_factor (hW : IsGraphon W μ) :
    (KAlg.j μ + kU hW) * (KAlg.j μ - kU hW)
      = Unitization.inr ((4 : ℝ) • (wElt hW * uElt hW)) := by
  have hadd : (KAlg.j μ + kU hW) = Unitization.inr ((2 : ℝ) • wElt hW) := by
    rw [KAlg.j, kU, ← Unitization.inr_add, ones_add_kElt]
  have hsub : (KAlg.j μ - kU hW) = Unitization.inr ((2 : ℝ) • uElt hW) := by
    rw [KAlg.j, kU, ← Unitization.inr_sub, ones_sub_kElt]
  rw [hadd, hsub, ← Unitization.inr_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num

/-! ### Fact A for kernels -/

/-- **Fact A, kernel side.**  The same universal expression in the moments as on the matrix side. -/
theorem tau_alt_kernel (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) :
    KAlg.tau μ (((KAlg.j μ + kU hW) * (KAlg.j μ - kU hW)) ^ m) + KAlg.tau μ (kU hW ^ (2 * m))
      = ∑ a ∈ range (2 * m + 1), ∑ b ∈ range (2 * m + 1),
          RankOne.coeff RankOne.alt (kMoment hW) (2 * m) a b * kMoment hW (a + b) :=
  RankOne.tau_alt_add (kMoment hW) (KAlg.j μ) (kU hW) (KAlg.tau μ)
    (fun b => KAlg.j_mul_mul_j (kU hW ^ b)) KAlg.tau_mul_comm
    (fun g => KAlg.tau_j_mul (kU hW ^ g)) hm

/-- The period-two centered-kernel word has the same universal moment expansion as its matrix
counterpart. -/
theorem tau_density_kernel (hW : IsGraphon W μ) (D : DensityParams) {m : ℕ} (hm : Odd m) :
    KAlg.tau μ
          (((KAlg.j μ + D.a • densityKU hW D) *
            (KAlg.j μ - D.b • densityKU hW D)) ^ m) +
        KAlg.tau μ (densityKU hW D ^ (2 * m)) =
      ∑ x ∈ range (2 * m + 1), ∑ y ∈ range (2 * m + 1),
        RankOne.coeff (RankOne.colorPattern D.a D.b) (densityKMoment hW D)
          (2 * m) x y * densityKMoment hW D (x + y) :=
  RankOne.tau_colorPattern_add D.a D.b (densityKMoment hW D) (KAlg.j μ)
    (densityKU hW D) (KAlg.tau μ)
    (fun g => KAlg.j_mul_mul_j (densityKU hW D ^ g)) KAlg.tau_mul_comm
    (fun g => KAlg.tau_j_mul (densityKU hW D ^ g)) D.ab_eq hm

/-! ### The two sides as densities -/

/-- `τ (k ^ (2m)) = t(C_{2m}, 2W−1)` in the trace convention. -/
lemma tau_kU_pow (hW : IsGraphon W μ) (r : ℕ) :
    KAlg.tau μ (kU hW ^ (r + 1)) = trace μ (compPow μ (sgn W) r) := by
  rw [kU, inr_pow]; rfl

/-- Powers of the normalized centered kernel scale powers of the unnormalized centered kernel. -/
lemma tau_densityKU_pow (hW : IsGraphon W μ) (D : DensityParams) (r : ℕ) :
    KAlg.tau μ (densityKU hW D ^ (r + 1)) =
      (D.s⁻¹) ^ (r + 1) * trace μ (compPow μ (centered W D.p) r) := by
  rw [densityKU, inr_pow, densityKElt_eq_s_inv_smul_centeredElt, GK.pow_smul]
  show trace μ (((D.s⁻¹) ^ (r + 1) • GK.pow (centeredElt hW D) r).ker) = _
  rw [GK.smul_ker, GK.pow_ker, trace_smul]
  rfl

/-- `τ ((( J+K)(J−K)) ^ m) = 4^m · Alt_{2m}(W)` in the trace convention. -/
lemma tau_alt_factor (hW : IsGraphon W μ) (t : ℕ) :
    KAlg.tau μ (((KAlg.j μ + kU hW) * (KAlg.j μ - kU hW)) ^ (t + 1))
      = 4 ^ (t + 1) * trace μ (compPow μ (comp μ W (cmpl W)) t) := by
  rw [alt_factor hW, inr_pow, GK.pow_smul]
  show trace μ (((4 : ℝ) ^ (t + 1) • GK.pow (wElt hW * uElt hW) t).ker) = _
  rw [GK.smul_ker, GK.pow_ker]
  exact trace_smul _ _

/-- The period-two factor contributes `(p*q)⁻m` times the alternating-cycle trace. -/
lemma tau_density_factor (hW : IsGraphon W μ) (D : DensityParams) (t : ℕ) :
    KAlg.tau μ
        (((KAlg.j μ + D.a • densityKU hW D) *
          (KAlg.j μ - D.b • densityKU hW D)) ^ (t + 1)) =
      ((D.p * D.q)⁻¹) ^ (t + 1) *
        trace μ (compPow μ (comp μ W (cmpl W)) t) := by
  rw [density_factor hW D, inr_pow, GK.pow_smul]
  show trace μ
      (((((D.p * D.q)⁻¹) ^ (t + 1)) • GK.pow (wElt hW * uElt hW) t).ker) = _
  rw [GK.smul_ker, GK.pow_ker]
  exact trace_smul _ _

/-- The normalized alternating and centered even-cycle densities equal the universal period-two
moment expression. -/
theorem normalized_alt_add_centeredCycle_eq_necklace
    (hW : IsGraphon W μ) (D : DensityParams) {m : ℕ} (hm : Odd m) :
    ((D.p * D.q)⁻¹) ^ m * altDensity W μ m +
        ((D.p * D.q)⁻¹) ^ m * signedCycleDensity (centered W D.p) μ (2 * m) =
      ∑ x ∈ range (2 * m + 1), ∑ y ∈ range (2 * m + 1),
        RankOne.coeff (RankOne.colorPattern D.a D.b) (densityKMoment hW D)
          (2 * m) x y * densityKMoment hW D (x + y) := by
  have hm0 : m ≠ 0 := by
    obtain ⟨k, hk⟩ := hm
    omega
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have htwo : 1 ≤ 2 * m := by omega
  have hscale : (D.s⁻¹) ^ (2 * m) = ((D.p * D.q)⁻¹) ^ m := by
    calc
      (D.s⁻¹) ^ (2 * m) = ((D.s⁻¹) ^ 2) ^ m := by rw [pow_mul]
      _ = ((D.p * D.q)⁻¹) ^ m := by rw [inv_pow, D.s_sq]
  have halt := tau_density_factor hW D (m - 1)
  rw [Nat.sub_add_cancel hm1] at halt
  have hcenter := tau_densityKU_pow hW D (2 * m - 1)
  rw [Nat.sub_add_cancel htwo] at hcenter
  rw [altDensity, signedCycleDensity, ← halt, ← hscale, ← hcenter]
  exact tau_density_kernel hW D hm

/-- For an arbitrary graphon on an arbitrary probability space, the two
alternating and centered densities add up to the universal moment expression. -/
theorem alt_add_cycle_eq_necklace (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) :
    4 ^ m * altDensity W μ m + signedCycleDensity (sgn W) μ (2 * m)
      = ∑ a ∈ range (2 * m + 1), ∑ b ∈ range (2 * m + 1),
          RankOne.coeff RankOne.alt (kMoment hW) (2 * m) a b * kMoment hW (a + b) := by
  rw [altDensity, signedCycleDensity]
  obtain ⟨t, rfl⟩ := hm
  rw [show 2 * t + 1 - 1 = 2 * t from by omega, ← tau_alt_factor hW (2 * t),
    show 2 * (2 * t + 1) - 1 = 4 * t + 1 from by omega, ← tau_kU_pow hW (4 * t + 1),
    show 4 * t + 1 + 1 = 2 * (2 * t + 1) from by omega]
  exact tau_alt_kernel hW ⟨t, rfl⟩

end AlternatingCycle
