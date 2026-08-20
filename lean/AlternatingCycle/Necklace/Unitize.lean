import AlternatingCycle.Foundation.Kernel
import AlternatingCycle.Foundation.GraphonL2Operator
import Mathlib.Algebra.Algebra.Unitization

/-!
# The unitized kernel algebra

Kernel composition has no identity element, while `Necklace/RankOne.lean` works in a unital ring.
So the bounded measurable kernels are bundled as a non-unital `ℝ`-algebra `GK μ` and a unit is
adjoined with mathlib's `Unitization`:

```
  KAlg μ := Unitization ℝ (GK μ),      (a, Z) * (b, Y) = (a * b, a • Y + b • Z + Z ∘ Y).
```

Every `GoodK` side-condition is discharged once, inside the instances, and never appears again: in
`KAlg μ` associativity is `mul_assoc` and bilinearity is `mul_add`, so `Necklace/RankOne.lean`
applies verbatim.

The trace extends to the whole unitisation by `τ (a, Z) := trace μ Z`, which is linear and still
cyclic, so no ideal and no partial trace are needed.  It sends the unit to `0`, which is harmless:
the necklace identity never takes `τ` of the unit.
-/

-- The kernel lemmas of `Foundation/Kernel.lean` all carry `[IsProbabilityMeasure μ]`, so it stays in
-- the section variables even where a particular lemma does not use it.
set_option linter.unusedSectionVars false

open MeasureTheory OddCycleBound

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Closure properties of `GoodK` -/

lemma goodK_smul (c : ℝ) {K : Ω → Ω → ℝ} (hK : GoodK K) : GoodK (fun x y => c * K x y) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  refine ⟨measurable_const.mul hK.meas, |c| * C, mul_nonneg (abs_nonneg c) hC0, fun x y => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x y) (abs_nonneg c)

lemma goodK_neg {K : Ω → Ω → ℝ} (hK : GoodK K) : GoodK (fun x y => -K x y) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  exact ⟨hK.meas.neg, C, hC0, fun x y => by rw [abs_neg]; exact hC x y⟩

lemma goodK_sub {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) :
    GoodK (fun x y => K x y - L x y) := by
  simpa [sub_eq_add_neg] using goodK_add hK (goodK_neg hL)

lemma trace_add {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) :
    trace μ (fun x y => K x y + L x y) = trace μ K + trace μ L :=
  integral_add hK.diag_integrable hL.diag_integrable

lemma trace_smul (c : ℝ) (K : Ω → Ω → ℝ) :
    trace μ (fun x y => c * K x y) = c * trace μ K :=
  integral_const_mul c _

lemma comp_zero_left (L : Ω → Ω → ℝ) : comp μ (fun _ _ => (0 : ℝ)) L = fun _ _ => 0 := by
  funext x y; simp [comp]

lemma comp_zero_right (K : Ω → Ω → ℝ) : comp μ K (fun _ _ => (0 : ℝ)) = fun _ _ => 0 := by
  funext x y; simp [comp]

/-! ### The non-unital algebra of bounded kernels -/

/-- A bounded measurable kernel on `(Ω, μ)`.  The measure is a parameter of the type so that the
composition instance below can depend on it. -/
structure GK (μ : Measure Ω) where
  /-- The underlying kernel. -/
  ker : Ω → Ω → ℝ
  /-- It is bounded and measurable. -/
  good : GoodK ker

namespace GK

@[ext] lemma ext {x y : GK μ} (h : ∀ p q, x.ker p q = y.ker p q) : x = y := by
  cases x; cases y
  have : _ = _ := funext fun p => funext fun q => h p q
  subst this; rfl

lemma ext_ker {x y : GK μ} (h : x.ker = y.ker) : x = y := ext fun p q => congrFun (congrFun h p) q

instance : Zero (GK μ) := ⟨⟨fun _ _ => 0, goodK_zero⟩⟩
instance : Add (GK μ) := ⟨fun x y => ⟨fun p q => x.ker p q + y.ker p q, goodK_add x.good y.good⟩⟩
instance : Neg (GK μ) := ⟨fun x => ⟨fun p q => -x.ker p q, goodK_neg x.good⟩⟩
instance : Sub (GK μ) := ⟨fun x y => ⟨fun p q => x.ker p q - y.ker p q, goodK_sub x.good y.good⟩⟩
instance : SMul ℝ (GK μ) := ⟨fun c x => ⟨fun p q => c * x.ker p q, goodK_smul c x.good⟩⟩
noncomputable instance : Mul (GK μ) := ⟨fun x y => ⟨comp μ x.ker y.ker, goodK_comp x.good y.good⟩⟩

@[simp] lemma zero_ker : (0 : GK μ).ker = fun _ _ => 0 := rfl
@[simp] lemma add_ker (x y : GK μ) : (x + y).ker = fun p q => x.ker p q + y.ker p q := rfl
@[simp] lemma neg_ker (x : GK μ) : (-x).ker = fun p q => -x.ker p q := rfl
@[simp] lemma sub_ker (x y : GK μ) : (x - y).ker = fun p q => x.ker p q - y.ker p q := rfl
@[simp] lemma smul_ker (c : ℝ) (x : GK μ) : (c • x).ker = fun p q => c * x.ker p q := rfl
@[simp] lemma mul_ker (x y : GK μ) : (x * y).ker = comp μ x.ker y.ker := rfl

instance : AddCommGroup (GK μ) where
  add_assoc x y z := by ext p q; exact add_assoc _ _ _
  zero_add x := by ext p q; exact zero_add _
  add_zero x := by ext p q; exact add_zero _
  add_comm x y := by ext p q; exact add_comm _ _
  neg_add_cancel x := by ext p q; exact neg_add_cancel _
  sub_eq_add_neg x y := by ext p q; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul := zsmulRec
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl

instance : Module ℝ (GK μ) where
  one_smul x := by ext p q; exact one_mul _
  mul_smul c d x := by ext p q; exact mul_assoc _ _ _
  smul_zero c := by ext p q; exact mul_zero _
  smul_add c x y := by ext p q; exact mul_add _ _ _
  add_smul c d x := by ext p q; exact add_mul _ _ _
  zero_smul x := by ext p q; exact zero_mul _

noncomputable instance : NonUnitalRing (GK μ) where
  mul_assoc x y z := ext_ker (comp_assoc x.good y.good z.good)
  left_distrib x y z := ext_ker (comp_add_right x.good y.good z.good)
  right_distrib x y z := ext_ker (comp_add_left x.good y.good z.good)
  zero_mul x := ext_ker (comp_zero_left x.ker)
  mul_zero x := ext_ker (comp_zero_right x.ker)

instance : IsScalarTower ℝ (GK μ) (GK μ) :=
  ⟨fun c x y => ext_ker (comp_smul_left c x.ker y.ker)⟩

instance : SMulCommClass ℝ (GK μ) (GK μ) :=
  ⟨fun c x y => ext_ker (comp_smul_right c x.ker y.ker).symm⟩

/-- The kernel trace, as a linear functional. -/
noncomputable def traceL (μ : Measure Ω) [IsProbabilityMeasure μ] : GK μ →ₗ[ℝ] ℝ where
  toFun x := trace μ x.ker
  map_add' x y := trace_add x.good y.good
  map_smul' c x := trace_smul c x.ker

@[simp] lemma traceL_apply (x : GK μ) : traceL μ x = trace μ x.ker := rfl

/-- The all-ones kernel as an element of the algebra. -/
def ones (μ : Measure Ω) : GK μ := ⟨onesKernel, goodK_onesKernel⟩

@[simp] lemma ones_ker : (ones μ).ker = onesKernel := rfl

/-- `J` is idempotent. -/
lemma ones_mul_ones : ones μ * ones μ = ones μ := ext_ker comp_onesKernel_onesKernel

/-- **The cut lemma, bundled.**  `J ∘ Z ∘ J = (∫∫ Z) • J`: this is the rank-one-ness of `J`. -/
lemma ones_mul_mul_ones (x : GK μ) : ones μ * x * ones μ = doubleMean μ x.ker • ones μ := by
  refine ext_ker ?_
  rw [mul_ker, mul_ker, ones_ker, comp_assoc goodK_onesKernel x.good goodK_onesKernel, cut]
  funext p q
  simp [onesKernel]

/-- The trace against `J` reads off the double mean. -/
lemma trace_ones_mul (x : GK μ) : traceL μ (ones μ * x) = doubleMean μ x.ker :=
  trace_comp_onesKernel x.good

end GK

/-! ### The unitisation -/

/-- The unital `ℝ`-algebra of bounded kernels with a unit adjoined. -/
abbrev KAlg (μ : Measure Ω) [IsProbabilityMeasure μ] : Type _ := Unitization ℝ (GK μ)

namespace KAlg

/-- The trace, extended to the unitisation by ignoring the scalar part: linear, cyclic, total. -/
noncomputable def tau (μ : Measure Ω) [IsProbabilityMeasure μ] : KAlg μ →ₗ[ℝ] ℝ :=
  (GK.traceL μ).comp (Unitization.sndHom ℝ ℝ (GK μ))

@[simp] lemma tau_apply (x : KAlg μ) : tau μ x = trace μ x.snd.ker := rfl

/-- `τ` is cyclic on the whole algebra: the unit parts contribute symmetrically and the kernel part
is `trace_comp_comm`. -/
lemma tau_mul_comm (x y : KAlg μ) : tau μ (x * y) = tau μ (y * x) := by
  simp only [tau_apply, Unitization.snd_mul, GK.add_ker, GK.smul_ker, GK.mul_ker]
  rw [trace_add (goodK_add (goodK_smul _ y.snd.good) (goodK_smul _ x.snd.good))
      (goodK_comp x.snd.good y.snd.good),
    trace_add (goodK_smul _ y.snd.good) (goodK_smul _ x.snd.good),
    trace_add (goodK_add (goodK_smul _ x.snd.good) (goodK_smul _ y.snd.good))
      (goodK_comp y.snd.good x.snd.good),
    trace_add (goodK_smul _ x.snd.good) (goodK_smul _ y.snd.good),
    trace_comp_comm x.snd.good y.snd.good]
  ring

/-- The rank-one element `j`. -/
def j (μ : Measure Ω) [IsProbabilityMeasure μ] : KAlg μ := Unitization.inr (GK.ones μ)

/-- The scalar functional `φ (a, Z) = a + ∫∫ Z`. -/
noncomputable def phi (μ : Measure Ω) [IsProbabilityMeasure μ] (x : KAlg μ) : ℝ :=
  x.fst + doubleMean μ x.snd.ker

/-- **`hj`.**  `j` is rank one: `j * x * j = φ x • j` for every `x`. -/
lemma j_mul_mul_j (x : KAlg μ) : j μ * x * j μ = phi μ x • j μ := by
  refine Unitization.ext ?_ ?_
  · simp [j, phi]
  · have hsnd : (j μ * x * j μ).snd
        = x.fst • (GK.ones μ * GK.ones μ) + GK.ones μ * x.snd * GK.ones μ := by
      simp only [j, Unitization.snd_mul, Unitization.fst_mul, Unitization.fst_inr,
        Unitization.snd_inr, zero_mul, zero_smul, zero_add, add_zero]
      rw [add_mul, smul_mul_assoc]
    rw [hsnd, GK.ones_mul_ones, GK.ones_mul_mul_ones, phi]
    simp [j, add_smul]

/-- **`hτj`.**  `τ (j * x) = φ x`.  The `∫∫` comes from the cut lemma and the `x.fst` from
`trace J = 1`. -/
lemma tau_j_mul (x : KAlg μ) : tau μ (j μ * x) = phi μ x := by
  have hsnd : (j μ * x).snd = x.fst • GK.ones μ + GK.ones μ * x.snd := by
    simp only [j, Unitization.snd_mul, Unitization.fst_inr, Unitization.snd_inr, zero_smul,
      zero_add]
  rw [tau_apply, ← GK.traceL_apply, hsnd, map_add, GK.traceL_apply, GK.smul_ker,
    trace_smul, GK.ones_ker, trace_onesKernel, GK.trace_ones_mul, phi, mul_one]

end KAlg

end AlternatingCycle
