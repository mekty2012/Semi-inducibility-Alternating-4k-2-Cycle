import AlternatingCycle.Foundation.Kernel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# L² foundations for graphon kernel operators

This file starts the graphon Hilbert-space layer used by the C9 low-band
argument.  It does not assert compactness or trace-class spectral identities.
Instead it provides the concrete L² objects already forced by the integral
graphon definitions: bounded graphon-side functions define elements of
`Lp ℝ 2 μ`, and the constant vector paired with the graphon degree function is
exactly the edge density.

The missing hard theorem remains the construction of the compact self-adjoint
integral operator on `Lp ℝ 2 μ` and its countable trace/eigenvalue identities.
-/

open MeasureTheory
open scoped InnerProductSpace
open scoped ENNReal

-- A few lemmas do not use the section variable `[IsProbabilityMeasure mu]`; keep the declarations uniform.
set_option linter.unusedSectionVars false

noncomputable section

namespace OddCycleBound
namespace Spectral
namespace L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega] {mu : Measure Omega}
variable [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/-- A bounded strongly measurable real function is in `L²` over a probability
space. -/
lemma good_memLp_two {f : Omega -> Real} (hf : Good f) :
    MemLp f 2 mu := by
  obtain ⟨C, _hC0, hC⟩ := hf.bdd
  exact MemLp.of_bound hf.meas.aestronglyMeasurable C
    (ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs] using hC x)

/-- The zero function is a `Good` representative. -/
lemma good_zero : Good (fun _ : Omega => (0 : Real)) :=
  ⟨stronglyMeasurable_const, ⟨0, le_rfl, fun _ => by simp⟩⟩

/-- Taking pointwise absolute values preserves `Good` representatives. -/
lemma good_abs {f : Omega -> Real} (hf : Good f) :
    Good (fun x => |f x|) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨continuous_abs.comp_stronglyMeasurable hf.meas, ⟨C, hC0, fun x => ?_⟩⟩
  simpa [abs_abs] using hC x

/-- Negation preserves `Good` representatives. -/
lemma good_neg {f : Omega -> Real} (hf : Good f) :
    Good (fun x => - f x) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨hf.meas.neg, C, hC0, fun x => ?_⟩
  simpa using hC x

/-- Subtraction preserves `Good` representatives. -/
lemma good_sub {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    Good (fun x => f x - g x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bdd
  refine ⟨hf.meas.sub hg.meas, Cf + Cg, add_nonneg hCf0 hCg0, fun x => ?_⟩
  calc
    |f x - g x| <= |f x| + |g x| := abs_sub _ _
    _ <= Cf + Cg := add_le_add (hCf x) (hCg x)

/-- The `L²` vector represented by a bounded strongly measurable function. -/
def goodL2 {f : Omega -> Real} (hf : Good f) :
    Lp Real 2 mu :=
  (good_memLp_two hf).toLp f

/-- The chosen representative of `goodL2 hf` agrees almost everywhere with
the original pointwise function. -/
lemma goodL2_ae_eq {f : Omega -> Real} (hf : Good f) :
    (goodL2 (mu := mu) hf : Omega -> Real) =ᵐ[mu] f :=
  MemLp.coeFn_toLp (good_memLp_two hf)

/-- Inner products of `Good` representatives are the usual integral pairings. -/
lemma inner_goodL2_eq_integral_mul {f g : Omega -> Real}
    (hf : Good f) (hg : Good g) :
    inner Real (goodL2 (mu := mu) hf) (goodL2 (mu := mu) hg) =
      ∫ x, f x * g x ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  have hfae := goodL2_ae_eq (mu := mu) hf
  have hgae := goodL2_ae_eq (mu := mu) hg
  refine integral_congr_ae ?_
  filter_upwards [hfae, hgae] with x hfx hgx
  rw [hfx, hgx]
  simp [RCLike.inner_apply, mul_comm]

/-- The squared `L²` norm of a `Good` representative is its integral square. -/
lemma norm_goodL2_sq_eq_integral_mul {f : Omega -> Real}
    (hf : Good f) :
    ‖goodL2 (mu := mu) hf‖ ^ 2 =
      ∫ x, f x * f x ∂mu := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_goodL2_eq_integral_mul hf hf

/-- The `Good` embedding into `L2` respects pointwise subtraction. -/
lemma goodL2_sub {f g : Omega -> Real}
    (hf : Good f) (hg : Good g) :
    goodL2 (mu := mu) (good_sub hf hg) =
      goodL2 (mu := mu) hf - goodL2 (mu := mu) hg := by
  calc
    goodL2 (mu := mu) (good_sub hf hg)
        =
          ((good_memLp_two hf).sub (good_memLp_two hg)).toLp (f - g) := by
          exact MemLp.toLp_congr
            (good_memLp_two (good_sub hf hg))
            ((good_memLp_two hf).sub (good_memLp_two hg))
            (ae_of_all _ fun _ => rfl)
    _ = goodL2 (mu := mu) hf - goodL2 (mu := mu) hg := by
          exact MemLp.toLp_sub (good_memLp_two hf) (good_memLp_two hg)

/-- The `Good` embedding into `L2` respects pointwise absolute values. -/
lemma goodL2_abs {f : Omega -> Real} (hf : Good f) :
    goodL2 (mu := mu) (good_abs hf) =
      |goodL2 (mu := mu) hf| := by
  rw [Lp.ext_iff]
  filter_upwards [goodL2_ae_eq (mu := mu) (good_abs hf),
    Lp.coeFn_abs (goodL2 (mu := mu) hf),
    goodL2_ae_eq (mu := mu) hf] with x hgood hLp hbase
  rw [hgood, hLp, hbase]

/-- The `Good` embedding into `L2` respects scalar multiplication. -/
lemma goodL2_smul (c : Real) {f : Omega -> Real} (hf : Good f) :
    goodL2 (mu := mu) (good_smul c hf) =
      c • goodL2 (mu := mu) hf := by
  calc
    goodL2 (mu := mu) (good_smul c hf)
        =
          ((good_memLp_two hf).const_smul c).toLp (c • f) := by
          exact MemLp.toLp_congr
            (good_memLp_two (good_smul c hf))
            ((good_memLp_two hf).const_smul c)
            (ae_of_all _ fun _ => rfl)
    _ = c • goodL2 (mu := mu) hf := by
          exact MemLp.toLp_const_smul c (good_memLp_two hf)

/-- The integral square of a `Good` representative is nonnegative. -/
lemma integral_mul_self_nonneg_of_good {f : Omega -> Real}
    (hf : Good f) :
    0 <= ∫ x, f x * f x ∂mu := by
  rw [← norm_goodL2_sq_eq_integral_mul (mu := mu) hf]
  positivity

/-- The constant-one vector in `L²(mu)`. -/
def oneL2 (mu : Measure Omega) [IsProbabilityMeasure mu] :
    Lp Real 2 mu :=
  (memLp_const (1 : Real)).toLp (fun _ : Omega => 1)

/-- The pointwise representative of `oneL2` is almost everywhere the constant
function `1`. -/
lemma oneL2_ae_eq_one :
    (oneL2 (Omega := Omega) mu : Omega -> Real) =ᵐ[mu]
      fun _ : Omega => 1 :=
  MemLp.coeFn_toLp (memLp_const (1 : Real))

/-- The `Good` representative of the constant-one function gives the same
`L²` vector as `oneL2`. -/
lemma goodL2_one_eq_oneL2 :
    goodL2 (mu := mu) (good_one (Ω := Omega)) =
      oneL2 (Omega := Omega) mu := by
  exact MemLp.toLp_congr
    (good_memLp_two (good_one (Ω := Omega)))
    (memLp_const (1 : Real))
    (ae_of_all _ fun _ => rfl)

/-- The graphon degree function is in `L²`. -/
lemma degree_memLp_two (hW : IsGraphon W mu) :
    MemLp (degree W mu) 2 mu :=
  good_memLp_two (good_degree hW)

/-- The graphon degree as an `L²` vector. -/
def degreeL2 (hW : IsGraphon W mu) : Lp Real 2 mu :=
  (degree_memLp_two hW).toLp (degree W mu)

/-- A graphon kernel is uniformly bounded by `1` in absolute value. -/
lemma graphon_abs_le_one (hW : IsGraphon W mu) :
    forall x y, |W x y| <= 1 := by
  intro x y
  rw [abs_of_nonneg (hW.nonneg x y)]
  exact hW.le_one x y

/-- A bounded measurable kernel sends bounded strongly measurable functions to
bounded strongly measurable functions.

This is the non-graphon version needed for approximation arguments: simple
kernel approximants and kernel differences are generally `GoodK`, not
`IsGraphon`. -/
lemma good_kernelOp_goodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    Good (kernelOp K mu f) := by
  obtain ⟨CK, hCK0, hCK⟩ := hK.bdd
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  refine ⟨?_, ⟨CK * Cf, mul_nonneg hCK0 hCf0, fun x => ?_⟩⟩
  · have hSM : StronglyMeasurable
        (fun p : Omega × Omega => K p.1 p.2 * f p.2) :=
      hK.meas.stronglyMeasurable.mul
        (hf.meas.comp_measurable measurable_snd)
    exact hSM.integral_prod_right'
  · have hint : Integrable (fun y => K x y * f y) mu := by
      have hmK : Measurable (fun y => K x y) :=
        hK.meas.comp measurable_prodMk_left
      refine (integrable_const (CK * Cf)).mono'
        (hmK.stronglyMeasurable.mul hf.meas).aestronglyMeasurable
        (ae_of_all _ fun y => ?_)
      change |K x y * f y| <= CK * Cf
      rw [abs_mul]
      exact mul_le_mul (hCK x y) (hCf y) (abs_nonneg _) hCK0
    calc
      |kernelOp K mu f x|
          <= ∫ y, |K x y * f y| ∂mu := abs_integral_le_integral_abs
      _ <= ∫ _y, CK * Cf ∂mu := by
          refine integral_mono hint.abs (integrable_const (CK * Cf)) ?_
          intro y
          change |K x y * f y| <= CK * Cf
          rw [abs_mul]
          exact mul_le_mul (hCK x y) (hCf y) (abs_nonneg _) hCK0
      _ = CK * Cf := by simp

/-- A bounded measurable kernel sends bounded representatives to `L²`. -/
lemma kernelOpGoodK_memLp_two {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    MemLp (kernelOp K mu f) 2 mu :=
  good_memLp_two (good_kernelOp_goodK (mu := mu) hK hf)

/-- The `L²` vector represented by applying a bounded measurable kernel to a
bounded representative. -/
def kernelOpL2OfGoodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    Lp Real 2 mu :=
  (kernelOpGoodK_memLp_two (mu := mu) hK hf).toLp (kernelOp K mu f)

/-- The chosen representative of the `GoodK` kernel transform agrees almost
everywhere with the pointwise kernel transform. -/
lemma kernelOpL2OfGoodK_ae_eq {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    (kernelOpL2OfGoodK (mu := mu) hK hf : Omega -> Real) =ᵐ[mu]
      kernelOp K mu f :=
  MemLp.coeFn_toLp (kernelOpGoodK_memLp_two (mu := mu) hK hf)

/-- The integrand defining a bounded-kernel transform is integrable for
bounded representatives. -/
lemma integrable_Kf {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    Integrable (fun y => K x y * f y) mu := by
  obtain ⟨CK, hCK0, hCK⟩ := hK.bdd
  obtain ⟨Cf, _hCf0, hCf⟩ := hf.bdd
  have hmK : Measurable (fun y => K x y) :=
    hK.meas.comp measurable_prodMk_left
  refine (integrable_const (CK * Cf)).mono'
    (hmK.stronglyMeasurable.mul hf.meas).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  change |K x y * f y| <= CK * Cf
  rw [abs_mul]
  exact mul_le_mul (hCK x y) (hCf y) (abs_nonneg _) hCK0

/-- The bounded-kernel transform respects almost-everywhere equality of
representatives. -/
lemma kernelOpGoodK_congr_ae {K : Omega -> Omega -> Real}
    {f g : Omega -> Real} (hfg : f =ᵐ[mu] g) :
    kernelOp K mu f = kernelOp K mu g := by
  funext x
  simp only [kernelOp]
  refine integral_congr_ae ?_
  filter_upwards [hfg] with y hy
  rw [hy]

/-- Composing a kernel with the row-broadcast kernel `(z, y) ↦ f z`
is the same as applying the kernel to `f`, pointwise in the first variable. -/
lemma comp_rowBroadcast_eq_kernelOp {K : Omega -> Omega -> Real}
    (f : Omega -> Real) :
    comp mu K (fun z _y => f z) = fun x _y => kernelOp K mu f x := by
  rfl

/-- Pointwise composition law for bounded kernels acting on bounded
representatives: applying `L` and then `K` equals applying the composed
kernel `K ∘ L`.  This is a direct consequence of the already-proved
Fubini associativity of kernel composition. -/
lemma kernelOp_comp_eq_kernelOp_kernelOp {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {f : Omega -> Real} (hf : Good f) :
    kernelOp (comp mu K L) mu f =
      kernelOp K mu (kernelOp L mu f) := by
  have hassoc :=
    comp_assoc (μ := mu) hK hL (goodK_rowBroadcast (Ω := Omega) hf)
  have hleft :
      comp mu (comp mu K L) (fun z _y => f z) =
        fun x _y => kernelOp (comp mu K L) mu f x := by
    exact comp_rowBroadcast_eq_kernelOp (mu := mu) f
  have hright :
      comp mu L (fun z _y => f z) =
        fun x _y => kernelOp L mu f x := by
    exact comp_rowBroadcast_eq_kernelOp (mu := mu) f
  funext x
  have hx := congrFun (congrFun hassoc x) x
  rw [hleft] at hx
  rw [hright] at hx
  simpa [comp, kernelOp] using hx

/-- The pointwise composition law lifted to the chosen `L2` representatives. -/
lemma kernelOpL2OfGoodK_comp {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {f : Omega -> Real} (hf : Good f) :
    kernelOpL2OfGoodK (mu := mu) (goodK_comp (μ := mu) hK hL) hf =
      kernelOpL2OfGoodK (mu := mu) hK
        (good_kernelOp_goodK (mu := mu) hL hf) := by
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x =>
    congrFun (kernelOp_comp_eq_kernelOp_kernelOp
      (mu := mu) hK hL hf) x

/-- Iterated pointwise application of a bounded kernel operator.  The index
`0` is the identity, so `kernelOpIter K (n+1)` is `n+1` applications of
`K`. -/
noncomputable def kernelOpIter (mu : Measure Omega)
    (K : Omega -> Omega -> Real) : Nat -> (Omega -> Real) -> Omega -> Real
  | 0, f => f
  | n + 1, f => kernelOp K mu (kernelOpIter mu K n f)

/-- Bounded kernels preserve `Good` representatives under arbitrary finite
iteration. -/
lemma good_kernelOpIter_goodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    forall n, Good (kernelOpIter mu K n f)
  | 0 => hf
  | n + 1 =>
      good_kernelOp_goodK (mu := mu) hK
        (good_kernelOpIter_goodK hK hf n)

/-- Kernel powers act on bounded representatives as repeated applications of
the same integral operator. -/
lemma kernelOp_compPow_eq_kernelOpIter_succ
    {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) :
    forall n,
      kernelOp (compPow mu K n) mu f =
        kernelOpIter mu K (n + 1) f
  | 0 => rfl
  | n + 1 => by
      rw [compPow]
      calc
        kernelOp (comp mu K (compPow mu K n)) mu f
            =
              kernelOp K mu (kernelOp (compPow mu K n) mu f) := by
              exact kernelOp_comp_eq_kernelOp_kernelOp
                (mu := mu) hK (goodK_compPow (μ := mu) hK n) hf
        _ =
              kernelOp K mu (kernelOpIter mu K (n + 1) f) := by
              rw [kernelOp_compPow_eq_kernelOpIter_succ hK hf n]
        _ =
              kernelOpIter mu K (n + 2) f := rfl

/-- The preceding pointwise power identity lifted to the chosen `L2`
representatives. -/
lemma kernelOpL2OfGoodK_compPow_eq_goodL2_iter_succ
    {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f : Omega -> Real} (hf : Good f) (n : Nat) :
    kernelOpL2OfGoodK (mu := mu) (goodK_compPow (μ := mu) hK n) hf =
      goodL2 (mu := mu)
        (good_kernelOpIter_goodK (mu := mu) hK hf (n + 1)) := by
  exact MemLp.toLp_congr
    (kernelOpGoodK_memLp_two (mu := mu)
      (goodK_compPow (μ := mu) hK n) hf)
    (good_memLp_two
      (good_kernelOpIter_goodK (mu := mu) hK hf (n + 1)))
    (ae_of_all _ fun x =>
      congrFun (kernelOp_compPow_eq_kernelOpIter_succ
        (mu := mu) hK hf n) x)

/-- Pointwise differences of bounded measurable kernels are bounded
measurable kernels. -/
lemma goodK_sub {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L) :
    GoodK (fun x y => K x y - L x y) := by
  obtain ⟨CK, hCK0, hCK⟩ := hK.bdd
  obtain ⟨CL, hCL0, hCL⟩ := hL.bdd
  refine ⟨hK.meas.sub hL.meas, ⟨CK + CL, add_nonneg hCK0 hCL0, ?_⟩⟩
  intro x y
  calc
    |K x y - L x y| <= |K x y| + |L x y| := abs_sub _ _
    _ <= CK + CL := add_le_add (hCK x y) (hCL x y)

/-- The `L²` bounded-kernel transform is independent of the chosen
almost-everywhere representative. -/
lemma kernelOpL2OfGoodK_congr {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g)
    (hfg : f =ᵐ[mu] g) :
    kernelOpL2OfGoodK (mu := mu) hK hf =
      kernelOpL2OfGoodK (mu := mu) hK hg := by
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x =>
    congrFun (kernelOpGoodK_congr_ae (mu := mu) (K := K) hfg) x

/-- Pointwise additivity of bounded-kernel transforms on bounded
representatives. -/
lemma kernelOpGoodK_add' {K : Omega -> Omega -> Real}
    (hK : GoodK K) {f g : Omega -> Real}
    (hf : Good f) (hg : Good g) (x : Omega) :
    kernelOp K mu (f + g) x =
      kernelOp K mu f x + kernelOp K mu g x := by
  simp only [kernelOp, Pi.add_apply]
  rw [← integral_add (integrable_Kf (mu := mu) hK hf x)
    (integrable_Kf (mu := mu) hK hg x)]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/-- Pointwise homogeneity of bounded-kernel transforms. -/
lemma kernelOpGoodK_smul' {K : Omega -> Omega -> Real}
    (c : Real) (f : Omega -> Real) (x : Omega) :
    kernelOp K mu (c • f) x = c * kernelOp K mu f x := by
  simp only [kernelOp, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/-- Pointwise subtraction of bounded-kernel transforms in the kernel
argument. -/
lemma kernelOpGoodK_sub_kernel' {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L) {f : Omega -> Real}
    (hf : Good f) (x : Omega) :
    kernelOp (fun x y => K x y - L x y) mu f x =
      kernelOp K mu f x - kernelOp L mu f x := by
  simp only [kernelOp]
  rw [← integral_sub
    (integrable_Kf (mu := mu) hK hf x)
    (integrable_Kf (mu := mu) hL hf x)]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/-- Additivity of the `L²` bounded-kernel transform on bounded
representatives. -/
lemma kernelOpL2OfGoodK_add {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    kernelOpL2OfGoodK (mu := mu) hK (good_add hf hg) =
      kernelOpL2OfGoodK (mu := mu) hK hf +
        kernelOpL2OfGoodK (mu := mu) hK hg := by
  calc
    kernelOpL2OfGoodK (mu := mu) hK (good_add hf hg)
        =
          ((kernelOpGoodK_memLp_two (mu := mu) hK hf).add
            (kernelOpGoodK_memLp_two (mu := mu) hK hg)).toLp
            (kernelOp K mu f + kernelOp K mu g) := by
          exact MemLp.toLp_congr
            (kernelOpGoodK_memLp_two (mu := mu) hK (good_add hf hg))
            ((kernelOpGoodK_memLp_two (mu := mu) hK hf).add
              (kernelOpGoodK_memLp_two (mu := mu) hK hg))
            (ae_of_all _ fun x => kernelOpGoodK_add' (mu := mu) hK hf hg x)
    _ =
      kernelOpL2OfGoodK (mu := mu) hK hf +
        kernelOpL2OfGoodK (mu := mu) hK hg := by
          exact MemLp.toLp_add
            (kernelOpGoodK_memLp_two (mu := mu) hK hf)
            (kernelOpGoodK_memLp_two (mu := mu) hK hg)

/-- Homogeneity of the `L²` bounded-kernel transform on bounded
representatives. -/
lemma kernelOpL2OfGoodK_smul {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    (c : Real) {f : Omega -> Real} (hf : Good f) :
    kernelOpL2OfGoodK (mu := mu) hK (good_smul c hf) =
      c • kernelOpL2OfGoodK (mu := mu) hK hf := by
  calc
    kernelOpL2OfGoodK (mu := mu) hK (good_smul c hf)
        =
          ((kernelOpGoodK_memLp_two (mu := mu) hK hf).const_smul c).toLp
            (c • kernelOp K mu f) := by
          exact MemLp.toLp_congr
            (kernelOpGoodK_memLp_two (mu := mu) hK (good_smul c hf))
            ((kernelOpGoodK_memLp_two (mu := mu) hK hf).const_smul c)
            (ae_of_all _ fun x => kernelOpGoodK_smul' (mu := mu) c f x)
    _ = c • kernelOpL2OfGoodK (mu := mu) hK hf := by
          exact MemLp.toLp_const_smul c
            (kernelOpGoodK_memLp_two (mu := mu) hK hf)

/-- Subtraction of bounded-kernel transforms in the input representative. -/
lemma kernelOpL2OfGoodK_sub_input {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    kernelOpL2OfGoodK (mu := mu) hK (good_sub hf hg) =
      kernelOpL2OfGoodK (mu := mu) hK hf -
        kernelOpL2OfGoodK (mu := mu) hK hg := by
  calc
    kernelOpL2OfGoodK (mu := mu) hK (good_sub hf hg)
        =
          kernelOpL2OfGoodK (mu := mu) hK
            (good_add hf (good_neg hg)) := by
          exact kernelOpL2OfGoodK_congr (mu := mu) hK
            (good_sub hf hg)
            (good_add hf (good_neg hg))
            (ae_of_all _ fun x => by simp [sub_eq_add_neg])
    _ =
        kernelOpL2OfGoodK (mu := mu) hK hf +
          kernelOpL2OfGoodK (mu := mu) hK
            (good_neg hg) := by
          exact kernelOpL2OfGoodK_add (mu := mu) hK hf
            (good_neg hg)
    _ =
        kernelOpL2OfGoodK (mu := mu) hK hf -
          kernelOpL2OfGoodK (mu := mu) hK hg := by
          have hneg :
              kernelOpL2OfGoodK (mu := mu) hK (good_neg hg) =
                kernelOpL2OfGoodK (mu := mu) hK (good_smul (-1 : Real) hg) := by
            exact kernelOpL2OfGoodK_congr (mu := mu) hK
              (good_neg hg) (good_smul (-1 : Real) hg)
              (ae_of_all _ fun x => by simp)
          rw [hneg, kernelOpL2OfGoodK_smul (mu := mu) hK (-1) hg]
          simp [sub_eq_add_neg]

/-- Subtraction of bounded-kernel transforms in the kernel argument, lifted to
`L²` representatives. -/
lemma kernelOpL2OfGoodK_sub_kernel {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {f : Omega -> Real} (hf : Good f) :
    kernelOpL2OfGoodK (mu := mu) (goodK_sub hK hL) hf =
      kernelOpL2OfGoodK (mu := mu) hK hf -
        kernelOpL2OfGoodK (mu := mu) hL hf := by
  calc
    kernelOpL2OfGoodK (mu := mu) (goodK_sub hK hL) hf
        =
          ((kernelOpGoodK_memLp_two (mu := mu) hK hf).sub
            (kernelOpGoodK_memLp_two (mu := mu) hL hf)).toLp
            (kernelOp K mu f - kernelOp L mu f) := by
          exact MemLp.toLp_congr
            (kernelOpGoodK_memLp_two (mu := mu)
              (goodK_sub hK hL) hf)
            ((kernelOpGoodK_memLp_two (mu := mu) hK hf).sub
              (kernelOpGoodK_memLp_two (mu := mu) hL hf))
            (ae_of_all _ fun x =>
              kernelOpGoodK_sub_kernel' (mu := mu) hK hL hf x)
    _ =
      kernelOpL2OfGoodK (mu := mu) hK hf -
        kernelOpL2OfGoodK (mu := mu) hL hf := by
          exact MemLp.toLp_sub
            (kernelOpGoodK_memLp_two (mu := mu) hK hf)
            (kernelOpGoodK_memLp_two (mu := mu) hL hf)

/-- Pointwise `L¹` domination for a bounded measurable kernel. -/
lemma abs_kernelOpGoodK_le_const_integral_abs
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    |kernelOp K mu f x| <= C * ∫ y, |f y| ∂mu := by
  have hint : Integrable (fun y => K x y * f y) mu := by
    have hmK : Measurable (fun y => K x y) :=
      hK.meas.comp measurable_prodMk_left
    obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
    refine (integrable_const (C * Cf)).mono'
      (hmK.stronglyMeasurable.mul hf.meas).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    change |K x y * f y| <= C * Cf
    rw [abs_mul]
    exact mul_le_mul (hKC x y) (hCf y) (abs_nonneg _) hC0
  calc
    |kernelOp K mu f x|
        <= ∫ y, |K x y * f y| ∂mu := abs_integral_le_integral_abs
    _ <= ∫ y, C * |f y| ∂mu := by
        refine integral_mono hint.abs ((good_abs hf).integrable.const_mul C) ?_
        intro y
        change |K x y * f y| <= C * |f y|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hKC x y) (abs_nonneg _)
    _ = C * ∫ y, |f y| ∂mu := by
        rw [integral_const_mul]

/-- The squared norm of a bounded-kernel transform is its integral square. -/
lemma norm_kernelOpL2OfGoodK_sq_eq_integral_mul
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ ^ 2 =
      ∫ x, kernelOp K mu f x * kernelOp K mu f x ∂mu := by
  rw [← norm_goodL2_sq_eq_integral_mul
    (mu := mu) (good_kernelOp_goodK (mu := mu) hK hf)]
  rfl

/-- Applying a graphon kernel to a `Good` function again gives an `L²`
function. -/
lemma kernelOp_memLp_two (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    MemLp (kernelOp W mu f) 2 mu :=
  good_memLp_two (good_kernelOp hW hf)

/-- The `L²` vector represented by the pointwise graphon kernel transform of a
`Good` function. -/
def kernelOpL2OfGood (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    Lp Real 2 mu :=
  (kernelOp_memLp_two hW hf).toLp (kernelOp W mu f)

/-- The chosen representative of `kernelOpL2OfGood` agrees almost everywhere
with the pointwise kernel transform. -/
lemma kernelOpL2OfGood_ae_eq (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    (kernelOpL2OfGood (mu := mu) hW hf : Omega -> Real) =ᵐ[mu]
      kernelOp W mu f :=
  MemLp.coeFn_toLp (kernelOp_memLp_two hW hf)

/-- The row integrand of a graphon operator is integrable for any `L²`
representative. -/
lemma integrable_kernelOp_l2 (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) (x : Omega) :
    Integrable (fun y => W x y * f y) mu := by
  have hf_int : Integrable (fun y : Omega => f y) mu :=
    (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) <= 2)
  have hrow_meas : StronglyMeasurable (fun y : Omega => W x y) :=
    (hW.meas.comp measurable_prodMk_left).stronglyMeasurable
  refine hf_int.norm.mono'
    (hrow_meas.mul (Lp.stronglyMeasurable f)).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  change |W x y * f y| <= |f y|
  rw [abs_mul, abs_of_nonneg (hW.nonneg x y)]
  exact mul_le_of_le_one_left (abs_nonneg (f y)) (hW.le_one x y)

/-- Applying a graphon kernel to an arbitrary `L²` vector gives a bounded
strongly measurable representative.

This is the pointwise representative theorem for the graphon integral
operator; it does not assert any finite-rank or finite-spectrum property. -/
lemma good_kernelOp_l2 (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) :
    Good (kernelOp W mu (fun y : Omega => f y)) := by
  let C : Real := ∫ y, |f y| ∂mu
  have hf_int : Integrable (fun y : Omega => f y) mu :=
    (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) <= 2)
  have hprod_sm : StronglyMeasurable
      (fun p : Omega × Omega => W p.1 p.2 * f p.2) :=
    hW.meas.stronglyMeasurable.mul
      ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)
  refine ⟨hprod_sm.integral_prod_right', C, ?_, fun x => ?_⟩
  · exact integral_nonneg fun y => abs_nonneg (f y)
  · have hint : Integrable (fun y => W x y * f y) mu :=
      integrable_kernelOp_l2 (mu := mu) hW f x
    have hf_abs : Integrable (fun y : Omega => |f y|) mu := by
      simpa [Real.norm_eq_abs] using hf_int.norm
    calc
      |kernelOp W mu (fun y : Omega => f y) x|
          <= ∫ y, |W x y * f y| ∂mu := by
            simpa [kernelOp] using
              (abs_integral_le_integral_abs
                (μ := mu) (f := fun y : Omega => W x y * f y))
      _ <= ∫ y, |f y| ∂mu := by
            refine integral_mono hint.abs hf_abs ?_
            intro y
            change |W x y * f y| <= |f y|
            rw [abs_mul, abs_of_nonneg (hW.nonneg x y)]
            exact mul_le_of_le_one_left (abs_nonneg (f y)) (hW.le_one x y)

/-- The concrete `L²` vector represented by applying the pointwise graphon
kernel transform to an arbitrary `L²` vector. -/
def kernelOpL2OfL2 (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) :
    Lp Real 2 mu :=
  goodL2 (mu := mu) (good_kernelOp_l2 (mu := mu) hW f)

/-- On bounded representatives, the arbitrary-`L²` pointwise transform agrees
with the existing `Good`-representative transform. -/
lemma kernelOpL2OfL2_goodL2 (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    kernelOpL2OfL2 (mu := mu) hW (goodL2 (mu := mu) hf) =
      kernelOpL2OfGood (mu := mu) hW hf := by
  exact MemLp.toLp_congr
    (good_memLp_two
      (good_kernelOp_l2 (mu := mu) hW (goodL2 (mu := mu) hf)))
    (kernelOp_memLp_two hW hf)
    (ae_of_all _ fun x =>
      congrFun
        (kernelOpGoodK_congr_ae (mu := mu) (K := W)
          (goodL2_ae_eq (mu := mu) hf))
        x)

/-- The graphon-specific representative operator is the bounded-kernel
representative operator specialized to the same kernel. -/
lemma kernelOpL2OfGood_eq_kernelOpL2OfGoodK
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    kernelOpL2OfGood (mu := mu) hW hf =
      kernelOpL2OfGoodK (mu := mu) (goodK_of_isGraphon hW) hf := by
  apply MemLp.toLp_congr
  exact ae_of_all _ fun _ => rfl

/-- Pointwise `L¹` domination of the graphon kernel transform.  This is the
first pointwise bound: since `0 <= W <= 1`, each row integral is bounded
by the integral of `|f|`. -/
lemma abs_kernelOp_le_integral_abs (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    |kernelOp W mu f x| <= ∫ y, |f y| ∂mu := by
  calc
    |kernelOp W mu f x|
        <= ∫ y, |W x y * f y| ∂mu := by
          simpa [kernelOp] using
            (abs_integral_le_integral_abs
              (μ := mu) (f := fun y : Omega => W x y * f y))
    _ <= ∫ y, |f y| ∂mu := by
          refine integral_mono (integrable_Uf hW hf x).abs hf.integrable.abs ?_
          intro y
          change |W x y * f y| <= |f y|
          rw [abs_mul, abs_of_nonneg (hW.nonneg x y)]
          exact mul_le_of_le_one_left (abs_nonneg (f y)) (hW.le_one x y)

/-- Sharper pointwise domination by the graphon transform of the absolute
value.  This is the positivity-preserving inequality used in the Perron-type
orientation of the top compact eigenvalue. -/
lemma abs_kernelOp_le_kernelOp_abs (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    |kernelOp W mu f x| <=
      kernelOp W mu (fun y : Omega => |f y|) x := by
  calc
    |kernelOp W mu f x|
        <= ∫ y, |W x y * f y| ∂mu := by
          simpa [kernelOp] using
            (abs_integral_le_integral_abs
              (μ := mu) (f := fun y : Omega => W x y * f y))
    _ <= ∫ y, W x y * |f y| ∂mu := by
          refine integral_mono
            (integrable_Uf hW hf x).abs
            (integrable_Uf hW (good_abs hf) x) ?_
          intro y
          change |W x y * f y| <= W x y * |f y|
          rw [abs_mul, abs_of_nonneg (hW.nonneg x y)]

/-- The squared norm of the concrete L² kernel transform is the integral square
of the pointwise kernel transform. -/
lemma norm_kernelOpL2OfGood_sq_eq_integral_mul
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGood (mu := mu) hW hf‖ ^ 2 =
      ∫ x, kernelOp W mu f x * kernelOp W mu f x ∂mu := by
  rw [← norm_goodL2_sq_eq_integral_mul (mu := mu) (good_kernelOp hW hf)]
  rfl

/-- The pointwise kernel transform of a `Good` function has nonnegative
integral square. -/
lemma integral_kernelOp_mul_self_nonneg
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    0 <= ∫ x, kernelOp W mu f x * kernelOp W mu f x ∂mu := by
  rw [← norm_kernelOpL2OfGood_sq_eq_integral_mul (mu := mu) hW hf]
  positivity

/-- Squared-norm bound obtained from the pointwise `L¹` domination.  The
remaining step for the usual `L²` norm bound is the probability-space
inequality `(∫ |f|)^2 <= ∫ f^2`. -/
lemma norm_kernelOpL2OfGood_sq_le_integral_abs_sq
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGood (mu := mu) hW hf‖ ^ 2 <=
      (∫ y, |f y| ∂mu) ^ 2 := by
  rw [norm_kernelOpL2OfGood_sq_eq_integral_mul]
  let A : Real := ∫ y, |f y| ∂mu
  have hA0 : 0 <= A := by
    dsimp [A]
    exact integral_nonneg fun y => abs_nonneg (f y)
  have hmono :
      (∫ x, kernelOp W mu f x * kernelOp W mu f x ∂mu) <=
        ∫ _x : Omega, A * A ∂mu := by
    refine integral_mono
      ((good_kernelOp hW hf).mul (good_kernelOp hW hf)).integrable
      (integrable_const (A * A)) ?_
    intro x
    have hx : |kernelOp W mu f x| <= A := by
      simpa [A] using abs_kernelOp_le_integral_abs hW hf x
    calc
      kernelOp W mu f x * kernelOp W mu f x
          = |kernelOp W mu f x| * |kernelOp W mu f x| := by
            rw [← pow_two, ← pow_two, sq_abs]
      _ <= A * A :=
            mul_le_mul hx hx (abs_nonneg _) hA0
  calc
    (∫ x, kernelOp W mu f x * kernelOp W mu f x ∂mu)
        <= ∫ _x : Omega, A * A ∂mu := hmono
    _ = A ^ 2 := by simp [A, pow_two]

/-- Probability-space Cauchy: the square of the `L¹` norm of a bounded
measurable representative is bounded by its `L²` square. -/
lemma integral_abs_sq_le_integral_mul_self
    {f : Omega -> Real} (hf : Good f) :
    (∫ x, |f x| ∂mu) ^ 2 <= ∫ x, f x * f x ∂mu := by
  let h1 : Good (fun _ : Omega => (1 : Real)) := good_one (Ω := Omega)
  let habs : Good (fun x : Omega => |f x|) := good_abs hf
  have hcs :=
    real_inner_mul_inner_self_le
      (goodL2 (mu := mu) h1) (goodL2 (mu := mu) habs)
  have honeabs :
      inner Real (goodL2 (mu := mu) h1) (goodL2 (mu := mu) habs) =
        ∫ x, |f x| ∂mu := by
    rw [inner_goodL2_eq_integral_mul h1 habs]
    simp
  have honeone :
      inner Real (goodL2 (mu := mu) h1) (goodL2 (mu := mu) h1) =
        1 := by
    rw [inner_goodL2_eq_integral_mul h1 h1]
    simp
  have habsabs :
      inner Real (goodL2 (mu := mu) habs) (goodL2 (mu := mu) habs) =
        ∫ x, f x * f x ∂mu := by
    rw [inner_goodL2_eq_integral_mul habs habs]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change |f x| * |f x| = f x * f x
    rw [← pow_two, ← pow_two, sq_abs]
  rw [honeabs, honeone, habsabs] at hcs
  simpa [pow_two] using hcs

/-- Squared `L²` operator bound for a bounded measurable kernel. -/
lemma norm_kernelOpL2OfGoodK_sq_le_const_mul_norm_goodL2_sq
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ ^ 2 <=
      C ^ 2 * ‖goodL2 (mu := mu) hf‖ ^ 2 := by
  rw [norm_kernelOpL2OfGoodK_sq_eq_integral_mul]
  let A : Real := ∫ y, |f y| ∂mu
  have hA0 : 0 <= A := by
    dsimp [A]
    exact integral_nonneg fun y => abs_nonneg (f y)
  have hCA0 : 0 <= C * A := mul_nonneg hC0 hA0
  have hmono :
      (∫ x, kernelOp K mu f x * kernelOp K mu f x ∂mu) <=
        ∫ _x : Omega, (C * A) * (C * A) ∂mu := by
    refine integral_mono
      ((good_kernelOp_goodK (mu := mu) hK hf).mul
        (good_kernelOp_goodK (mu := mu) hK hf)).integrable
      (integrable_const ((C * A) * (C * A))) ?_
    intro x
    have hx : |kernelOp K mu f x| <= C * A := by
      simpa [A] using
        abs_kernelOpGoodK_le_const_integral_abs
          (mu := mu) hK hC0 hKC hf x
    calc
      kernelOp K mu f x * kernelOp K mu f x
          = |kernelOp K mu f x| * |kernelOp K mu f x| := by
            rw [← pow_two, ← pow_two, sq_abs]
      _ <= (C * A) * (C * A) :=
            mul_le_mul hx hx (abs_nonneg _) hCA0
  calc
    (∫ x, kernelOp K mu f x * kernelOp K mu f x ∂mu)
        <= ∫ _x : Omega, (C * A) * (C * A) ∂mu := hmono
    _ = (C * A) ^ 2 := by simp [pow_two]
    _ = C ^ 2 * A ^ 2 := by ring
    _ <= C ^ 2 * ‖goodL2 (mu := mu) hf‖ ^ 2 := by
          have hA := integral_abs_sq_le_integral_mul_self (mu := mu) hf
          rw [norm_goodL2_sq_eq_integral_mul (mu := mu) hf]
          exact mul_le_mul_of_nonneg_left hA (sq_nonneg C)

/-- Unsquared `L²` operator bound for a bounded measurable kernel. -/
lemma norm_kernelOpL2OfGoodK_le_const_mul_norm_goodL2
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ <=
      C * ‖goodL2 (mu := mu) hf‖ := by
  have hsq :=
    norm_kernelOpL2OfGoodK_sq_le_const_mul_norm_goodL2_sq
      (mu := mu) hK hC0 hKC hf
  have hsq' :
      ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ ^ 2 <=
        (C * ‖goodL2 (mu := mu) hf‖) ^ 2 := by
    simpa [mul_pow] using hsq
  have hrhs0 : 0 <= C * ‖goodL2 (mu := mu) hf‖ :=
    mul_nonneg hC0 (norm_nonneg _)
  exact le_of_sq_le_sq hsq' hrhs0

/-- Bounded-kernel transforms are Lipschitz in the input `L2` representative. -/
lemma norm_kernelOpL2OfGoodK_sub_le_const_mul_norm_goodL2_sub
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf -
        kernelOpL2OfGoodK (mu := mu) hK hg‖ <=
      C * ‖goodL2 (mu := mu) hf - goodL2 (mu := mu) hg‖ := by
  calc
    ‖kernelOpL2OfGoodK (mu := mu) hK hf -
        kernelOpL2OfGoodK (mu := mu) hK hg‖
        =
          ‖kernelOpL2OfGoodK (mu := mu) hK
            (good_sub hf hg)‖ := by
          rw [kernelOpL2OfGoodK_sub_input (mu := mu) hK hf hg]
    _ <=
        C * ‖goodL2 (mu := mu) (good_sub hf hg)‖ :=
          norm_kernelOpL2OfGoodK_le_const_mul_norm_goodL2
            (mu := mu) hK hC0 hKC (good_sub hf hg)
    _ =
        C * ‖goodL2 (mu := mu) hf - goodL2 (mu := mu) hg‖ := by
          rw [goodL2_sub (mu := mu) hf hg]

/-! ### Hilbert--Schmidt bounds for bounded kernels -/

/-- The iterated `L²` square mass of a concrete kernel.  This is the
Hilbert-Schmidt bound used for operator-norm approximation; it makes no
finite-spectrum assumption. -/
noncomputable def kernelSqNorm (mu : Measure Omega)
    (K : Omega -> Omega -> Real) : Real :=
  ∫ x, ∫ y, K x y * K x y ∂mu ∂mu

/-- The square of a bounded measurable kernel is integrable on the product
space. -/
lemma integrable_uncurry_mul_self_of_goodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    Integrable
      (fun p : Omega × Omega => K p.1 p.2 * K p.1 p.2)
      (mu.prod mu) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  have hSM : StronglyMeasurable
      (fun p : Omega × Omega => K p.1 p.2 * K p.1 p.2) :=
    hK.meas.stronglyMeasurable.mul hK.meas.stronglyMeasurable
  refine (integrable_const (C * C)).mono'
    hSM.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hC p.1 p.2) (hC p.1 p.2) (abs_nonneg _) hC0

/-- The project-side Hilbert-Schmidt square mass is the ordinary product-space
square integral. -/
lemma kernelSqNorm_eq_integral_prod_of_goodK {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    kernelSqNorm mu K =
      ∫ p : Omega × Omega, K p.1 p.2 * K p.1 p.2 ∂(mu.prod mu) := by
  rw [kernelSqNorm]
  exact (integral_prod
    (fun p : Omega × Omega => K p.1 p.2 * K p.1 p.2)
    (integrable_uncurry_mul_self_of_goodK (mu := mu) hK)).symm

/-- A bounded measurable kernel is an `L²` function on the product space. -/
lemma goodK_memLp_prod_two {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    MemLp (Function.uncurry K) 2 (mu.prod mu) := by
  obtain ⟨C, _hC0, hC⟩ := hK.bdd
  exact MemLp.of_bound (μ := mu.prod mu) hK.meas.aestronglyMeasurable C
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact hC p.1 p.2)

/-- Real-valued `L²` seminorm as the square root of the square integral. -/
lemma lpNorm_two_eq_sqrt_integral_sq
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α -> Real} (hf : AEStronglyMeasurable f ν) :
    lpNorm f 2 ν = Real.sqrt (∫ x, f x * f x ∂ν) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ENNReal)) (by norm_num) (by simp) hf]
  rw [Real.sqrt_eq_rpow]
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp [Real.norm_eq_abs, abs_mul_abs_self, sq]
  · norm_num

/-- Small square integral implies small real-valued `L²` seminorm. -/
lemma lpNorm_two_lt_of_integral_sq_lt
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α -> Real} (hf : AEStronglyMeasurable f ν)
    {ε : Real} (hε : 0 < ε)
    (hsmall : (∫ x, f x * f x ∂ν) < ε ^ 2) :
    lpNorm f 2 ν < ε := by
  rw [lpNorm_two_eq_sqrt_integral_sq hf]
  exact (Real.sqrt_lt
    (integral_nonneg fun x => mul_self_nonneg (f x))
    hε.le).2 hsmall

/-- The Mathlib `L²` seminorm of a bounded kernel on the product space is the
square root of the project-side Hilbert-Schmidt square mass. -/
lemma lpNorm_uncurry_two_eq_sqrt_kernelSqNorm_of_goodK
    {K : Omega -> Omega -> Real} (hK : GoodK K) :
    lpNorm (Function.uncurry K) 2 (mu.prod mu) =
      Real.sqrt (kernelSqNorm mu K) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ENNReal)) (by norm_num) (by simp)
    (goodK_memLp_prod_two (mu := mu) hK).aestronglyMeasurable]
  rw [kernelSqNorm_eq_integral_prod_of_goodK (mu := mu) hK,
    Real.sqrt_eq_rpow]
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun p => by
      simp [Function.uncurry, Real.norm_eq_abs, abs_mul_abs_self, sq]
  · norm_num

/-- Difference form of `lpNorm_uncurry_two_eq_sqrt_kernelSqNorm_of_goodK`. -/
lemma lpNorm_uncurry_sub_two_eq_sqrt_kernelSqNorm_sub_of_goodK
    {K L : Omega -> Omega -> Real} (hK : GoodK K) (hL : GoodK L) :
    lpNorm (Function.uncurry K - Function.uncurry L) 2 (mu.prod mu) =
      Real.sqrt (kernelSqNorm mu (fun x y => K x y - L x y)) := by
  calc
    lpNorm (Function.uncurry K - Function.uncurry L) 2 (mu.prod mu)
        =
      lpNorm (Function.uncurry (fun x y => K x y - L x y)) 2 (mu.prod mu) := by
        rfl
    _ =
      Real.sqrt (kernelSqNorm mu (fun x y => K x y - L x y)) :=
        lpNorm_uncurry_two_eq_sqrt_kernelSqNorm_of_goodK
          (mu := mu) (goodK_sub hK hL)

/-- General `L²` simple-function approximation for bounded measurable
kernels, stated on the product space.

The next graphon-specific step is to replace each simple-function level set
by finite unions of measurable rectangles, using the rectangle semiring
approximation in `Kernel.lean`. -/
lemma exists_simpleFunc_eLpNorm_uncurry_sub_lt_of_goodK
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ S : SimpleFunc (Omega × Omega) Real,
      eLpNorm (Function.uncurry K - ⇑S) 2 (mu.prod mu) < ε ∧
        MemLp S 2 (mu.prod mu) := by
  have htop := ENNReal.ofNat_ne_top (n := 2)
  exact (goodK_memLp_prod_two (mu := mu) hK).exists_simpleFunc_eLpNorm_sub_lt
    htop hε

/-- Real-valued `L²` simple-function approximation for bounded measurable
kernels on the product space. -/
lemma exists_simpleFunc_lpNorm_uncurry_sub_lt_of_goodK
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {δ : Real} (hδ : 0 < δ) :
    ∃ S : SimpleFunc (Omega × Omega) Real,
      lpNorm (Function.uncurry K - ⇑S) 2 (mu.prod mu) < δ ∧
        MemLp S 2 (mu.prod mu) := by
  rcases exists_simpleFunc_eLpNorm_uncurry_sub_lt_of_goodK
      (mu := mu) hK (ε := ENNReal.ofReal δ)
      (ENNReal.ofReal_ne_zero_iff.mpr hδ) with ⟨S, hSlt, hSmem⟩
  refine ⟨S, ?_, hSmem⟩
  have hSM :
      AEStronglyMeasurable (Function.uncurry K - ⇑S) (mu.prod mu) :=
    (goodK_memLp_prod_two (mu := mu) hK).aestronglyMeasurable.sub
      hSmem.aestronglyMeasurable
  rw [← MeasureTheory.toReal_eLpNorm hSM]
  exact ENNReal.toReal_lt_of_lt_ofReal hSlt

/-- A bounded measurable kernel is an `L²(mu × mu)` limit, in one-step
epsilon form, of exact finite separable kernels.

The proof first approximates the kernel by a simple function on `Omega ×
Omega`, then replaces each simple-function atom by a finite union of
measurable rectangles.  The latter rectangle-step function is an exact finite
sum of separated one-variable factors. -/
lemma exists_finiteRank_kernel_lpNorm_uncurry_sub_lt_of_goodK
    {K0 : Omega -> Omega -> Real} (hK0 : GoodK K0)
    {ε : Real} (hε : 0 < ε) :
    ∃ J : Type u, ∃ hJ : Fintype J,
    ∃ K : Omega -> Omega -> Real, ∃ B : Real,
    ∃ a b : J -> Omega -> Real,
      GoodK K ∧
      0 ≤ B ∧
      (∀ x y, |K x y| ≤ B) ∧
      (∀ j, Good (a j)) ∧
      (∀ j, Good (b j)) ∧
      (∀ x y, K x y = (@Finset.univ J hJ).sum
        (fun j : J => a j x * b j y)) ∧
      lpNorm (Function.uncurry K - Function.uncurry K0) 2 (mu.prod mu) < ε := by
  classical
  have hhalf : 0 < ε / 2 := by linarith
  rcases exists_simpleFunc_lpNorm_uncurry_sub_lt_of_goodK
      (mu := mu) hK0 hhalf with
    ⟨S, hSlt, hSmem⟩
  let A : Real :=
    ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
      ((SimpleFunc.range S).card : Real)
  let η : Real := (ε / 2) ^ 2 / (A + 1)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hA1 : 0 < A + 1 := by linarith
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (sq_pos_of_pos hhalf) hA1
  rcases exists_simpleFunc_rectangular_finiteRank_data_integral_sq_bound
      (Ω := Omega) mu S hη with
    ⟨J, hJ, K, B, a, b, hK, hB0, hKB, ha, hb, -, -, hsep, hInt⟩
  have hCoeff_lt :
      ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
          ((SimpleFunc.range S).card * η) < (ε / 2) ^ 2 := by
    have hmain : A * ((ε / 2) ^ 2 / (A + 1)) < (ε / 2) ^ 2 := by
      rw [show A * ((ε / 2) ^ 2 / (A + 1)) =
          A * (ε / 2) ^ 2 / (A + 1) by ring]
      rw [div_lt_iff₀ hA1]
      nlinarith [sq_pos_of_pos hhalf]
    dsimp [η]
    rw [show ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
          ((SimpleFunc.range S).card *
            ((ε / 2) ^ 2 / (A + 1))) =
        A * ((ε / 2) ^ 2 / (A + 1)) by
          dsimp [A]
          ring]
    exact hmain
  have hInt_lt :
      (∫ p : Omega × Omega, (S p - K p.1 p.2) ^ 2 ∂(mu.prod mu))
        < (ε / 2) ^ 2 :=
    lt_of_le_of_lt hInt hCoeff_lt
  have hRectLp :
      lpNorm (fun p : Omega × Omega => S p - K p.1 p.2) 2 (mu.prod mu) < ε / 2 := by
    have hSM :
        AEStronglyMeasurable
          (fun p : Omega × Omega => S p - K p.1 p.2) (mu.prod mu) :=
      hSmem.aestronglyMeasurable.sub
        (goodK_memLp_prod_two (mu := mu) hK).aestronglyMeasurable
    refine lpNorm_two_lt_of_integral_sq_lt (ν := mu.prod mu) hSM hhalf ?_
    simpa [pow_two] using hInt_lt
  have hKmem : MemLp (Function.uncurry K) 2 (mu.prod mu) :=
    goodK_memLp_prod_two (mu := mu) hK
  have htri :
      lpNorm (Function.uncurry K - Function.uncurry K0) 2 (mu.prod mu) ≤
        lpNorm (Function.uncurry K - (S : Omega × Omega -> Real)) 2 (mu.prod mu) +
          lpNorm ((S : Omega × Omega -> Real) - Function.uncurry K0) 2 (mu.prod mu) := by
    exact lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub
      (μ := mu.prod mu) (p := (2 : ENNReal))
      (f := Function.uncurry K) (g := (S : Omega × Omega -> Real))
      (h := Function.uncurry K0)
      hKmem hSmem (by norm_num)
  have hKS :
      lpNorm (Function.uncurry K - (S : Omega × Omega -> Real)) 2 (mu.prod mu) <
        ε / 2 := by
    rw [MeasureTheory.lpNorm_sub_comm]
    change lpNorm (fun p : Omega × Omega => S p - K p.1 p.2) 2
      (mu.prod mu) < ε / 2
    exact hRectLp
  have hSW :
      lpNorm ((S : Omega × Omega -> Real) - Function.uncurry K0) 2 (mu.prod mu) <
        ε / 2 := by
    simpa [MeasureTheory.lpNorm_sub_comm] using hSlt
  refine ⟨J, hJ, K, B, a, b, hK, hB0, hKB, ha, hb, hsep, ?_⟩
  calc
    lpNorm (Function.uncurry K - Function.uncurry K0) 2 (mu.prod mu)
        ≤ lpNorm (Function.uncurry K - (S : Omega × Omega -> Real)) 2 (mu.prod mu) +
          lpNorm ((S : Omega × Omega -> Real) - Function.uncurry K0) 2
            (mu.prod mu) := htri
    _ < ε := by linarith

/-- Hilbert-Schmidt square-root form of
`exists_finiteRank_kernel_lpNorm_uncurry_sub_lt_of_goodK`. -/
lemma exists_finiteRank_kernel_sqrt_kernelSqNorm_sub_lt_of_goodK
    {K0 : Omega -> Omega -> Real} (hK0 : GoodK K0)
    {ε : Real} (hε : 0 < ε) :
    ∃ J : Type u, ∃ hJ : Fintype J,
    ∃ K : Omega -> Omega -> Real, ∃ B : Real,
    ∃ a b : J -> Omega -> Real,
      GoodK K ∧
      0 ≤ B ∧
      (∀ x y, |K x y| ≤ B) ∧
      (∀ j, Good (a j)) ∧
      (∀ j, Good (b j)) ∧
      (∀ x y, K x y = (@Finset.univ J hJ).sum
        (fun j : J => a j x * b j y)) ∧
      Real.sqrt (kernelSqNorm mu (fun x y => K x y - K0 x y)) < ε := by
  rcases exists_finiteRank_kernel_lpNorm_uncurry_sub_lt_of_goodK
      (mu := mu) hK0 hε with
    ⟨J, hJ, K, B, a, b, hK, hB0, hKB, ha, hb, hsep, hlt⟩
  refine ⟨J, hJ, K, B, a, b, hK, hB0, hKB, ha, hb, hsep, ?_⟩
  rw [← lpNorm_uncurry_sub_two_eq_sqrt_kernelSqNorm_sub_of_goodK
    (mu := mu) hK hK0]
  exact hlt

/-- Each row of a bounded measurable kernel is a bounded measurable
representative. -/
lemma goodK_row {K : Omega -> Omega -> Real}
    (hK : GoodK K) (x : Omega) :
    Good (fun y => K x y) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  exact ⟨(hK.meas.comp measurable_prodMk_left).stronglyMeasurable,
    C, hC0, fun y => hC x y⟩

/-- The row-square integral of a bounded measurable kernel is again a bounded
measurable representative. -/
lemma good_kernelSqRow {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    Good (fun x => ∫ y, K x y * K x y ∂mu) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  refine ⟨?_, C * C, mul_nonneg hC0 hC0, ?_⟩
  · have hSM :
        StronglyMeasurable
          (fun p : Omega × Omega => K p.1 p.2 * K p.1 p.2) :=
      hK.meas.stronglyMeasurable.mul hK.meas.stronglyMeasurable
    exact hSM.integral_prod_right'
  · intro x
    have hrow : Good (fun y => K x y) := goodK_row hK x
    calc
      |∫ y, K x y * K x y ∂mu|
          <= ∫ y, |K x y * K x y| ∂mu := abs_integral_le_integral_abs
      _ <= ∫ _y : Omega, C * C ∂mu := by
          refine integral_mono (hrow.mul hrow).integrable.abs
            (integrable_const (C * C)) ?_
          intro y
          change |K x y * K x y| <= C * C
          rw [abs_mul]
          exact mul_le_mul (hC x y) (hC x y) (abs_nonneg _) hC0
      _ = C * C := by simp

/-- The kernel square mass is nonnegative. -/
lemma kernelSqNorm_nonneg {K : Omega -> Omega -> Real} :
    0 <= kernelSqNorm mu K := by
  unfold kernelSqNorm
  exact integral_nonneg fun x =>
    integral_nonneg fun y => mul_self_nonneg (K x y)

/-- For a symmetric kernel, the two-step cyclic trace is exactly the
Hilbert-Schmidt square mass of the kernel.

This is an exact integral identity, not a spectral assertion: `trace (K ∘ K)`
unfolds to `∫ x ∫ y, K x y * K y x`, and symmetry turns it into the square
mass `∫ x ∫ y, K x y * K x y`. -/
lemma trace_compPow_one_eq_kernelSqNorm_of_symm
    {K : Omega -> Omega -> Real}
    (hsymm : forall x y, K x y = K y x) :
    trace mu (compPow mu K 1) = kernelSqNorm mu K := by
  unfold trace compPow comp kernelSqNorm
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp [compPow, hsymm y x]

/-- The graphon two-step cyclic trace is the Hilbert-Schmidt square mass of
the graphon kernel. -/
lemma trace_compPow_one_eq_kernelSqNorm
    (hW : IsGraphon W mu) :
    trace mu (compPow mu W 1) = kernelSqNorm mu W :=
  trace_compPow_one_eq_kernelSqNorm_of_symm (mu := mu) hW.symm

/-- Rowwise Cauchy-Schwarz for a bounded measurable kernel applied to a
bounded representative. -/
lemma kernelOpGoodK_apply_mul_self_le_rowSq_mul_integral
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    kernelOp K mu f x * kernelOp K mu f x <=
      (∫ y, K x y * K x y ∂mu) * (∫ y, f y * f y ∂mu) := by
  let hrow : Good (fun y => K x y) := goodK_row hK x
  have hcs :=
    real_inner_mul_inner_self_le
      (goodL2 (mu := mu) hrow) (goodL2 (mu := mu) hf)
  have hrowf :
      inner Real (goodL2 (mu := mu) hrow) (goodL2 (mu := mu) hf) =
        ∫ y, K x y * f y ∂mu := by
    exact inner_goodL2_eq_integral_mul hrow hf
  have hrowrow :
      inner Real (goodL2 (mu := mu) hrow) (goodL2 (mu := mu) hrow) =
        ∫ y, K x y * K x y ∂mu := by
    exact inner_goodL2_eq_integral_mul hrow hrow
  have hff :
      inner Real (goodL2 (mu := mu) hf) (goodL2 (mu := mu) hf) =
        ∫ y, f y * f y ∂mu := by
    exact inner_goodL2_eq_integral_mul hf hf
  rw [hrowf, hrowrow, hff] at hcs
  simpa [kernelOp] using hcs

/-- Hilbert--Schmidt squared-norm bound on bounded representatives. -/
lemma norm_kernelOpL2OfGoodK_sq_le_kernelSqNorm_mul_norm_goodL2_sq
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ ^ 2 <=
      kernelSqNorm mu K * ‖goodL2 (mu := mu) hf‖ ^ 2 := by
  rw [norm_kernelOpL2OfGoodK_sq_eq_integral_mul]
  let B : Real := ∫ y, f y * f y ∂mu
  have hBnorm : B = ‖goodL2 (mu := mu) hf‖ ^ 2 := by
    rw [norm_goodL2_sq_eq_integral_mul (mu := mu) hf]
  have hmono :
      (∫ x, kernelOp K mu f x * kernelOp K mu f x ∂mu) <=
        ∫ x, (∫ y, K x y * K x y ∂mu) * B ∂mu := by
    refine integral_mono
      ((good_kernelOp_goodK (mu := mu) hK hf).mul
        (good_kernelOp_goodK (mu := mu) hK hf)).integrable
      ((good_kernelSqRow (mu := mu) hK).integrable.mul_const B) ?_
    intro x
    simpa [B] using
      kernelOpGoodK_apply_mul_self_le_rowSq_mul_integral
        (mu := mu) hK hf x
  calc
    (∫ x, kernelOp K mu f x * kernelOp K mu f x ∂mu)
        <= ∫ x, (∫ y, K x y * K x y ∂mu) * B ∂mu := hmono
    _ = (∫ x, ∫ y, K x y * K x y ∂mu ∂mu) * B := by
          rw [integral_mul_const]
    _ = kernelSqNorm mu K * ‖goodL2 (mu := mu) hf‖ ^ 2 := by
          simp [kernelSqNorm, hBnorm]

/-- A bounded-kernel row paired with a bounded representative is the pointwise
kernel transform. -/
lemma inner_goodK_row_goodL2_eq_kernelOp
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) (x : Omega) :
    inner Real (goodL2 (mu := mu) (goodK_row hK x))
        (goodL2 (mu := mu) hf) =
      kernelOp K mu f x := by
  exact inner_goodL2_eq_integral_mul (goodK_row hK x) hf

/-- A bounded-kernel row paired with an arbitrary `L²` vector is the
pointwise integral against that `L²` representative. -/
lemma inner_goodK_row_l2_eq_kernelOp
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    (f : Lp Real 2 mu) (x : Omega) :
    inner Real (goodL2 (mu := mu) (goodK_row hK x)) f =
      kernelOp K mu (fun y : Omega => f y) x := by
  rw [MeasureTheory.L2.inner_def]
  have hrowae := goodL2_ae_eq (mu := mu) (goodK_row hK x)
  refine integral_congr_ae ?_
  filter_upwards [hrowae] with y hy
  rw [hy]
  simp [RCLike.inner_apply, mul_comm]

/-- Finite row-coordinate square sums for arbitrary `L²` modes are
integrable for graphon rows. -/
lemma integrable_sum_graphon_row_inner_l2_sq
    (hW : IsGraphon W mu)
    (mode : Nat -> Lp Real 2 mu)
    (s : Finset Nat) :
    Integrable (fun x : Omega =>
      s.sum (fun n : Nat =>
        inner Real
          (goodL2 (mu := mu) (goodK_row (goodK_of_isGraphon hW) x))
          (mode n) ^ 2)) mu := by
  refine integrable_finsetSum s ?_
  intro n hn
  have hgood : Good (fun x : Omega =>
      kernelOp W mu (fun y : Omega => mode n y) x *
        kernelOp W mu (fun y : Omega => mode n y) x) :=
    (good_kernelOp_l2 (mu := mu) hW (mode n)).mul
      (good_kernelOp_l2 (mu := mu) hW (mode n))
  refine hgood.integrable.congr ?_
  exact ae_of_all _ fun x => by
    change
      kernelOp W mu (fun y : Omega => mode n y) x *
          kernelOp W mu (fun y : Omega => mode n y) x =
        inner Real
          (goodL2 (mu := mu) (goodK_row (goodK_of_isGraphon hW) x))
          (mode n) ^ 2
    rw [inner_goodK_row_l2_eq_kernelOp
      (mu := mu) (goodK_of_isGraphon hW) (mode n) x]
    ring

/-- Finite row-energy identity for bounded representatives.

This is the exact Hilbert-Schmidt calculation on the dense bounded layer:
the finite sum of output energies equals the integral of the finite row
coordinate square sum. -/
lemma sum_norm_kernelOpL2OfGoodK_sq_eq_integral_sum_row_inner_sq
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Nat -> Omega -> Real} (hf : ∀ n : Nat, Good (f n))
    (s : Finset Nat) :
    s.sum (fun n : Nat => ‖kernelOpL2OfGoodK (mu := mu) hK (hf n)‖ ^ 2) =
      ∫ x, s.sum (fun n : Nat =>
        inner Real (goodL2 (mu := mu) (goodK_row hK x))
            (goodL2 (mu := mu) (hf n)) ^ 2) ∂mu := by
  have hterm_integrable :
      ∀ n ∈ s, Integrable (fun x : Omega =>
        inner Real (goodL2 (mu := mu) (goodK_row hK x))
            (goodL2 (mu := mu) (hf n)) ^ 2) mu := by
    intro n hn
    have hgood : Good (fun x : Omega => kernelOp K mu (f n) x * kernelOp K mu (f n) x) :=
      (good_kernelOp_goodK (mu := mu) hK (hf n)).mul
        (good_kernelOp_goodK (mu := mu) hK (hf n))
    refine hgood.integrable.congr ?_
    exact ae_of_all _ fun x => by
      change kernelOp K mu (f n) x * kernelOp K mu (f n) x =
        inner Real (goodL2 (mu := mu) (goodK_row hK x))
            (goodL2 (mu := mu) (hf n)) ^ 2
      rw [inner_goodK_row_goodL2_eq_kernelOp (mu := mu) hK (hf n) x]
      ring
  rw [integral_finsetSum s hterm_integrable]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [norm_kernelOpL2OfGoodK_sq_eq_integral_mul (mu := mu) hK (hf n)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change kernelOp K mu (f n) x * kernelOp K mu (f n) x =
    inner Real (goodL2 (mu := mu) (goodK_row hK x))
        (goodL2 (mu := mu) (hf n)) ^ 2
  rw [inner_goodK_row_goodL2_eq_kernelOp (mu := mu) hK (hf n) x]
  ring

/-- Finite row-coordinate square sums for bounded representatives are
integrable. -/
lemma integrable_sum_goodK_row_inner_sq
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Nat -> Omega -> Real} (hf : ∀ n : Nat, Good (f n))
    (s : Finset Nat) :
    Integrable (fun x : Omega =>
      s.sum (fun n : Nat =>
        inner Real (goodL2 (mu := mu) (goodK_row hK x))
            (goodL2 (mu := mu) (hf n)) ^ 2)) mu := by
  refine integrable_finsetSum s ?_
  intro n hn
  have hgood : Good (fun x : Omega => kernelOp K mu (f n) x * kernelOp K mu (f n) x) :=
    (good_kernelOp_goodK (mu := mu) hK (hf n)).mul
      (good_kernelOp_goodK (mu := mu) hK (hf n))
  refine hgood.integrable.congr ?_
  exact ae_of_all _ fun x => by
    change kernelOp K mu (f n) x * kernelOp K mu (f n) x =
      inner Real (goodL2 (mu := mu) (goodK_row hK x))
          (goodL2 (mu := mu) (hf n)) ^ 2
    rw [inner_goodK_row_goodL2_eq_kernelOp (mu := mu) hK (hf n) x]
    ring

/-- The row self-inner-product of a bounded kernel is integrable. -/
lemma integrable_goodK_row_inner_self
    {K : Omega -> Omega -> Real} (hK : GoodK K) :
    Integrable (fun x : Omega =>
      inner Real (goodL2 (mu := mu) (goodK_row hK x))
        (goodL2 (mu := mu) (goodK_row hK x))) mu := by
  refine (good_kernelSqRow (mu := mu) hK).integrable.congr ?_
  exact ae_of_all _ fun x => by
    change (∫ y, K x y * K x y ∂mu) =
      inner Real (goodL2 (mu := mu) (goodK_row hK x))
        (goodL2 (mu := mu) (goodK_row hK x))
    rw [inner_goodL2_eq_integral_mul (goodK_row hK x) (goodK_row hK x)]

/-- Integrating the row self-inner-products gives the kernel square mass. -/
lemma integral_goodK_row_inner_self_eq_kernelSqNorm
    {K : Omega -> Omega -> Real} (hK : GoodK K) :
    (∫ x, inner Real (goodL2 (mu := mu) (goodK_row hK x))
        (goodL2 (mu := mu) (goodK_row hK x)) ∂mu) =
      kernelSqNorm mu K := by
  unfold kernelSqNorm
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change inner Real (goodL2 (mu := mu) (goodK_row hK x))
      (goodL2 (mu := mu) (goodK_row hK x)) =
    ∫ y, K x y * K x y ∂mu
  rw [inner_goodL2_eq_integral_mul (goodK_row hK x) (goodK_row hK x)]

/-- Hilbert--Schmidt norm bound on bounded representatives. -/
lemma norm_kernelOpL2OfGoodK_le_sqrt_kernelSqNorm_mul_norm_goodL2
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ <=
      Real.sqrt (kernelSqNorm mu K) * ‖goodL2 (mu := mu) hf‖ := by
  have hsq :=
    norm_kernelOpL2OfGoodK_sq_le_kernelSqNorm_mul_norm_goodL2_sq
      (mu := mu) hK hf
  have hsq' :
      ‖kernelOpL2OfGoodK (mu := mu) hK hf‖ ^ 2 <=
        (Real.sqrt (kernelSqNorm mu K) *
          ‖goodL2 (mu := mu) hf‖) ^ 2 := by
    simpa [mul_pow, Real.sq_sqrt (kernelSqNorm_nonneg (mu := mu) (K := K))]
      using hsq
  exact le_of_sq_le_sq hsq'
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

/-- The graphon kernel transform has operator norm at most one on bounded measurable
representatives.  This is the concrete norm bound needed before promoting the
kernel to an operator on the quotient space. -/
lemma norm_kernelOpL2OfGood_sq_le_norm_goodL2_sq
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGood (mu := mu) hW hf‖ ^ 2 <=
      ‖goodL2 (mu := mu) hf‖ ^ 2 := by
  calc
    ‖kernelOpL2OfGood (mu := mu) hW hf‖ ^ 2
        <= (∫ y, |f y| ∂mu) ^ 2 :=
          norm_kernelOpL2OfGood_sq_le_integral_abs_sq hW hf
    _ <= ∫ y, f y * f y ∂mu :=
          integral_abs_sq_le_integral_mul_self (mu := mu) hf
    _ = ‖goodL2 (mu := mu) hf‖ ^ 2 := by
          rw [norm_goodL2_sq_eq_integral_mul]

/-- Unsquared form of the concrete `L²` norm bound. -/
lemma norm_kernelOpL2OfGood_le_norm_goodL2
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    ‖kernelOpL2OfGood (mu := mu) hW hf‖ <=
      ‖goodL2 (mu := mu) hf‖ := by
  exact le_of_sq_le_sq
    (norm_kernelOpL2OfGood_sq_le_norm_goodL2_sq hW hf)
    (norm_nonneg _)

/-- The pointwise kernel transform respects almost-everywhere equality of
representatives.  This is the quotient-stability fact needed before the kernel
can be promoted to an operator on `Lp`. -/
lemma kernelOp_congr_ae {f g : Omega -> Real}
    (hfg : f =ᵐ[mu] g) :
    kernelOp W mu f = kernelOp W mu g := by
  funext x
  simp only [kernelOp]
  refine integral_congr_ae ?_
  filter_upwards [hfg] with y hy
  rw [hy]

/-- The `L²` kernel transform of `Good` representatives is independent of the
chosen almost-everywhere representative. -/
lemma kernelOpL2OfGood_congr (hW : IsGraphon W mu)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g)
    (hfg : f =ᵐ[mu] g) :
    kernelOpL2OfGood (mu := mu) hW hf =
      kernelOpL2OfGood (mu := mu) hW hg := by
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => congrFun (kernelOp_congr_ae (mu := mu) (W := W) hfg) x

/-- A `Good` representative that is zero almost everywhere has zero kernel
transform as an `L²` vector. -/
lemma kernelOpL2OfGood_eq_zero_of_ae_eq_zero (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f)
    (hf0 : f =ᵐ[mu] fun _ : Omega => (0 : Real)) :
    kernelOpL2OfGood (mu := mu) hW hf = 0 := by
  have hcongr :=
    kernelOpL2OfGood_congr (mu := mu) hW hf (good_zero (Omega := Omega)) hf0
  have hzero : kernelOp W mu (fun _ : Omega => (0 : Real)) =
      fun _ : Omega => (0 : Real) := by
    funext x
    simp [kernelOp]
  rw [hcongr]
  calc
    kernelOpL2OfGood (mu := mu) hW (good_zero (Omega := Omega))
        = (good_memLp_two (good_zero (Omega := Omega))).toLp
            (fun _ : Omega => (0 : Real)) := by
          exact MemLp.toLp_congr
            (kernelOp_memLp_two hW (good_zero (Omega := Omega)))
            (good_memLp_two (good_zero (Omega := Omega)))
            (ae_of_all _ fun x => congrFun hzero x)
    _ = 0 := MemLp.toLp_zero _

/-- Additivity of the L² graphon kernel transform on `Good` representatives. -/
lemma kernelOpL2OfGood_add (hW : IsGraphon W mu)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    kernelOpL2OfGood (mu := mu) hW (good_add hf hg) =
      kernelOpL2OfGood (mu := mu) hW hf +
        kernelOpL2OfGood (mu := mu) hW hg := by
  calc
    kernelOpL2OfGood (mu := mu) hW (good_add hf hg)
        =
          ((kernelOp_memLp_two hW hf).add (kernelOp_memLp_two hW hg)).toLp
            (kernelOp W mu f + kernelOp W mu g) := by
          exact MemLp.toLp_congr
            (kernelOp_memLp_two hW (good_add hf hg))
            ((kernelOp_memLp_two hW hf).add (kernelOp_memLp_two hW hg))
            (ae_of_all _ fun x => kernelOp_add' hW hf hg x)
    _ =
      kernelOpL2OfGood (mu := mu) hW hf +
        kernelOpL2OfGood (mu := mu) hW hg := by
          exact MemLp.toLp_add
            (kernelOp_memLp_two hW hf) (kernelOp_memLp_two hW hg)

/-- Homogeneity of the L² graphon kernel transform on `Good` representatives. -/
lemma kernelOpL2OfGood_smul (hW : IsGraphon W mu)
    (c : Real) {f : Omega -> Real} (hf : Good f) :
    kernelOpL2OfGood (mu := mu) hW (good_smul c hf) =
      c • kernelOpL2OfGood (mu := mu) hW hf := by
  calc
    kernelOpL2OfGood (mu := mu) hW (good_smul c hf)
        =
          ((kernelOp_memLp_two hW hf).const_smul c).toLp
            (c • kernelOp W mu f) := by
          exact MemLp.toLp_congr
            (kernelOp_memLp_two hW (good_smul c hf))
            ((kernelOp_memLp_two hW hf).const_smul c)
            (ae_of_all _ fun x => kernelOp_smul' (U := W) (μ := mu) c f x)
    _ = c • kernelOpL2OfGood (mu := mu) hW hf := by
          exact MemLp.toLp_const_smul c (kernelOp_memLp_two hW hf)

/-- The canonical simple-function representative of an `Lp` simple function is
`Good`: simple functions are bounded and strongly measurable. -/
lemma simpleFunc_good (s : Lp.simpleFunc Real 2 mu) :
    Good (Lp.simpleFunc.toSimpleFunc s) := by
  obtain ⟨C, hC⟩ :=
    SimpleFunc.exists_forall_norm_le (Lp.simpleFunc.toSimpleFunc s)
  refine ⟨Lp.simpleFunc.stronglyMeasurable s,
    ⟨max C 0, le_max_right _ _, fun x => ?_⟩⟩
  have hx : |Lp.simpleFunc.toSimpleFunc s x| <= C := by
    simpa [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_left _ _)

/-- Our `Good`-representative embedding agrees with Mathlib's dense embedding
of `Lp.simpleFunc` into `Lp`. -/
lemma goodL2_simpleFunc_eq_coe (s : Lp.simpleFunc Real 2 mu) :
    goodL2 (mu := mu) (simpleFunc_good (mu := mu) s) =
      (s : Lp Real 2 mu) := by
  calc
    goodL2 (mu := mu) (simpleFunc_good (mu := mu) s)
        =
          (Lp.simpleFunc.memLp s).toLp (Lp.simpleFunc.toSimpleFunc s) := by
          exact MemLp.toLp_congr
            (good_memLp_two (simpleFunc_good (mu := mu) s))
            (Lp.simpleFunc.memLp s)
            (ae_of_all _ fun _ => rfl)
    _ = (s : Lp Real 2 mu) := by
          have h :=
            congrArg (fun t : Lp.simpleFunc Real 2 mu => (t : Lp Real 2 mu))
              (Lp.simpleFunc.toLp_toSimpleFunc s)
          simpa using h

/-- The range of `Good` representatives is dense in `L²`: it contains the
dense subspace of `Lp.simpleFunc` representatives. -/
lemma denseRange_goodL2 :
    DenseRange
      (fun f : {f : Omega -> Real // Good f} =>
        goodL2 (mu := mu) f.property) := by
  have hsimple :
      DenseRange
        (fun s : Lp.simpleFunc Real 2 mu => (s : Lp Real 2 mu)) :=
    Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
      (by norm_num)
  intro x
  refine closure_mono ?_ (hsimple x)
  intro y hy
  rcases hy with ⟨s, rfl⟩
  refine ⟨⟨Lp.simpleFunc.toSimpleFunc s, simpleFunc_good (mu := mu) s⟩, ?_⟩
  change goodL2 (mu := mu) (simpleFunc_good (mu := mu) s) =
    (s : Lp Real 2 mu)
  exact goodL2_simpleFunc_eq_coe (mu := mu) s

/-- The graphon kernel transform on the dense simple-function subspace, with
values in the ambient `L²` space. -/
def kernelOpSimple (hW : IsGraphon W mu)
    (s : Lp.simpleFunc Real 2 mu) :
    Lp Real 2 mu :=
  kernelOpL2OfGood (mu := mu) hW (simpleFunc_good (mu := mu) s)

local instance simpleFuncSMul :
    SMul Real (Lp.simpleFunc Real 2 mu) :=
  Lp.simpleFunc.smul

local instance simpleFuncModule :
    Module Real (Lp.simpleFunc Real 2 mu) :=
  Lp.simpleFunc.module

local instance simpleFuncBoundedSMul :
    IsBoundedSMul Real (Lp.simpleFunc Real 2 mu) :=
  Lp.simpleFunc.isBoundedSMul

local instance simpleFuncNormedSpace :
    NormedSpace Real (Lp.simpleFunc Real 2 mu) :=
  Lp.simpleFunc.normedSpace

/-- A bounded measurable kernel acting on the dense simple-function subspace,
with values in ambient `L²`. -/
def kernelOpGoodKSimple {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    (s : Lp.simpleFunc Real 2 mu) :
    Lp Real 2 mu :=
  kernelOpL2OfGoodK (mu := mu) hK (simpleFunc_good (mu := mu) s)

/-- The graphon simple-function operator is the bounded-kernel simple-function
operator specialized to the same kernel. -/
lemma kernelOpSimple_eq_kernelOpGoodKSimple
    (hW : IsGraphon W mu)
    (s : Lp.simpleFunc Real 2 mu) :
    kernelOpSimple (mu := mu) hW s =
      kernelOpGoodKSimple (mu := mu) (goodK_of_isGraphon hW) s := by
  simpa [kernelOpSimple, kernelOpGoodKSimple] using
    kernelOpL2OfGood_eq_kernelOpL2OfGoodK
      (mu := mu) hW (simpleFunc_good (mu := mu) s)

/-- Additivity of the bounded-kernel transform on `Lp.simpleFunc`. -/
lemma kernelOpGoodKSimple_add {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    (s t : Lp.simpleFunc Real 2 mu) :
    kernelOpGoodKSimple (mu := mu) hK (s + t) =
      kernelOpGoodKSimple (mu := mu) hK s +
        kernelOpGoodKSimple (mu := mu) hK t := by
  calc
    kernelOpGoodKSimple (mu := mu) hK (s + t)
        =
          kernelOpL2OfGoodK (mu := mu) hK
            (good_add (simpleFunc_good (mu := mu) s)
              (simpleFunc_good (mu := mu) t)) := by
          exact kernelOpL2OfGoodK_congr (mu := mu) hK
            (simpleFunc_good (mu := mu) (s + t))
            (good_add (simpleFunc_good (mu := mu) s)
              (simpleFunc_good (mu := mu) t))
            (Lp.simpleFunc.add_toSimpleFunc s t)
    _ =
      kernelOpGoodKSimple (mu := mu) hK s +
        kernelOpGoodKSimple (mu := mu) hK t := by
          exact kernelOpL2OfGoodK_add (mu := mu) hK
            (simpleFunc_good (mu := mu) s)
            (simpleFunc_good (mu := mu) t)

/-- Homogeneity of the bounded-kernel transform on `Lp.simpleFunc`. -/
lemma kernelOpGoodKSimple_smul {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    (c : Real) (s : Lp.simpleFunc Real 2 mu) :
    kernelOpGoodKSimple (mu := mu) hK (c • s) =
      c • kernelOpGoodKSimple (mu := mu) hK s := by
  calc
    kernelOpGoodKSimple (mu := mu) hK (c • s)
        =
          kernelOpL2OfGoodK (mu := mu) hK
            (good_smul c (simpleFunc_good (mu := mu) s)) := by
          exact kernelOpL2OfGoodK_congr (mu := mu) hK
            (simpleFunc_good (mu := mu) (c • s))
            (good_smul c (simpleFunc_good (mu := mu) s))
            (Lp.simpleFunc.smul_toSimpleFunc c s)
    _ = c • kernelOpGoodKSimple (mu := mu) hK s := by
          exact kernelOpL2OfGoodK_smul (mu := mu) hK c
            (simpleFunc_good (mu := mu) s)

/-- Subtraction of bounded-kernel transforms on `Lp.simpleFunc` in the kernel
argument. -/
lemma kernelOpGoodKSimple_sub_kernel {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    (s : Lp.simpleFunc Real 2 mu) :
    kernelOpGoodKSimple (mu := mu) (goodK_sub hK hL) s =
      kernelOpGoodKSimple (mu := mu) hK s -
        kernelOpGoodKSimple (mu := mu) hL s := by
  simpa [kernelOpGoodKSimple] using
    kernelOpL2OfGoodK_sub_kernel (mu := mu) hK hL
      (simpleFunc_good (mu := mu) s)

/-- Operator norm bound for a bounded measurable kernel on the dense
simple-function subspace. -/
lemma norm_kernelOpGoodKSimple_le {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    (s : Lp.simpleFunc Real 2 mu) :
    ‖kernelOpGoodKSimple (mu := mu) hK s‖ <=
      C * ‖(s : Lp Real 2 mu)‖ := by
  simpa [kernelOpGoodKSimple, goodL2_simpleFunc_eq_coe (mu := mu) s] using
    norm_kernelOpL2OfGoodK_le_const_mul_norm_goodL2
      (mu := mu) hK hC0 hKC (simpleFunc_good (mu := mu) s)

/-- Hilbert-Schmidt operator bound on the dense simple-function subspace. -/
lemma norm_kernelOpGoodKSimple_le_sqrt_kernelSqNorm
    {K : Omega -> Omega -> Real} (hK : GoodK K)
    (s : Lp.simpleFunc Real 2 mu) :
    ‖kernelOpGoodKSimple (mu := mu) hK s‖ <=
      Real.sqrt (kernelSqNorm mu K) * ‖(s : Lp Real 2 mu)‖ := by
  simpa [kernelOpGoodKSimple, goodL2_simpleFunc_eq_coe (mu := mu) s] using
    norm_kernelOpL2OfGoodK_le_sqrt_kernelSqNorm_mul_norm_goodL2
      (mu := mu) hK (simpleFunc_good (mu := mu) s)

/-- The bounded-kernel transform on the dense simple-function subspace as a
linear map. -/
def kernelOpGoodKSimpleLinearMap {K : Omega -> Omega -> Real}
    (hK : GoodK K) :
    Lp.simpleFunc Real 2 mu →ₗ[Real] Lp Real 2 mu where
  toFun := kernelOpGoodKSimple (mu := mu) hK
  map_add' := kernelOpGoodKSimple_add (mu := mu) hK
  map_smul' := kernelOpGoodKSimple_smul (mu := mu) hK

/-- The bounded-kernel transform on simple functions as a continuous linear
map with explicit norm bound. -/
def kernelOpGoodKSimpleCLM {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    Lp.simpleFunc Real 2 mu →L[Real] Lp Real 2 mu :=
  (kernelOpGoodKSimpleLinearMap (mu := mu) hK).mkContinuous C
    (fun s => by
      change ‖kernelOpGoodKSimple (mu := mu) hK s‖ <=
        C * ‖(s : Lp Real 2 mu)‖
      exact norm_kernelOpGoodKSimple_le (mu := mu) hK hC0 hKC s)

/-- The simple-function bounded-kernel operator has norm at most its uniform
kernel bound. -/
lemma norm_kernelOpGoodKSimpleCLM_le {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ <= C :=
  LinearMap.mkContinuous_norm_le
    (kernelOpGoodKSimpleLinearMap (mu := mu) hK) hC0 _

/-- Hilbert-Schmidt operator-norm bound on the dense simple-function
subspace. -/
lemma norm_kernelOpGoodKSimpleCLM_le_sqrt_kernelSqNorm
    {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ <=
      Real.sqrt (kernelSqNorm mu K) := by
  refine ContinuousLinearMap.opNorm_le_bound
    (kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC)
    (Real.sqrt_nonneg _) ?_
  intro s
  change ‖kernelOpGoodKSimple (mu := mu) hK s‖ <=
    Real.sqrt (kernelSqNorm mu K) * ‖(s : Lp Real 2 mu)‖
  exact norm_kernelOpGoodKSimple_le_sqrt_kernelSqNorm (mu := mu) hK s

/-- Additivity of the graphon kernel transform on `Lp.simpleFunc`. -/
lemma kernelOpSimple_add (hW : IsGraphon W mu)
    (s t : Lp.simpleFunc Real 2 mu) :
    kernelOpSimple (mu := mu) hW (s + t) =
      kernelOpSimple (mu := mu) hW s +
        kernelOpSimple (mu := mu) hW t := by
  calc
    kernelOpSimple (mu := mu) hW (s + t)
        =
          kernelOpL2OfGood (mu := mu) hW
            (good_add (simpleFunc_good (mu := mu) s)
              (simpleFunc_good (mu := mu) t)) := by
          exact kernelOpL2OfGood_congr (mu := mu) hW
            (simpleFunc_good (mu := mu) (s + t))
            (good_add (simpleFunc_good (mu := mu) s)
              (simpleFunc_good (mu := mu) t))
            (Lp.simpleFunc.add_toSimpleFunc s t)
    _ =
      kernelOpSimple (mu := mu) hW s +
        kernelOpSimple (mu := mu) hW t := by
          exact kernelOpL2OfGood_add hW
            (simpleFunc_good (mu := mu) s)
            (simpleFunc_good (mu := mu) t)

/-- Homogeneity of the graphon kernel transform on `Lp.simpleFunc`. -/
lemma kernelOpSimple_smul (hW : IsGraphon W mu)
    (c : Real) (s : Lp.simpleFunc Real 2 mu) :
    kernelOpSimple (mu := mu) hW (c • s) =
      c • kernelOpSimple (mu := mu) hW s := by
  calc
    kernelOpSimple (mu := mu) hW (c • s)
        =
          kernelOpL2OfGood (mu := mu) hW
            (good_smul c (simpleFunc_good (mu := mu) s)) := by
          exact kernelOpL2OfGood_congr (mu := mu) hW
            (simpleFunc_good (mu := mu) (c • s))
            (good_smul c (simpleFunc_good (mu := mu) s))
            (Lp.simpleFunc.smul_toSimpleFunc c s)
    _ = c • kernelOpSimple (mu := mu) hW s := by
          exact kernelOpL2OfGood_smul hW c (simpleFunc_good (mu := mu) s)

/-- The simple-function kernel transform is contractive in `L²`. -/
lemma norm_kernelOpSimple_le (hW : IsGraphon W mu)
    (s : Lp.simpleFunc Real 2 mu) :
    ‖kernelOpSimple (mu := mu) hW s‖ <= ‖(s : Lp Real 2 mu)‖ := by
  simpa [kernelOpSimple, goodL2_simpleFunc_eq_coe (mu := mu) s] using
    norm_kernelOpL2OfGood_le_norm_goodL2 hW
      (simpleFunc_good (mu := mu) s)

/-- The graphon kernel on the dense simple-function subspace as a linear map. -/
def kernelOpSimpleLinearMap (hW : IsGraphon W mu) :
    Lp.simpleFunc Real 2 mu →ₗ[Real] Lp Real 2 mu where
  toFun := kernelOpSimple (mu := mu) hW
  map_add' := kernelOpSimple_add (mu := mu) hW
  map_smul' := kernelOpSimple_smul (mu := mu) hW

/-- The graphon kernel on the dense simple-function subspace, bundled as a
continuous linear map with operator norm at most `1`. -/
def kernelOpSimpleCLM (hW : IsGraphon W mu) :
    Lp.simpleFunc Real 2 mu →L[Real] Lp Real 2 mu :=
  (kernelOpSimpleLinearMap (mu := mu) hW).mkContinuous 1
      (fun s => by
        change ‖kernelOpSimple (mu := mu) hW s‖ <= 1 * ‖(s : Lp Real 2 mu)‖
        simpa [one_mul] using norm_kernelOpSimple_le (mu := mu) hW s)

/-- The dense-domain graphon kernel map has norm at most `1`. -/
lemma norm_kernelOpSimpleCLM_le_one (hW : IsGraphon W mu) :
    ‖kernelOpSimpleCLM (mu := mu) hW‖ <= 1 :=
  LinearMap.mkContinuous_norm_le
    (kernelOpSimpleLinearMap (mu := mu) hW) zero_le_one _

/-- The dense embedding of `Lp.simpleFunc` into `Lp`, as a continuous linear
map.  This is the domain map used for extending the graphon kernel from simple
functions to all of `L²`. -/
def simpleFuncToL2 :
    Lp.simpleFunc Real 2 mu →L[Real] Lp Real 2 mu :=
  Lp.simpleFunc.coeToLp (α := Omega) (E := Real) (𝕜 := Real)
    (p := (2 : ENNReal)) (μ := mu)

/-- The bounded-kernel operator on all of `L²`, obtained by extending the
dense simple-function operator. -/
def kernelOpGoodKCLM {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    Lp Real 2 mu →L[Real] Lp Real 2 mu :=
  (kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC).extend
    (simpleFuncToL2 (mu := mu))

/-- Finite iteration of a completed `L2` operator.  The index `0` is the
identity. -/
noncomputable def clmIter
    (T : Lp Real 2 mu →L[Real] Lp Real 2 mu) :
    Nat -> Lp Real 2 mu -> Lp Real 2 mu
  | 0, f => f
  | n + 1, f => T (clmIter T n f)

/-- The full bounded-kernel operator agrees with the concrete
simple-function transform on the dense simple-function subspace. -/
lemma kernelOpGoodKCLM_simpleFunc {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    (s : Lp.simpleFunc Real 2 mu) :
    kernelOpGoodKCLM (mu := mu) hK hC0 hKC (s : Lp Real 2 mu) =
      kernelOpGoodKSimple (mu := mu) hK s := by
  change
    kernelOpGoodKCLM (mu := mu) hK hC0 hKC
      ((simpleFuncToL2 (mu := mu)) s) =
      kernelOpGoodKSimple (mu := mu) hK s
  simpa [kernelOpGoodKCLM, simpleFuncToL2, kernelOpGoodKSimpleCLM,
    kernelOpGoodKSimpleLinearMap] using
    ContinuousLinearMap.extend_eq
      (f := kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (Lp.simpleFunc.isUniformInducing (E := Real) (p := (2 : ENNReal))
        (μ := mu))
      s

/-- The completed bounded-kernel operator agrees with the concrete integral
transform on every bounded measurable representative.  This is the key
density argument from the simple-function extension to honest graphon-side
functions. -/
lemma kernelOpGoodKCLM_goodL2 {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f : Omega -> Real} (hf : Good f) :
    kernelOpGoodKCLM (mu := mu) hK hC0 hKC
        (goodL2 (mu := mu) hf) =
      kernelOpL2OfGoodK (mu := mu) hK hf := by
  let T : Lp Real 2 mu -> Lp Real 2 mu :=
    fun x => kernelOpGoodKCLM (mu := mu) hK hC0 hKC x
  let y : Lp Real 2 mu := kernelOpL2OfGoodK (mu := mu) hK hf
  let x0 : Lp Real 2 mu := goodL2 (mu := mu) hf
  set p : Lp Real 2 mu -> Prop :=
    fun x => ‖T x - y‖ <= C * ‖x - x0‖
  have hp_x0 : p x0 := by
    apply DenseRange.induction_on (p := p)
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      x0
    · dsimp [p, T, x0, y]
      exact isClosed_le (by fun_prop) (by fun_prop)
    · intro s
      dsimp [p, T, x0, y]
      rw [kernelOpGoodKCLM_simpleFunc (mu := mu) hK hC0 hKC s]
      simpa [kernelOpGoodKSimple, goodL2_simpleFunc_eq_coe (mu := mu) s] using
        norm_kernelOpL2OfGoodK_sub_le_const_mul_norm_goodL2_sub
          (mu := mu) hK hC0 hKC
          (simpleFunc_good (mu := mu) s) hf
  have hnorm :
      ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC
          (goodL2 (mu := mu) hf) -
        kernelOpL2OfGoodK (mu := mu) hK hf‖ <= 0 := by
    simpa [p, T, x0, y] using hp_x0
  have hzero :
      kernelOpGoodKCLM (mu := mu) hK hC0 hKC
          (goodL2 (mu := mu) hf) -
        kernelOpL2OfGoodK (mu := mu) hK hf = 0 := by
    exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  exact sub_eq_zero.mp hzero

/-- Finite iterates of the completed bounded-kernel operator agree with the
pointwise iterated integral operator on bounded representatives. -/
lemma kernelOpGoodKCLM_iter_goodL2 {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {f : Omega -> Real} (hf : Good f) :
    forall n,
      clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC) n
          (goodL2 (mu := mu) hf) =
        goodL2 (mu := mu) (good_kernelOpIter_goodK (mu := mu) hK hf n)
  | 0 => rfl
  | n + 1 => by
      calc
        clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC)
            (n + 1) (goodL2 (mu := mu) hf)
            =
              kernelOpGoodKCLM (mu := mu) hK hC0 hKC
                (goodL2 (mu := mu)
                  (good_kernelOpIter_goodK (mu := mu) hK hf n)) := by
              change
                kernelOpGoodKCLM (mu := mu) hK hC0 hKC
                    (clmIter (mu := mu)
                      (kernelOpGoodKCLM (mu := mu) hK hC0 hKC)
                      n (goodL2 (mu := mu) hf)) =
                  kernelOpGoodKCLM (mu := mu) hK hC0 hKC
                    (goodL2 (mu := mu)
                      (good_kernelOpIter_goodK (mu := mu) hK hf n))
              rw [kernelOpGoodKCLM_iter_goodL2 hK hC0 hKC hf n]
        _ =
              kernelOpL2OfGoodK (mu := mu) hK
                (good_kernelOpIter_goodK (mu := mu) hK hf n) := by
              exact kernelOpGoodKCLM_goodL2 (mu := mu) hK hC0 hKC
                (good_kernelOpIter_goodK (mu := mu) hK hf n)
        _ =
              goodL2 (mu := mu)
                (good_kernelOpIter_goodK (mu := mu) hK hf (n + 1)) := rfl

/-- The full bounded-kernel operator has norm at most the supplied uniform
kernel bound. -/
lemma norm_kernelOpGoodKCLM_le {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC‖ <= C := by
  have h_ext :
      ‖(kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC).extend
          (simpleFuncToL2 (mu := mu))‖ <=
        1 * ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
    exact ContinuousLinearMap.opNorm_extend_le
      (N := (1 : NNReal))
      (f := kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (fun s => by
        change ‖(simpleFuncToL2 (mu := mu)) s‖ <= ((1 : NNReal) : Real) *
          ‖(s : Lp Real 2 mu)‖
        rw [NNReal.coe_one, one_mul]
        exact le_of_eq rfl)
  calc
    ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC‖
        <= 1 * ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
          simpa [kernelOpGoodKCLM] using h_ext
    _ = ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
          exact one_mul _
    _ <= C := by
          exact norm_kernelOpGoodKSimpleCLM_le
            (mu := mu) hK hC0 hKC

/-- Hilbert-Schmidt operator-norm bound for the completed bounded-kernel
operator on `L²`. -/
lemma norm_kernelOpGoodKCLM_le_sqrt_kernelSqNorm
    {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C) :
    ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC‖ <=
      Real.sqrt (kernelSqNorm mu K) := by
  have h_ext :
      ‖(kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC).extend
          (simpleFuncToL2 (mu := mu))‖ <=
        1 * ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
    exact ContinuousLinearMap.opNorm_extend_le
      (N := (1 : NNReal))
      (f := kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (fun s => by
        change ‖(simpleFuncToL2 (mu := mu)) s‖ <= ((1 : NNReal) : Real) *
          ‖(s : Lp Real 2 mu)‖
        rw [NNReal.coe_one, one_mul]
        exact le_of_eq rfl)
  calc
    ‖kernelOpGoodKCLM (mu := mu) hK hC0 hKC‖
        <= 1 * ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
          simpa [kernelOpGoodKCLM] using h_ext
    _ = ‖kernelOpGoodKSimpleCLM (mu := mu) hK hC0 hKC‖ := by
          exact one_mul _
    _ <= Real.sqrt (kernelSqNorm mu K) := by
          exact norm_kernelOpGoodKSimpleCLM_le_sqrt_kernelSqNorm
            (mu := mu) hK hC0 hKC

/-- The operator of a pointwise kernel difference is the difference of the
corresponding bounded-kernel operators. -/
lemma kernelOpGoodKCLM_sub_kernel {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {CK CL C : Real}
    (hCK0 : 0 <= CK) (hKC : forall x y, |K x y| <= CK)
    (hCL0 : 0 <= CL) (hLC : forall x y, |L x y| <= CL)
    (hC0 : 0 <= C) (hSubC : forall x y, |K x y - L x y| <= C) :
    kernelOpGoodKCLM (mu := mu) (goodK_sub hK hL)
        hC0 hSubC =
      kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
        kernelOpGoodKCLM (mu := mu) hL hCL0 hLC := by
  have hcomp :
      (kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
          kernelOpGoodKCLM (mu := mu) hL hCL0 hLC).comp
          (simpleFuncToL2 (mu := mu)) =
        kernelOpGoodKSimpleCLM (mu := mu)
          (goodK_sub hK hL) hC0 hSubC := by
    apply ContinuousLinearMap.ext
    intro s
    change
      (kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
          kernelOpGoodKCLM (mu := mu) hL hCL0 hLC)
          ((simpleFuncToL2 (mu := mu)) s) =
        kernelOpGoodKSimple (mu := mu) (goodK_sub hK hL) s
    rw [sub_apply]
    calc
      kernelOpGoodKCLM (mu := mu) hK hCK0 hKC
          ((simpleFuncToL2 (mu := mu)) s) -
          kernelOpGoodKCLM (mu := mu) hL hCL0 hLC
            ((simpleFuncToL2 (mu := mu)) s)
          =
            kernelOpGoodKCLM (mu := mu) hK hCK0 hKC
              (s : Lp Real 2 mu) -
            kernelOpGoodKCLM (mu := mu) hL hCL0 hLC
              (s : Lp Real 2 mu) := by
            rfl
      _ 
          =
            kernelOpGoodKSimple (mu := mu) hK s -
              kernelOpGoodKSimple (mu := mu) hL s := by
            rw [← kernelOpGoodKCLM_simpleFunc
                (mu := mu) hK hCK0 hKC s,
              ← kernelOpGoodKCLM_simpleFunc
                (mu := mu) hL hCL0 hLC s]
      _ =
          kernelOpGoodKSimple (mu := mu) (goodK_sub hK hL) s := by
            exact (kernelOpGoodKSimple_sub_kernel
              (mu := mu) hK hL s).symm
  have huniq :
      (kernelOpGoodKSimpleCLM (mu := mu)
          (goodK_sub hK hL) hC0 hSubC).extend
          (simpleFuncToL2 (mu := mu)) =
        kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
          kernelOpGoodKCLM (mu := mu) hL hCL0 hLC := by
    exact ContinuousLinearMap.extend_unique
      (f := kernelOpGoodKSimpleCLM (mu := mu)
        (goodK_sub hK hL) hC0 hSubC)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (Lp.simpleFunc.isUniformInducing (E := Real) (p := (2 : ENNReal))
        (μ := mu))
      (kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
        kernelOpGoodKCLM (mu := mu) hL hCL0 hLC)
      hcomp
  simpa [kernelOpGoodKCLM] using huniq

/-- Operator-norm bound for the difference of two bounded-kernel operators,
from a uniform bound on the pointwise kernel difference. -/
lemma norm_kernelOpGoodKCLM_sub_le {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {CK CL C : Real}
    (hCK0 : 0 <= CK) (hKC : forall x y, |K x y| <= CK)
    (hCL0 : 0 <= CL) (hLC : forall x y, |L x y| <= CL)
    (hC0 : 0 <= C) (hSubC : forall x y, |K x y - L x y| <= C) :
    ‖kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
        kernelOpGoodKCLM (mu := mu) hL hCL0 hLC‖ <= C := by
  rw [← kernelOpGoodKCLM_sub_kernel
    (mu := mu) hK hL hCK0 hKC hCL0 hLC hC0 hSubC]
  exact norm_kernelOpGoodKCLM_le
    (mu := mu) (goodK_sub hK hL) hC0 hSubC

/-- Hilbert--Schmidt operator-norm bound for the difference of two
bounded-kernel operators. -/
lemma norm_kernelOpGoodKCLM_sub_le_sqrt_kernelSqNorm
    {K L : Omega -> Omega -> Real}
    (hK : GoodK K) (hL : GoodK L)
    {CK CL C : Real}
    (hCK0 : 0 <= CK) (hKC : forall x y, |K x y| <= CK)
    (hCL0 : 0 <= CL) (hLC : forall x y, |L x y| <= CL)
    (hC0 : 0 <= C) (hSubC : forall x y, |K x y - L x y| <= C) :
    ‖kernelOpGoodKCLM (mu := mu) hK hCK0 hKC -
        kernelOpGoodKCLM (mu := mu) hL hCL0 hLC‖ <=
      Real.sqrt (kernelSqNorm mu (fun x y => K x y - L x y)) := by
  rw [← kernelOpGoodKCLM_sub_kernel
    (mu := mu) hK hL hCK0 hKC hCL0 hLC hC0 hSubC]
  exact norm_kernelOpGoodKCLM_le_sqrt_kernelSqNorm
    (mu := mu) (goodK_sub hK hL) hC0 hSubC

/-- The graphon kernel as a continuous linear operator on all of `L²`, obtained
by extending the contractive simple-function operator from the dense subspace
`Lp.simpleFunc`. -/
def kernelOpCLM (hW : IsGraphon W mu) :
    Lp Real 2 mu →L[Real] Lp Real 2 mu :=
  (kernelOpSimpleCLM (mu := mu) hW).extend (simpleFuncToL2 (mu := mu))

/-- The full `L²` graphon operator agrees with the concrete simple-function
kernel transform on the dense simple-function subspace. -/
lemma kernelOpCLM_simpleFunc (hW : IsGraphon W mu)
    (s : Lp.simpleFunc Real 2 mu) :
    kernelOpCLM (mu := mu) hW (s : Lp Real 2 mu) =
      kernelOpSimple (mu := mu) hW s := by
  change
    kernelOpCLM (mu := mu) hW ((simpleFuncToL2 (mu := mu)) s) =
      kernelOpSimple (mu := mu) hW s
  simpa [kernelOpCLM, simpleFuncToL2, kernelOpSimpleCLM,
    kernelOpSimpleLinearMap] using
    ContinuousLinearMap.extend_eq
      (f := kernelOpSimpleCLM (mu := mu) hW)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (Lp.simpleFunc.isUniformInducing (E := Real) (p := (2 : ENNReal))
        (μ := mu))
      s

/-- The canonical graphon operator is exactly the general bounded-kernel
operator specialized to the same graphon kernel. -/
lemma kernelOpCLM_eq_kernelOpGoodKCLM (hW : IsGraphon W mu) :
    kernelOpCLM (mu := mu) hW =
      kernelOpGoodKCLM (mu := mu) (goodK_of_isGraphon hW)
        zero_le_one (graphon_abs_le_one (mu := mu) hW) := by
  let hK : GoodK W := goodK_of_isGraphon hW
  let hKC : forall x y, |W x y| <= 1 := graphon_abs_le_one (mu := mu) hW
  have hcomp :
      (kernelOpCLM (mu := mu) hW).comp (simpleFuncToL2 (mu := mu)) =
        kernelOpGoodKSimpleCLM (mu := mu) hK zero_le_one hKC := by
    apply ContinuousLinearMap.ext
    intro s
    change kernelOpCLM (mu := mu) hW ((simpleFuncToL2 (mu := mu)) s) =
      kernelOpGoodKSimple (mu := mu) hK s
    calc
      kernelOpCLM (mu := mu) hW ((simpleFuncToL2 (mu := mu)) s)
          = kernelOpCLM (mu := mu) hW (s : Lp Real 2 mu) := by
            rfl
      _ = kernelOpSimple (mu := mu) hW s := by
            exact kernelOpCLM_simpleFunc (mu := mu) hW s
      _ = kernelOpGoodKSimple (mu := mu) hK s := by
            simpa [hK] using
              kernelOpSimple_eq_kernelOpGoodKSimple (mu := mu) hW s
  have huniq :
      (kernelOpGoodKSimpleCLM (mu := mu) hK zero_le_one hKC).extend
          (simpleFuncToL2 (mu := mu)) =
        kernelOpCLM (mu := mu) hW := by
    exact ContinuousLinearMap.extend_unique
      (f := kernelOpGoodKSimpleCLM (mu := mu) hK zero_le_one hKC)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (Lp.simpleFunc.isUniformInducing (E := Real) (p := (2 : ENNReal))
        (μ := mu))
      (kernelOpCLM (mu := mu) hW)
      hcomp
  simpa [kernelOpGoodKCLM, hK, hKC] using huniq.symm

/-- The completed graphon operator agrees with the concrete graphon integral
transform on every bounded measurable representative. -/
lemma kernelOpCLM_goodL2 (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    kernelOpCLM (mu := mu) hW (goodL2 (mu := mu) hf) =
      kernelOpL2OfGood (mu := mu) hW hf := by
  rw [kernelOpCLM_eq_kernelOpGoodKCLM (mu := mu) hW]
  rw [kernelOpL2OfGood_eq_kernelOpL2OfGoodK (mu := mu) hW hf]
  exact kernelOpGoodKCLM_goodL2 (mu := mu)
    (goodK_of_isGraphon hW)
    zero_le_one (graphon_abs_le_one (mu := mu) hW) hf

/-- Finite iterates of the completed graphon operator agree with the
pointwise iterated graphon integral operator on bounded representatives. -/
lemma kernelOpCLM_iter_goodL2 (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    forall n,
      clmIter (mu := mu) (kernelOpCLM (mu := mu) hW) n
          (goodL2 (mu := mu) hf) =
        goodL2 (mu := mu)
          (good_kernelOpIter_goodK (mu := mu) (goodK_of_isGraphon hW) hf n) := by
  rw [kernelOpCLM_eq_kernelOpGoodKCLM (mu := mu) hW]
  exact kernelOpGoodKCLM_iter_goodL2 (mu := mu)
    (goodK_of_isGraphon hW)
    zero_le_one (graphon_abs_le_one (mu := mu) hW) hf

/-- A graphon-operator iterate is the same `L²` vector as applying the
corresponding composed bounded kernel to a bounded representative. -/
lemma kernelOpCLM_iter_goodL2_eq_compPow (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) (n : Nat) :
    clmIter (mu := mu) (kernelOpCLM (mu := mu) hW) (n + 1)
        (goodL2 (mu := mu) hf) =
      kernelOpL2OfGoodK (mu := mu)
        (goodK_compPow (μ := mu) (goodK_of_isGraphon hW) n) hf := by
  rw [kernelOpCLM_iter_goodL2 (mu := mu) hW hf (n + 1)]
  rw [← kernelOpL2OfGoodK_compPow_eq_goodL2_iter_succ
    (mu := mu) (goodK_of_isGraphon hW) hf n]

/-- The full `L²` graphon operator has operator norm at most `1`. -/
lemma norm_kernelOpCLM_le_one (hW : IsGraphon W mu) :
    ‖kernelOpCLM (mu := mu) hW‖ <= 1 := by
  have h_ext :
      ‖(kernelOpSimpleCLM (mu := mu) hW).extend
          (simpleFuncToL2 (mu := mu))‖ <=
        1 * ‖kernelOpSimpleCLM (mu := mu) hW‖ := by
    exact ContinuousLinearMap.opNorm_extend_le
      (N := (1 : NNReal))
      (f := kernelOpSimpleCLM (mu := mu) hW)
      (e := simpleFuncToL2 (mu := mu))
      (Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
        (by norm_num))
      (fun s => by
        change ‖s‖ <= ((1 : NNReal) : Real) *
          ‖(s : Lp Real 2 mu)‖
        rw [NNReal.coe_one, one_mul]
        exact le_of_eq (by simp))
  calc
    ‖kernelOpCLM (mu := mu) hW‖
        <= 1 * ‖kernelOpSimpleCLM (mu := mu) hW‖ := by
          simpa [kernelOpCLM] using h_ext
    _ <= 1 := by
          simpa using norm_kernelOpSimpleCLM_le_one (mu := mu) hW

/-- Pointwise norm bound for the full `L²` graphon operator. -/
lemma norm_kernelOpCLM_apply_le (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) :
    ‖kernelOpCLM (mu := mu) hW f‖ <= ‖f‖ := by
  calc
    ‖kernelOpCLM (mu := mu) hW f‖
        <= ‖kernelOpCLM (mu := mu) hW‖ * ‖f‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ <= 1 * ‖f‖ := by
          exact mul_le_mul_of_nonneg_right
            (norm_kernelOpCLM_le_one (mu := mu) hW) (norm_nonneg f)
    _ = ‖f‖ := one_mul _

/-- A simple-function representative of the constant-one vector. -/
def oneSimpleL2 :
    Lp.simpleFunc Real 2 mu :=
  SimpleFunc.toLp (SimpleFunc.const Omega (1 : Real))
    ((SimpleFunc.const Omega (1 : Real)).memLp_of_isFiniteMeasure
      (2 : ENNReal) mu)

/-- The simple-function constant one embeds as the `L²` constant-one vector. -/
lemma oneSimpleL2_coe_eq_oneL2 :
    (oneSimpleL2 (Omega := Omega) (mu := mu) : Lp Real 2 mu) =
      oneL2 (Omega := Omega) mu := by
  calc
    (oneSimpleL2 (Omega := Omega) (mu := mu) : Lp Real 2 mu)
        =
          ((SimpleFunc.const Omega (1 : Real)).memLp_of_isFiniteMeasure
            (2 : ENNReal) mu).toLp
              (SimpleFunc.const Omega (1 : Real)) := rfl
    _ = (memLp_const (1 : Real)).toLp (fun _ : Omega => 1) := by
          exact MemLp.toLp_congr
            ((SimpleFunc.const Omega (1 : Real)).memLp_of_isFiniteMeasure
              (2 : ENNReal) mu)
            (memLp_const (1 : Real))
            (ae_of_all _ fun _ => rfl)
    _ = oneL2 (Omega := Omega) mu := rfl

/-- The kernel form applied to the constant-one function is the degree
function. -/
lemma kernelOp_one_eq_degree :
    kernelOp W mu (fun _ : Omega => 1) = degree W mu := by
  funext x
  simp [kernelOp, degree]

/-- The integral pairing of the constant-one function with the graphon degree
is the edge density. -/
lemma integral_one_mul_degree_eq_edgeDensity :
    (∫ x, (1 : Real) * degree W mu x ∂mu) = edgeDensity W mu := by
  simp [edgeDensity, mean]

/-- Equivalently, the kernel quadratic form at the constant-one function is
the edge density. -/
lemma integral_one_mul_kernelOp_one_eq_edgeDensity :
    (∫ x, (1 : Real) * kernelOp W mu (fun _ : Omega => 1) x ∂mu) =
      edgeDensity W mu := by
  rw [kernelOp_one_eq_degree]
  exact integral_one_mul_degree_eq_edgeDensity

/-- The concrete L² kernel transform sends the constant-one test function to
the graphon degree vector.  This is the representative-level form of the
eventual operator identity `T_W 1 = degree`. -/
lemma kernelOpL2OfGood_one_eq_degreeL2 (hW : IsGraphon W mu) :
    kernelOpL2OfGood (mu := mu) hW (good_one (Ω := Omega)) =
      degreeL2 hW := by
  exact MemLp.toLp_congr
    (kernelOp_memLp_two hW (good_one (Ω := Omega)))
    (degree_memLp_two hW)
    (ae_of_all _ fun x => congrFun (kernelOp_one_eq_degree (mu := mu) (W := W)) x)

/-- On the simple-function constant one, the kernel sends `1` to the graphon
degree vector. -/
lemma kernelOpSimple_one_eq_degreeL2 (hW : IsGraphon W mu) :
    kernelOpSimple (mu := mu) hW (oneSimpleL2 (Omega := Omega) (mu := mu)) =
      degreeL2 hW := by
  calc
    kernelOpSimple (mu := mu) hW (oneSimpleL2 (Omega := Omega) (mu := mu))
        =
          kernelOpL2OfGood (mu := mu) hW (good_one (Ω := Omega)) := by
          exact kernelOpL2OfGood_congr (mu := mu) hW
            (simpleFunc_good (mu := mu)
              (oneSimpleL2 (Omega := Omega) (mu := mu)))
            (good_one (Ω := Omega))
            (Lp.simpleFunc.toSimpleFunc_toLp
              (SimpleFunc.const Omega (1 : Real))
              ((SimpleFunc.const Omega (1 : Real)).memLp_of_isFiniteMeasure
                (2 : ENNReal) mu))
    _ = degreeL2 hW := kernelOpL2OfGood_one_eq_degreeL2 hW

/-- The full `L²` graphon operator sends the constant-one vector to the graphon
degree vector. -/
lemma kernelOpCLM_one_eq_degreeL2 (hW : IsGraphon W mu) :
    kernelOpCLM (mu := mu) hW (oneL2 (Omega := Omega) mu) =
      degreeL2 hW := by
  rw [← oneSimpleL2_coe_eq_oneL2 (Omega := Omega) (mu := mu)]
  rw [kernelOpCLM_simpleFunc hW]
  exact kernelOpSimple_one_eq_degreeL2 hW

/-- The `L²` pairing of `g` with the pointwise kernel transform of `f`. -/
lemma inner_goodL2_kernelOpL2OfGood_eq_integral
    (hW : IsGraphon W mu)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    inner Real (goodL2 (mu := mu) hg)
      (kernelOpL2OfGood (mu := mu) hW hf) =
      ∫ x, g x * kernelOp W mu f x ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  have hgae := goodL2_ae_eq (mu := mu) hg
  have hkfae := kernelOpL2OfGood_ae_eq (mu := mu) hW hf
  refine integral_congr_ae ?_
  filter_upwards [hgae, hkfae] with x hgx hkfx
  rw [hgx, hkfx]
  simp [RCLike.inner_apply, mul_comm]

/-- The same kernel pairing with the kernel-transformed function in the first
slot. -/
lemma inner_kernelOpL2OfGood_goodL2_eq_integral
    (hW : IsGraphon W mu)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    inner Real (kernelOpL2OfGood (mu := mu) hW hf)
      (goodL2 (mu := mu) hg) =
      ∫ x, kernelOp W mu f x * g x ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  have hkfae := kernelOpL2OfGood_ae_eq (mu := mu) hW hf
  have hgae := goodL2_ae_eq (mu := mu) hg
  refine integral_congr_ae ?_
  filter_upwards [hkfae, hgae] with x hkfx hgx
  rw [hkfx, hgx]
  simp [RCLike.inner_apply, mul_comm]

/-- For bounded representatives, the absolute value of the graphon quadratic
form is bounded by the quadratic form of the pointwise absolute value.

This is the concrete positivity inequality behind the Perron orientation step:
for a nonnegative graphon kernel, replacing `f` by `|f|` cannot decrease the
absolute Rayleigh numerator. -/
lemma abs_inner_goodL2_kernelOpL2OfGood_self_le_abs
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    |inner Real (goodL2 (mu := mu) hf)
        (kernelOpL2OfGood (mu := mu) hW hf)| <=
      inner Real
        (goodL2 (mu := mu) (good_abs hf))
        (kernelOpL2OfGood (mu := mu) hW (good_abs hf)) := by
  rw [inner_goodL2_kernelOpL2OfGood_eq_integral hW hf hf,
    inner_goodL2_kernelOpL2OfGood_eq_integral hW (good_abs hf) (good_abs hf)]
  calc
    |∫ x, f x * kernelOp W mu f x ∂mu|
        <= ∫ x, |f x * kernelOp W mu f x| ∂mu := by
          exact abs_integral_le_integral_abs
    _ <= ∫ x, |f x| * kernelOp W mu (fun y : Omega => |f y|) x ∂mu := by
          refine integral_mono
            ((hf.mul (good_kernelOp hW hf)).integrable).abs
            ((good_abs hf).mul (good_kernelOp hW (good_abs hf))).integrable ?_
          intro x
          change |f x * kernelOp W mu f x| <=
            |f x| * kernelOp W mu (fun y : Omega => |f y|) x
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (abs_kernelOp_le_kernelOp_abs hW hf x) (abs_nonneg (f x))

/-- The positivity-preserving quadratic-form domination, lifted from bounded
representatives to their `L²` vectors. -/
lemma abs_inner_goodL2_kernelOpCLM_self_le_abs
    (hW : IsGraphon W mu)
    {f : Omega -> Real} (hf : Good f) :
    |inner Real (goodL2 (mu := mu) hf)
        (kernelOpCLM (mu := mu) hW (goodL2 (mu := mu) hf))| <=
      inner Real
        |goodL2 (mu := mu) hf|
        (kernelOpCLM (mu := mu) hW |goodL2 (mu := mu) hf|) := by
  rw [kernelOpCLM_goodL2 (mu := mu) hW hf]
  rw [← goodL2_abs (mu := mu) hf]
  rw [kernelOpCLM_goodL2 (mu := mu) hW (good_abs hf)]
  exact abs_inner_goodL2_kernelOpL2OfGood_self_le_abs (mu := mu) hW hf

/-- The absolute-value map on real `L²` is continuous. -/
lemma continuous_abs_l2 :
    Continuous (fun f : Lp Real 2 mu => |f|) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro f
  refine Metric.continuousAt_iff.2 ?_
  intro eps heps
  refine ⟨eps, heps, fun g hg => ?_⟩
  have hg' : ‖g - f‖ < eps := by
    simpa [dist_eq_norm] using hg
  have hle : ‖|g| - |f|‖ <= ‖g - f‖ :=
    norm_abs_sub_abs g f
  simpa [dist_eq_norm] using lt_of_le_of_lt hle hg'

/-- Positivity-preserving quadratic-form domination for every `L²` vector.

This is the operator-level form of
`abs_inner_goodL2_kernelOpCLM_self_le_abs`, obtained by density of bounded
representatives. -/
lemma abs_inner_kernelOpCLM_self_le_abs
    (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) :
    |inner Real f (kernelOpCLM (mu := mu) hW f)| <=
      inner Real |f| (kernelOpCLM (mu := mu) hW |f|) := by
  let T : Lp Real 2 mu →L[Real] Lp Real 2 mu :=
    kernelOpCLM (mu := mu) hW
  let p : Lp Real 2 mu -> Prop := fun f =>
    |inner Real f (T f)| <= inner Real |f| (T |f|)
  change p f
  exact DenseRange.induction_on
    (denseRange_goodL2 (Omega := Omega) (mu := mu)) f
    (by
      dsimp [p]
      have hleft :
          Continuous fun f : Lp Real 2 mu => |inner Real f (T f)| :=
        continuous_abs.comp
          (Continuous.inner continuous_id T.continuous)
      have hright :
          Continuous fun f : Lp Real 2 mu => inner Real |f| (T |f|) :=
        Continuous.inner continuous_abs_l2 (T.continuous.comp continuous_abs_l2)
      exact isClosed_le hleft hright)
    (by
      intro a
      rcases a with ⟨g, hg⟩
      dsimp [p, T]
      simpa using abs_inner_goodL2_kernelOpCLM_self_le_abs
        (mu := mu) hW hg)

/-- The `L²` pairing of a bounded test function with the pointwise graphon
transform of an arbitrary `L²` vector. -/
lemma inner_goodL2_kernelOpL2OfL2_eq_integral
    (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) {g : Omega -> Real} (hg : Good g) :
    inner Real (goodL2 (mu := mu) hg)
      (kernelOpL2OfL2 (mu := mu) hW f) =
      ∫ x, g x * kernelOp W mu (fun y : Omega => f y) x ∂mu := by
  simpa [kernelOpL2OfL2] using
    inner_goodL2_eq_integral_mul
      (mu := mu) hg (good_kernelOp_l2 (mu := mu) hW f)

/-- The `L²` pairing of the pointwise transform of a bounded function with an
arbitrary `L²` vector. -/
lemma inner_kernelOpL2OfGood_l2_eq_integral
    (hW : IsGraphon W mu)
    {g : Omega -> Real} (hg : Good g) (f : Lp Real 2 mu) :
    inner Real (kernelOpL2OfGood (mu := mu) hW hg) f =
      ∫ x, kernelOp W mu g x * f x ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  have hkgae := kernelOpL2OfGood_ae_eq (mu := mu) hW hg
  refine integral_congr_ae ?_
  filter_upwards [hkgae] with x hkx
  rw [hkx]
  simp [RCLike.inner_apply, mul_comm]

/-- Mixed graphon-kernel symmetry with one arbitrary `L²` input and one
bounded strongly measurable test function. -/
lemma kernelOp_symm_l2_good
    (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) {g : Omega -> Real} (hg : Good g) :
    (∫ x, kernelOp W mu (fun y : Omega => f y) x * g x ∂mu) =
      ∫ y, f y * kernelOp W mu g y ∂mu := by
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bdd
  have hf_int : Integrable (fun y : Omega => f y) mu :=
    (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) <= 2)
  have hSM : StronglyMeasurable
      (Function.uncurry
        (fun x y : Omega => W x y * f y * g x)) := by
    have h1 : StronglyMeasurable
        (fun p : Omega × Omega => W p.1 p.2) :=
      hW.meas.stronglyMeasurable
    have h2 : StronglyMeasurable
        (fun p : Omega × Omega => f p.2) :=
      (Lp.stronglyMeasurable f).comp_measurable measurable_snd
    have h3 : StronglyMeasurable
        (fun p : Omega × Omega => g p.1) :=
      hg.meas.comp_measurable measurable_fst
    exact (h1.mul h2).mul h3
  have hInt : Integrable
      (Function.uncurry
        (fun x y : Omega => W x y * f y * g x))
      (mu.prod mu) := by
    have hbound : Integrable
        (fun p : Omega × Omega => Cg * |f p.2|) (mu.prod mu) :=
      (hf_int.norm.const_mul Cg).comp_snd mu
    refine hbound.mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨x, y⟩
    simp only [Function.uncurry, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (hW.nonneg x y)]
    have hleft_nonneg : 0 <= W x y * |f y| :=
      mul_nonneg (hW.nonneg x y) (abs_nonneg _)
    have h1 : W x y * |f y| <= 1 * |f y| :=
      mul_le_mul_of_nonneg_right (hW.le_one x y) (abs_nonneg _)
    have h2 : W x y * |f y| * |g x| <= (1 * |f y|) * Cg :=
      mul_le_mul h1 (hCg x) (abs_nonneg _)
        (mul_nonneg zero_le_one (abs_nonneg _))
    simpa [one_mul, mul_assoc, mul_comm, mul_left_comm] using h2
  have hL :
      ∀ x,
        kernelOp W mu (fun y : Omega => f y) x * g x =
          ∫ y, W x y * f y * g x ∂mu := fun x => by
    rw [kernelOp, integral_mul_const]
  have hR :
      ∀ y,
        f y * kernelOp W mu g y =
          ∫ x, W x y * f y * g x ∂mu := fun y => by
    rw [kernelOp, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show f y * (W y x * g x) = W x y * f y * g x
    rw [hW.symm y x]
    ring
  calc
    (∫ x, kernelOp W mu (fun y : Omega => f y) x * g x ∂mu)
        = ∫ x, ∫ y, W x y * f y * g x ∂mu ∂mu := by
          simp_rw [hL]
    _ = ∫ y, ∫ x, W x y * f y * g x ∂mu ∂mu := by
          exact integral_integral_swap hInt
    _ = ∫ y, f y * kernelOp W mu g y ∂mu := by
          simp_rw [hR]

/-- Mixed Hilbert-space self-adjointness with one arbitrary `L²` vector and
one bounded representative. -/
lemma kernelOpL2OfL2_goodL2_selfadj
    (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) {g : Omega -> Real} (hg : Good g) :
    inner Real (goodL2 (mu := mu) hg)
        (kernelOpL2OfL2 (mu := mu) hW f) =
      inner Real (kernelOpL2OfGood (mu := mu) hW hg) f := by
  rw [inner_goodL2_kernelOpL2OfL2_eq_integral (mu := mu) hW f hg]
  rw [inner_kernelOpL2OfGood_l2_eq_integral (mu := mu) hW hg f]
  calc
    (∫ x, g x * kernelOp W mu (fun y : Omega => f y) x ∂mu)
        = ∫ x, kernelOp W mu (fun y : Omega => f y) x * g x ∂mu := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          ring
    _ = ∫ y, f y * kernelOp W mu g y ∂mu :=
          kernelOp_symm_l2_good (mu := mu) hW f hg
    _ = ∫ x, kernelOp W mu g x * f x ∂mu := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          ring

/-- On bounded measurable test functions, the graphon kernel transform is
self-adjoint as an `L²` bilinear form. -/
lemma kernelOpL2OfGood_selfadj (hW : IsGraphon W mu)
    {f g : Omega -> Real} (hf : Good f) (hg : Good g) :
    inner Real (kernelOpL2OfGood (mu := mu) hW hf)
        (goodL2 (mu := mu) hg) =
      inner Real (goodL2 (mu := mu) hf)
        (kernelOpL2OfGood (mu := mu) hW hg) := by
  rw [inner_kernelOpL2OfGood_goodL2_eq_integral hW hf hg,
    inner_goodL2_kernelOpL2OfGood_eq_integral hW hg hf]
  exact kernelOp_symm hW hf hg

/-- The canonical `L²` graphon operator is self-adjoint as a Hilbert-space
operator.  This is obtained from the representative-level kernel symmetry by
density of simple functions, not by any finite-spectrum reduction. -/
lemma kernelOpCLM_isSymmetric (hW : IsGraphon W mu) :
    (kernelOpCLM (mu := mu) hW :
      Lp Real 2 mu →ₗ[Real] Lp Real 2 mu).IsSymmetric := by
  intro f g
  let e : Lp.simpleFunc Real 2 mu -> Lp Real 2 mu :=
    fun s => (s : Lp Real 2 mu)
  have hdense : DenseRange e :=
    Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
      (by norm_num)
  refine hdense.induction_on₂
    (p := fun f g =>
      inner Real (kernelOpCLM (mu := mu) hW f) g =
        inner Real f (kernelOpCLM (mu := mu) hW g))
    ?closed ?simple f g
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro s t
    dsimp [e]
    rw [kernelOpCLM_simpleFunc hW s, kernelOpCLM_simpleFunc hW t]
    dsimp [kernelOpSimple]
    have h :=
      kernelOpL2OfGood_selfadj (mu := mu) hW
        (simpleFunc_good (mu := mu) s) (simpleFunc_good (mu := mu) t)
    simpa [goodL2_simpleFunc_eq_coe (mu := mu) s,
      goodL2_simpleFunc_eq_coe (mu := mu) t] using h

/-- Pointwise form of `kernelOpCLM_isSymmetric`. -/
lemma kernelOpCLM_selfadj (hW : IsGraphon W mu)
    (f g : Lp Real 2 mu) :
    inner Real (kernelOpCLM (mu := mu) hW f) g =
      inner Real f (kernelOpCLM (mu := mu) hW g) :=
  kernelOpCLM_isSymmetric (mu := mu) hW f g

/-- The completed graphon operator is the concrete pointwise `L²` integral
operator on every `L²` input.

The proof separates vectors by the dense family of bounded strongly
measurable representatives.  This identifies the abstract extension
`kernelOpCLM` with the graphon-side integral formula. -/
lemma kernelOpCLM_eq_kernelOpL2OfL2_apply (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) :
    kernelOpCLM (mu := mu) hW f =
      kernelOpL2OfL2 (mu := mu) hW f := by
  let z : Lp Real 2 mu :=
    kernelOpCLM (mu := mu) hW f - kernelOpL2OfL2 (mu := mu) hW f
  have hinner_good :
      ∀ a : {g : Omega -> Real // Good g},
        inner Real (goodL2 (mu := mu) a.property) z = 0 := by
    intro a
    rcases a with ⟨g, hg⟩
    have hclm :
        inner Real (goodL2 (mu := mu) hg)
            (kernelOpCLM (mu := mu) hW f) =
          inner Real (kernelOpL2OfGood (mu := mu) hW hg) f := by
      calc
        inner Real (goodL2 (mu := mu) hg)
            (kernelOpCLM (mu := mu) hW f)
            =
              inner Real (kernelOpCLM (mu := mu) hW
                  (goodL2 (mu := mu) hg)) f := by
              exact (kernelOpCLM_selfadj (mu := mu) hW
                (goodL2 (mu := mu) hg) f).symm
        _ =
              inner Real (kernelOpL2OfGood (mu := mu) hW hg) f := by
              rw [kernelOpCLM_goodL2 (mu := mu) hW hg]
    have hpoint :
        inner Real (goodL2 (mu := mu) hg)
            (kernelOpL2OfL2 (mu := mu) hW f) =
          inner Real (kernelOpL2OfGood (mu := mu) hW hg) f :=
      kernelOpL2OfL2_goodL2_selfadj (mu := mu) hW f hg
    dsimp [z]
    rw [inner_sub_right, hclm, hpoint, sub_self]
  have hall :
      ∀ v : Lp Real 2 mu, inner Real v z = 0 := by
    intro v
    apply DenseRange.induction_on
      (p := fun v : Lp Real 2 mu => inner Real v z = 0)
      (denseRange_goodL2 (Omega := Omega) (mu := mu)) v
    · exact isClosed_eq (by fun_prop) continuous_const
    · intro a
      exact hinner_good a
  have hz_zero : z = 0 := by
    have hzz : inner Real z z = 0 := hall z
    have hnormsq : ‖z‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hzz
    have hnorm : ‖z‖ = 0 := by
      nlinarith [sq_nonneg ‖z‖]
    exact norm_eq_zero.mp hnorm
  exact sub_eq_zero.mp hz_zero

/-- Functional extensional form of `kernelOpCLM_eq_kernelOpL2OfL2_apply`. -/
lemma kernelOpCLM_eq_kernelOpL2OfL2 (hW : IsGraphon W mu) :
    kernelOpCLM (mu := mu) hW =
      fun f : Lp Real 2 mu => kernelOpL2OfL2 (mu := mu) hW f := by
  funext f
  exact kernelOpCLM_eq_kernelOpL2OfL2_apply (mu := mu) hW f

/-- Finite row-energy identity for arbitrary `L²` modes and the completed
graphon operator. -/
lemma sum_norm_kernelOpCLM_sq_eq_integral_sum_graphon_row_inner_l2_sq
    (hW : IsGraphon W mu)
    (mode : Nat -> Lp Real 2 mu)
    (s : Finset Nat) :
    s.sum (fun n : Nat =>
        ‖(kernelOpCLM (mu := mu) hW) (mode n)‖ ^ 2) =
      ∫ x, s.sum (fun n : Nat =>
        inner Real
          (goodL2 (mu := mu) (goodK_row (goodK_of_isGraphon hW) x))
          (mode n) ^ 2) ∂mu := by
  have hterm_integrable :
      ∀ n ∈ s, Integrable (fun x : Omega =>
        inner Real
          (goodL2 (mu := mu) (goodK_row (goodK_of_isGraphon hW) x))
          (mode n) ^ 2) mu := by
    intro n hn
    have hgood : Good (fun x : Omega =>
        kernelOp W mu (fun y : Omega => mode n y) x *
          kernelOp W mu (fun y : Omega => mode n y) x) :=
      (good_kernelOp_l2 (mu := mu) hW (mode n)).mul
        (good_kernelOp_l2 (mu := mu) hW (mode n))
    refine hgood.integrable.congr ?_
    exact ae_of_all _ fun x => by
      change
        kernelOp W mu (fun y : Omega => mode n y) x *
            kernelOp W mu (fun y : Omega => mode n y) x =
          inner Real
            (goodL2 (mu := mu) (goodK_row (goodK_of_isGraphon hW) x))
            (mode n) ^ 2
      rw [inner_goodK_row_l2_eq_kernelOp
        (mu := mu) (goodK_of_isGraphon hW) (mode n) x]
      ring
  rw [integral_finsetSum s hterm_integrable]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have happly :
      (kernelOpCLM (mu := mu) hW) (mode n) =
        kernelOpL2OfL2 (mu := mu) hW (mode n) :=
    kernelOpCLM_eq_kernelOpL2OfL2_apply (mu := mu) hW (mode n)
  calc
    ‖(kernelOpCLM (mu := mu) hW) (mode n)‖ ^ 2
        = ‖kernelOpL2OfL2 (mu := mu) hW (mode n)‖ ^ 2 := by
          rw [happly]
    _ = ∫ x, kernelOp W mu (fun y : Omega => mode n y) x *
          kernelOp W mu (fun y : Omega => mode n y) x ∂mu := by
          rw [kernelOpL2OfL2]
          rw [norm_goodL2_sq_eq_integral_mul
            (mu := mu) (good_kernelOp_l2 (mu := mu) hW (mode n))]
    _ = ∫ x,
          inner Real
            (goodL2 (mu := mu) (goodK_row (goodK_of_isGraphon hW) x))
            (mode n) ^ 2 ∂mu := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          change
            kernelOp W mu (fun y : Omega => mode n y) x *
                kernelOp W mu (fun y : Omega => mode n y) x =
              inner Real
                (goodL2 (mu := mu) (goodK_row (goodK_of_isGraphon hW) x))
                (mode n) ^ 2
          rw [inner_goodK_row_l2_eq_kernelOp
            (mu := mu) (goodK_of_isGraphon hW) (mode n) x]
          ring

/-- Cyclic graphon traces as integrals of row pairings against operator
iterates.

For every `k`, the `(k+3)`-cycle trace `trace (W^(k+3))`, represented here as
`trace (compPow W (k+2))`, is the integral of
`⟪W_x, T_W^(k+1) W_x⟫` over graphon rows.  This is an integral identity, not a
spectral assertion. -/
lemma trace_compPow_eq_integral_row_inner_clmIter
    (hW : IsGraphon W mu) (k : Nat) :
    trace mu (compPow mu W (k + 2)) =
      ∫ x, inner Real
        (goodL2 (mu := mu) (goodK_row (goodK_of_isGraphon hW) x))
        (clmIter (mu := mu) (kernelOpCLM (mu := mu) hW) (k + 1)
          (goodL2 (mu := mu) (goodK_row (goodK_of_isGraphon hW) x))) ∂mu := by
  let hK : GoodK W := goodK_of_isGraphon hW
  have hpowk : GoodK (compPow mu W k) := goodK_compPow (μ := mu) hK k
  have hpowks : GoodK (compPow mu W (k + 1)) :=
    goodK_compPow (μ := mu) hK (k + 1)
  have htrace_rotate :
      trace mu (compPow mu W (k + 2)) =
        trace mu (comp mu (compPow mu W (k + 1)) W) := by
    change trace mu (comp mu W (compPow mu W (k + 1))) =
      trace mu (comp mu (compPow mu W (k + 1)) W)
    exact trace_comp_comm (μ := mu) hK hpowks
  rw [htrace_rotate]
  rw [trace]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  let hrow : Good (fun y : Omega => W x y) := goodK_row hK x
  have hiter :
      clmIter (mu := mu) (kernelOpCLM (mu := mu) hW) (k + 1)
          (goodL2 (mu := mu) hrow) =
        kernelOpL2OfGoodK (mu := mu) hpowk hrow := by
    exact kernelOpCLM_iter_goodL2_eq_compPow (mu := mu) hW hrow k
  have hkernel :
      kernelOp W mu
          (fun y : Omega =>
            (kernelOpL2OfGoodK (mu := mu) hpowk hrow : Lp Real 2 mu) y)
          x =
        kernelOp W mu (kernelOp (compPow mu W k) mu (fun y => W x y)) x := by
    unfold kernelOp
    refine integral_congr_ae ?_
    filter_upwards [kernelOpL2OfGoodK_ae_eq (mu := mu) hpowk hrow] with y hy
    rw [hy]
    simp [kernelOp]
  calc
    comp mu (compPow mu W (k + 1)) W x x
        = kernelOp (compPow mu W (k + 1)) mu (fun y : Omega => W x y) x := by
          unfold comp kernelOp
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          change compPow mu W (k + 1) x y * W y x =
            compPow mu W (k + 1) x y * W x y
          rw [← hW.symm x y]
    _ = kernelOp W mu (kernelOp (compPow mu W k) mu (fun y => W x y)) x := by
          rw [← kernelOp_comp_eq_kernelOp_kernelOp
            (mu := mu) hK hpowk hrow]
          rfl
    _ = kernelOp W mu
          (fun y : Omega =>
            (kernelOpL2OfGoodK (mu := mu) hpowk hrow : Lp Real 2 mu) y)
          x := hkernel.symm
    _ = inner Real (goodL2 (mu := mu) hrow)
          (kernelOpL2OfGoodK (mu := mu) hpowk hrow) := by
          rw [inner_goodK_row_l2_eq_kernelOp (mu := mu) hK
            (kernelOpL2OfGoodK (mu := mu) hpowk hrow) x]
    _ = inner Real (goodL2 (mu := mu) hrow)
          (clmIter (mu := mu) (kernelOpCLM (mu := mu) hW) (k + 1)
            (goodL2 (mu := mu) hrow)) := by
          rw [hiter]

/-- The Hilbert-space version of the same identity:
`⟪1, degree⟫ = p`.  Once the graphon integral operator `T_W` is constructed
with `T_W 1 = degree`, this is the Rayleigh numerator for the constant vector. -/
lemma inner_oneL2_degreeL2_eq_edgeDensity
    (hW : IsGraphon W mu) :
    inner Real (oneL2 (Omega := Omega) mu) (degreeL2 hW) =
      edgeDensity W mu := by
  rw [MeasureTheory.L2.inner_def]
  have hone := oneL2_ae_eq_one (Omega := Omega) (mu := mu)
  have hdeg : (degreeL2 hW : Omega -> Real) =ᵐ[mu] degree W mu := by
    change
      ((degree_memLp_two hW).toLp (degree W mu) : Omega -> Real) =ᵐ[mu]
        degree W mu
    exact MemLp.coeFn_toLp (degree_memLp_two hW)
  calc
    (∫ x : Omega,
        inner Real ((oneL2 (Omega := Omega) mu : Lp Real 2 mu) x)
          ((degreeL2 hW : Lp Real 2 mu) x) ∂mu)
        = ∫ x : Omega, (1 : Real) * degree W mu x ∂mu := by
          refine integral_congr_ae ?_
          filter_upwards [hone, hdeg] with x hxone hxdeg
          rw [hxone, hxdeg]
          simp
    _ = edgeDensity W mu := integral_one_mul_degree_eq_edgeDensity

/-- The constant vector paired with the concrete L² kernel transform of the
constant-one test function is the edge density. -/
lemma inner_oneL2_kernelOpL2OfGood_one_eq_edgeDensity
    (hW : IsGraphon W mu) :
    inner Real (oneL2 (Omega := Omega) mu)
      (kernelOpL2OfGood (mu := mu) hW (good_one (Ω := Omega))) =
      edgeDensity W mu := by
  rw [kernelOpL2OfGood_one_eq_degreeL2 hW]
  exact inner_oneL2_degreeL2_eq_edgeDensity hW

/-- The constant-one vector has squared norm `1` in a probability space. -/
lemma inner_oneL2_oneL2 :
    inner Real (oneL2 (Omega := Omega) mu) (oneL2 (Omega := Omega) mu) =
      1 := by
  rw [MeasureTheory.L2.inner_def]
  have hone := oneL2_ae_eq_one (Omega := Omega) (mu := mu)
  calc
    (∫ x : Omega,
        inner Real ((oneL2 (Omega := Omega) mu : Lp Real 2 mu) x)
          ((oneL2 (Omega := Omega) mu : Lp Real 2 mu) x) ∂mu)
        = ∫ _x : Omega, (1 : Real) ∂mu := by
          refine integral_congr_ae ?_
          filter_upwards [hone] with x hxone
          rw [hxone]
          simp
    _ = 1 := by simp

/-- The constant-one vector is nonzero in a probability space. -/
lemma oneL2_ne_zero :
    oneL2 (Omega := Omega) mu ≠ 0 := by
  intro h
  have hinner := inner_oneL2_oneL2 (Omega := Omega) (mu := mu)
  rw [h] at hinner
  norm_num at hinner

/-- The squared norm of the constant-one vector is `1`. -/
lemma norm_oneL2_sq :
    ‖oneL2 (Omega := Omega) mu‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_oneL2_oneL2]

/-- Positive edge density forces the canonical `L²` graphon operator to be
nonzero.

Indeed, the quadratic pairing of the constant-one vector with its image under
the operator is exactly the edge density. -/
lemma kernelOpCLM_ne_zero_of_edgeDensity_pos
    (hW : IsGraphon W mu)
    (hp : 0 < edgeDensity W mu) :
    Ne (kernelOpCLM (mu := mu) hW) 0 := by
  intro hzero
  have hpair :
      inner Real (oneL2 (Omega := Omega) mu)
        (kernelOpCLM (mu := mu) hW (oneL2 (Omega := Omega) mu)) =
        edgeDensity W mu := by
    rw [kernelOpCLM_one_eq_degreeL2 hW]
    exact inner_oneL2_degreeL2_eq_edgeDensity hW
  rw [hzero] at hpair
  simp at hpair
  linarith

end L2Kernel
end Spectral
end OddCycleBound
