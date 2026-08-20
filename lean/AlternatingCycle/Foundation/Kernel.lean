import AlternatingCycle.Foundation.PathDensity
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sets
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.Real

/-!
# Kernel-composition algebra

To prove the cycle inclusion–exclusion `t(C_m, 1−U) = [polynomial in x_j and c_m]` uniformly,
we work with kernels `K : Ω → Ω → ℝ` under composition `comp K L x y = ∫ z, K x z · L z y`.
The all-ones kernel `onesKernel` is idempotent (`onesKernel ∘ onesKernel = onesKernel`) and rank-one, and the central
**cut lemma** `onesKernel ∘ M ∘ onesKernel = (∫∫ M) · onesKernel` is the arc-factorization mechanism: a `onesKernel`-flanked
run of `U`'s collapses to the scalar path density `∫∫ Uᵒˡ = x_ℓ`.

This file builds the reusable algebra (composition, boundedness/measurability closure,
bilinearity, the cut lemma).  Cyclic traces, the per-cycle expansions (C5/C7/C9), and the
connection to `pathDensity`/`c_m` are built on top.
-/

open MeasureTheory
open scoped BigOperators ENNReal symmDiff

-- A few lemmas do not use the section variables `[IsProbabilityMeasure μ]` or `[MeasurableSpace Ω]`; keep the declarations uniform.
set_option linter.unusedSectionVars false

namespace OddCycleBound

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded, jointly measurable kernel. -/
structure GoodK (K : Ω → Ω → ℝ) : Prop where
  meas : Measurable (Function.uncurry K)
  bdd : ∃ C, 0 ≤ C ∧ ∀ x y, |K x y| ≤ C

/-- Kernel composition `(K ∘ L)(x,y) = ∫ z, K x z · L z y`. -/
noncomputable def comp (μ : Measure Ω) (K L : Ω → Ω → ℝ) : Ω → Ω → ℝ :=
  fun x y => ∫ z, K x z * L z y ∂μ

/-- The all-ones kernel. -/
def onesKernel : Ω → Ω → ℝ := fun _ _ => 1

/-- Double mean `∫∫ M`. -/
noncomputable def doubleMean (μ : Measure Ω) (M : Ω → Ω → ℝ) : ℝ := ∫ x, ∫ y, M x y ∂μ ∂μ

lemma goodK_onesKernel : GoodK (onesKernel (Ω := Ω)) :=
  ⟨measurable_const, ⟨1, zero_le_one, fun _ _ => by simp [onesKernel]⟩⟩

lemma goodK_of_isGraphon {U : Ω → Ω → ℝ} (hU : IsGraphon U μ) : GoodK U :=
  ⟨hU.meas, ⟨1, zero_le_one, fun x y => by
    rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y⟩⟩

/-- A real simple function is the finite sum of its level indicators weighted
by the corresponding level value. -/
lemma simpleFunc_eq_finset_sum_range_indicator
    {α : Type*} [MeasurableSpace α] (S : SimpleFunc α ℝ) :
    (fun x => S x) =
      fun x =>
        (SimpleFunc.range S).sum fun c =>
          c * ((S ⁻¹' {c}).indicator (fun _ : α => (1 : ℝ)) x) := by
  funext x
  classical
  have hxmem : S x ∈ SimpleFunc.range S := S.mem_range_self x
  rw [Finset.sum_eq_single (S x)]
  · simp [Set.indicator_of_mem]
  · intro c _hc hne
    have hxnot : x ∉ S ⁻¹' {c} := by
      intro hx
      exact hne (by simpa using hx.symm)
    simp [Set.indicator_of_notMem hxnot]
  · intro hnot
    exact (hnot hxmem).elim

/-- The difference of two set indicators is supported by the symmetric
difference. -/
lemma abs_indicator_one_sub_indicator_one_le_indicator_symmDiff
    {α : Type*} (A B : Set α) (x : α) :
    |A.indicator (fun _ : α => (1 : ℝ)) x -
        B.indicator (fun _ : α => (1 : ℝ)) x| ≤
      (A ∆ B).indicator (fun _ : α => (1 : ℝ)) x := by
  classical
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B
  · have hx : x ∉ A ∆ B := by
      simp [Set.mem_symmDiff, hA, hB]
    simp [Set.indicator_of_notMem, hA, hB, hx]
  · have hx : x ∈ A ∆ B := by
      simp [Set.mem_symmDiff, hA, hB]
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hA, hB, hx]
  · have hx : x ∈ A ∆ B := by
      simp [Set.mem_symmDiff, hA, hB]
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hA, hB, hx]
  · have hx : x ∉ A ∆ B := by
      simp [Set.mem_symmDiff, hA, hB]
    simp [Set.indicator_of_notMem, hA, hB, hx]

/-- Finite weighted sums of indicators change only on the corresponding
symmetric differences, with coefficient-weighted error. -/
lemma abs_finset_weighted_indicator_sum_sub_le
    {α ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (A B : ι → Set α) (x : α) :
    |(s.sum fun i => c i *
          (A i).indicator (fun _ : α => (1 : ℝ)) x) -
        (s.sum fun i => c i *
          (B i).indicator (fun _ : α => (1 : ℝ)) x)| ≤
      s.sum fun i => |c i| *
        ((A i ∆ B i).indicator (fun _ : α => (1 : ℝ)) x) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs
    (fun i =>
      c i * (A i).indicator (fun _ : α => (1 : ℝ)) x -
        c i * (B i).indicator (fun _ : α => (1 : ℝ)) x) s).trans ?_
  refine Finset.sum_le_sum ?_
  intro i hi
  calc
    |c i * (A i).indicator (fun _ : α => (1 : ℝ)) x -
        c i * (B i).indicator (fun _ : α => (1 : ℝ)) x|
        = |c i| *
            |(A i).indicator (fun _ : α => (1 : ℝ)) x -
              (B i).indicator (fun _ : α => (1 : ℝ)) x| := by
          rw [← mul_sub, abs_mul]
    _ ≤ |c i| *
          ((A i ∆ B i).indicator (fun _ : α => (1 : ℝ)) x) := by
          exact mul_le_mul_of_nonneg_left
            (abs_indicator_one_sub_indicator_one_le_indicator_symmDiff
              (A i) (B i) x)
            (abs_nonneg _)

/-- Squared finite weighted indicator-sum error is supported on the union of
the symmetric differences of the atoms. -/
lemma sq_finset_weighted_indicator_sum_sub_le_badSet
    {α ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (A B : ι → Set α) (x : α) :
    ((s.sum fun i => c i *
          (A i).indicator (fun _ : α => (1 : ℝ)) x) -
        (s.sum fun i => c i *
          (B i).indicator (fun _ : α => (1 : ℝ)) x)) ^ 2 ≤
      (s.sum fun i => |c i|) ^ 2 *
        ({y : α | ∃ i ∈ s, y ∈ A i ∆ B i}.indicator
          (fun _ : α => (1 : ℝ)) x) := by
  classical
  let D : ℝ :=
    (s.sum fun i => c i *
      (A i).indicator (fun _ : α => (1 : ℝ)) x) -
      (s.sum fun i => c i *
        (B i).indicator (fun _ : α => (1 : ℝ)) x)
  let C : ℝ := s.sum fun i => |c i|
  let Bad : Set α := {y : α | ∃ i ∈ s, y ∈ A i ∆ B i}
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun i _ => abs_nonneg (c i)
  by_cases hxBad : x ∈ Bad
  · have habsD : |D| ≤ C := by
      dsimp [D, C]
      calc
        |(s.sum fun i => c i *
              (A i).indicator (fun _ : α => (1 : ℝ)) x) -
            (s.sum fun i => c i *
              (B i).indicator (fun _ : α => (1 : ℝ)) x)|
            ≤ s.sum fun i => |c i| *
                ((A i ∆ B i).indicator (fun _ : α => (1 : ℝ)) x) :=
              abs_finset_weighted_indicator_sum_sub_le s c A B x
        _ ≤ s.sum fun i => |c i| := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hind :
                  ((A i ∆ B i).indicator (fun _ : α => (1 : ℝ)) x) ≤ 1 := by
                by_cases hx : x ∈ A i ∆ B i
                · simp [Set.indicator_of_mem hx]
                · simp [Set.indicator_of_notMem hx]
              simpa [mul_one] using
                mul_le_mul_of_nonneg_left hind (abs_nonneg (c i))
    have hsq : D ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs D]
      nlinarith [abs_nonneg D, hC0, habsD]
    simpa [D, C, Bad, Set.indicator_of_mem hxBad] using hsq
  · have hterm :
        ∀ i ∈ s,
          (A i).indicator (fun _ : α => (1 : ℝ)) x =
            (B i).indicator (fun _ : α => (1 : ℝ)) x := by
      intro i hi
      have hnot : x ∉ A i ∆ B i := by
        intro hx
        exact hxBad ⟨i, hi, hx⟩
      by_cases hA : x ∈ A i <;> by_cases hB : x ∈ B i
      · simp [Set.indicator_of_mem, hA, hB]
      · have hx : x ∈ A i ∆ B i := by
          simp [Set.mem_symmDiff, hA, hB]
        exact (hnot hx).elim
      · have hx : x ∈ A i ∆ B i := by
          simp [Set.mem_symmDiff, hA, hB]
        exact (hnot hx).elim
      · simp [Set.indicator_of_notMem, hA, hB]
    have hsum :
        (s.sum fun i => c i *
            (A i).indicator (fun _ : α => (1 : ℝ)) x) =
          (s.sum fun i => c i *
            (B i).indicator (fun _ : α => (1 : ℝ)) x) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hterm i hi]
    simp [Bad, hsum, Set.indicator_of_notMem hxBad]

/-- Integral form of `sq_finset_weighted_indicator_sum_sub_le_badSet`.

This turns finite atomwise symmetric-difference control into an `L²` error
bound.  It is the quantitative bridge needed when replacing simple-function
level sets by finite rectangle unions. -/
lemma integral_sq_finset_weighted_indicator_sum_sub_le_badSet
    {α ι : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    (s : Finset ι) (c : ι → ℝ)
    (A B : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hB : ∀ i ∈ s, MeasurableSet (B i)) :
    ∫ x : α,
        ((s.sum fun i => c i *
              (A i).indicator (fun _ : α => (1 : ℝ)) x) -
            (s.sum fun i => c i *
              (B i).indicator (fun _ : α => (1 : ℝ)) x)) ^ 2 ∂ν
      ≤ (s.sum fun i => |c i|) ^ 2 *
        ν.real {x : α | ∃ i ∈ s, x ∈ A i ∆ B i} := by
  classical
  let Bad : Set α := {x : α | ∃ i ∈ s, x ∈ A i ∆ B i}
  let C : ℝ := s.sum fun i => |c i|
  let f : α → ℝ := fun x =>
    ((s.sum fun i => c i *
          (A i).indicator (fun _ : α => (1 : ℝ)) x) -
        (s.sum fun i => c i *
          (B i).indicator (fun _ : α => (1 : ℝ)) x)) ^ 2
  let g : α → ℝ := fun x =>
    C ^ 2 * Bad.indicator (fun _ : α => (1 : ℝ)) x
  have hBad : MeasurableSet Bad := by
    have hBad' : MeasurableSet (⋃ i ∈ s, A i ∆ B i) := by
      refine Finset.measurableSet_biUnion s ?_
      intro i hi
      rw [Set.symmDiff_def]
      exact ((hA i hi).diff (hB i hi)).union ((hB i hi).diff (hA i hi))
    convert hBad' using 1
    ext x
    simp [Bad]
  have hf_nonneg : 0 ≤ᵐ[ν] f := by
    exact ae_of_all _ fun x => sq_nonneg _
  have hg_int : Integrable g ν := by
    have hg_eq : g = Bad.indicator (fun _ : α => C ^ 2) := by
      funext x
      by_cases hx : x ∈ Bad
      · simp [g, Set.indicator_of_mem hx]
      · simp [g, Set.indicator_of_notMem hx]
    rw [hg_eq]
    exact (integrable_const (C ^ 2)).indicator hBad
  have hfg : f ≤ᵐ[ν] g := by
    exact ae_of_all _ fun x => by
      dsimp [f, g, C, Bad]
      exact sq_finset_weighted_indicator_sum_sub_le_badSet s c A B x
  have hmono : ∫ x, f x ∂ν ≤ ∫ x, g x ∂ν :=
    integral_mono_of_nonneg hf_nonneg hg_int hfg
  have hg_eq : (∫ x, g x ∂ν) =
      C ^ 2 * ν.real Bad := by
    have hg_fun : g = Bad.indicator (fun _ : α => C ^ 2) := by
      funext x
      by_cases hx : x ∈ Bad
      · simp [g, Set.indicator_of_mem hx]
      · simp [g, Set.indicator_of_notMem hx]
    rw [hg_fun, integral_indicator_const (C ^ 2) hBad]
    simp [mul_comm]
  rw [hg_eq] at hmono
  simpa [f, C, Bad] using hmono

/-- Sum-of-errors version of
`integral_sq_finset_weighted_indicator_sum_sub_le_badSet`.

The finite union of bad atom sets is bounded by the sum of their real
measures. -/
lemma integral_sq_finset_weighted_indicator_sum_sub_le_sum_symmDiff
    {α ι : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    (s : Finset ι) (c : ι → ℝ)
    (A B : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hB : ∀ i ∈ s, MeasurableSet (B i)) :
    ∫ x : α,
        ((s.sum fun i => c i *
              (A i).indicator (fun _ : α => (1 : ℝ)) x) -
            (s.sum fun i => c i *
              (B i).indicator (fun _ : α => (1 : ℝ)) x)) ^ 2 ∂ν
      ≤ (s.sum fun i => |c i|) ^ 2 *
        (s.sum fun i => ν.real (A i ∆ B i)) := by
  classical
  let Bad : Set α := {x : α | ∃ i ∈ s, x ∈ A i ∆ B i}
  have hbase :=
    integral_sq_finset_weighted_indicator_sum_sub_le_badSet
      (ν := ν) s c A B hA hB
  have hmeasure : ν.real Bad ≤ s.sum fun i => ν.real (A i ∆ B i) := by
    have h :=
      measureReal_biUnion_finset_le (μ := ν) s
        (fun i => A i ∆ B i)
    have hBad_eq : Bad = ⋃ i ∈ s, A i ∆ B i := by
      ext x
      simp [Bad]
    rw [hBad_eq]
    exact h
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hmeasure
      (sq_nonneg (s.sum fun i => |c i|)))

/-- A simple function is close in `L²` to any replacement of its level sets,
with error controlled by the symmetric differences of the level sets.

This is the simple-function version of the finite indicator estimate.  In the
graphon compactness proof, the replacement sets will be finite unions of
measurable rectangles. -/
lemma integral_sq_simpleFunc_sub_levelSet_replacements_le_sum_symmDiff
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    (S : SimpleFunc α ℝ) (T : ℝ → Set α)
    (hT : ∀ c ∈ SimpleFunc.range S, MeasurableSet (T c)) :
    ∫ x : α,
        (S x -
          ((SimpleFunc.range S).sum fun c =>
            c * (T c).indicator (fun _ : α => (1 : ℝ)) x)) ^ 2 ∂ν
      ≤ ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
        ((SimpleFunc.range S).sum fun c =>
          ν.real ((S ⁻¹' {c}) ∆ T c)) := by
  classical
  have hbase :=
    integral_sq_finset_weighted_indicator_sum_sub_le_sum_symmDiff
      (ν := ν) (SimpleFunc.range S) (fun c : ℝ => c)
      (fun c : ℝ => S ⁻¹' {c}) T
      (fun c _hc => S.measurableSet_fiber c) hT
  have hS_point : ∀ x : α,
      S x =
        (SimpleFunc.range S).sum fun c =>
          c * ((S ⁻¹' {c}).indicator (fun _ : α => (1 : ℝ)) x) := by
    intro x
    exact congrFun (simpleFunc_eq_finset_sum_range_indicator S) x
  simpa [hS_point] using hbase

/-- Uniform-error version of
`integral_sq_simpleFunc_sub_levelSet_replacements_le_sum_symmDiff`.

If every replaced level set has symmetric-difference mass at most `η`, then
the whole simple-function square error is bounded by the square of the total
coefficient mass times `#range * η`. -/
lemma integral_sq_simpleFunc_sub_levelSet_replacements_le_uniform_symmDiff
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    (S : SimpleFunc α ℝ) (T : ℝ → Set α)
    (hT : ∀ c ∈ SimpleFunc.range S, MeasurableSet (T c))
    {η : ℝ}
    (hη : ∀ c ∈ SimpleFunc.range S, ν.real ((S ⁻¹' {c}) ∆ T c) ≤ η) :
    ∫ x : α,
        (S x -
          ((SimpleFunc.range S).sum fun c =>
            c * (T c).indicator (fun _ : α => (1 : ℝ)) x)) ^ 2 ∂ν
      ≤ ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
        ((SimpleFunc.range S).card * η) := by
  classical
  have hbase :=
    integral_sq_simpleFunc_sub_levelSet_replacements_le_sum_symmDiff
      (ν := ν) S T hT
  have hsum :
      (SimpleFunc.range S).sum
          (fun c => ν.real ((S ⁻¹' {c}) ∆ T c))
        ≤ (SimpleFunc.range S).sum (fun _c => η) :=
    Finset.sum_le_sum hη
  calc
    ∫ x : α,
        (S x -
          ((SimpleFunc.range S).sum fun c =>
            c * (T c).indicator (fun _ : α => (1 : ℝ)) x)) ^ 2 ∂ν
        ≤ ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
          ((SimpleFunc.range S).sum fun c =>
            ν.real ((S ⁻¹' {c}) ∆ T c)) := hbase
    _ ≤ ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
        ((SimpleFunc.range S).sum fun _c => η) := by
          exact mul_le_mul_of_nonneg_left hsum
            (sq_nonneg ((SimpleFunc.range S).sum fun c => |c|))
    _ = ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
        ((SimpleFunc.range S).card * η) := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- The indicator of a finite pairwise-disjoint union is the sum of the
indicators of its pieces. -/
lemma indicator_biUnion_finset_one_eq_sum_indicator
    {α ι : Type*} (s : Finset ι) (A : ι → Set α)
    (hdisj : (s : Set ι).PairwiseDisjoint A) (x : α) :
    ((s.sup A).indicator (fun _ : α => (1 : ℝ)) x) =
      s.sum fun i => (A i).indicator (fun _ : α => (1 : ℝ)) x := by
  classical
  by_cases hx : ∃ i ∈ s, x ∈ A i
  · rcases hx with ⟨i, hi, hxi⟩
    have hleft : x ∈ s.sup A := by
      rw [Finset.sup_set_eq_biUnion]
      exact Set.mem_iUnion.2
        ⟨i, Set.mem_iUnion.2 ⟨hi, hxi⟩⟩
    rw [Set.indicator_of_mem hleft]
    rw [Finset.sum_eq_single i]
    · simp [Set.indicator_of_mem hxi]
    · intro j hj hji
      have hxj : x ∉ A j := by
        intro hxj
        have hd : Disjoint (A i) (A j) := hdisj hi hj hji.symm
        exact (Set.disjoint_left.mp hd hxi hxj)
      simp [Set.indicator_of_notMem hxj]
    · intro hnot
      exact (hnot hi).elim
  · have hleft_sup : x ∉ s.sup A := by
      rw [Finset.sup_set_eq_biUnion]
      intro hxmem
      rcases Set.mem_iUnion.1 hxmem with ⟨i, hxi'⟩
      rcases Set.mem_iUnion.1 hxi' with ⟨hi, hxi⟩
      exact hx ⟨i, hi, hxi⟩
    rw [Set.indicator_of_notMem hleft_sup]
    symm
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hxi : x ∉ A i := by
      intro hmem
      exact hx ⟨i, hi, hmem⟩
    simp [Set.indicator_of_notMem hxi]

/-- The indicator of the set covered by a finite partition is the sum of the
part indicators. -/
lemma finpartition_sup_indicator_one_eq_sum_parts_indicator
    {α : Type*} {s : Set α} (P : Finpartition s) (x : α) :
    (P.parts.sup id).indicator (fun _ : α => (1 : ℝ)) x =
      P.parts.sum fun p => p.indicator (fun _ : α => (1 : ℝ)) x := by
  classical
  exact indicator_biUnion_finset_one_eq_sum_indicator
    P.parts (fun p : Set α => p) P.disjoint x

/-- Weighted version of `finpartition_sup_indicator_one_eq_sum_parts_indicator`. -/
lemma finpartition_sup_weighted_indicator_one_eq_sum_parts_indicator
    {α : Type*} {s : Set α} (P : Finpartition s) (c : ℝ) (x : α) :
    c * (P.parts.sup id).indicator (fun _ : α => (1 : ℝ)) x =
      P.parts.sum fun p => c * p.indicator (fun _ : α => (1 : ℝ)) x := by
  rw [finpartition_sup_indicator_one_eq_sum_parts_indicator P x,
    Finset.mul_sum]

/-- The indicator of a measurable set, with value `1`, is a bounded strongly
measurable function. -/
lemma good_indicator_one {s : Set Ω} (hs : MeasurableSet s) :
    Good (s.indicator fun _ : Ω => (1 : ℝ)) := by
  refine ⟨stronglyMeasurable_const.indicator hs, 1, zero_le_one, fun x => ?_⟩
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- A separable kernel `(x,y) ↦ a x * b y` built from bounded measurable
factors is a `GoodK` kernel. -/
lemma goodK_separable {a b : Ω → ℝ} (ha : Good a) (hb : Good b) :
    GoodK (fun x y => a x * b y) := by
  obtain ⟨Ca, hCa0, hCa⟩ := ha.bdd
  obtain ⟨Cb, hCb0, hCb⟩ := hb.bdd
  refine ⟨?_, Ca * Cb, mul_nonneg hCa0 hCb0, fun x y => ?_⟩
  · exact ((ha.meas.comp_measurable measurable_fst).mul
      (hb.meas.comp_measurable measurable_snd)).measurable
  · rw [abs_mul]
    exact mul_le_mul (hCa x) (hCb y) (abs_nonneg _) hCa0

/-- Rectangle indicator kernels are separable `GoodK` kernels. -/
lemma goodK_rectIndicator {s t : Set Ω}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    GoodK (fun x y =>
      (s.indicator (fun _ : Ω => (1 : ℝ)) x) *
        (t.indicator (fun _ : Ω => (1 : ℝ)) y)) :=
  goodK_separable (good_indicator_one (Ω := Ω) hs)
    (good_indicator_one (Ω := Ω) ht)

/-- Product-set indicators split as a product of one-dimensional indicators. -/
lemma indicator_prod_one_eq_mul_indicator_one
    {α β : Type*} (s : Set α) (t : Set β) (x : α) (y : β) :
    (s ×ˢ t).indicator (fun _ : α × β => (1 : ℝ)) (x, y) =
      s.indicator (fun _ : α => (1 : ℝ)) x *
        t.indicator (fun _ : β => (1 : ℝ)) y := by
  classical
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ t
  · have hxy : (x, y) ∈ s ×ˢ t := ⟨hx, hy⟩
    simp [Set.indicator_of_mem, hx, hy, hxy]
  · have hxy : (x, y) ∉ s ×ˢ t := by
      intro hmem
      exact hy hmem.2
    simp [Set.indicator_of_notMem, hx, hy, hxy]
  · have hxy : (x, y) ∉ s ×ˢ t := by
      intro hmem
      exact hx hmem.1
    simp [Set.indicator_of_notMem, hx, hy, hxy]
  · have hxy : (x, y) ∉ s ×ˢ t := by
      intro hmem
      exact hx hmem.1
    simp [Set.indicator_of_notMem, hx, hy, hxy]

/-- The zero kernel is `GoodK`. -/
lemma goodK_zero : GoodK (fun _x _y : Ω => (0 : ℝ)) :=
  ⟨measurable_const, 0, le_rfl, fun _ _ => by simp⟩

/-- Sums of `GoodK` kernels are `GoodK`. -/
lemma goodK_add {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) :
    GoodK (fun x y => K x y + L x y) := by
  obtain ⟨CK, hCK0, hCK⟩ := hK.bdd
  obtain ⟨CL, hCL0, hCL⟩ := hL.bdd
  refine ⟨hK.meas.add hL.meas, CK + CL, add_nonneg hCK0 hCL0, fun x y => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hCK x y) (hCL x y))

/-- Finite sums of `GoodK` kernels are `GoodK`. -/
lemma goodK_finset_sum {ι : Type*} (s : Finset ι) (K : ι → Ω → Ω → ℝ)
    (hK : ∀ i ∈ s, GoodK (K i)) :
    GoodK (fun x y => ∑ i ∈ s, K i x y) := by
  classical
  revert hK
  refine Finset.induction_on s ?base ?step
  · intro _hK
    simpa using (goodK_zero (Ω := Ω))
  · intro a s ha ih hK
    have hKa : GoodK (K a) := hK a (by simp)
    have hsum : GoodK (fun x y => ∑ i ∈ s, K i x y) := by
      exact ih fun i hi => hK i (by simp [hi])
    simpa [Finset.sum_insert ha] using goodK_add hKa hsum

lemma goodK_finset_rectIndicator_sum {ι : Type*} (s : Finset ι)
    (A B : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hB : ∀ i ∈ s, MeasurableSet (B i)) :
    GoodK (fun x y =>
      ∑ i ∈ s,
        (A i).indicator (fun _ : Ω => (1 : ℝ)) x *
          (B i).indicator (fun _ : Ω => (1 : ℝ)) y) := by
  exact goodK_finset_sum s
    (fun i x y =>
      (A i).indicator (fun _ : Ω => (1 : ℝ)) x *
        (B i).indicator (fun _ : Ω => (1 : ℝ)) y)
    (fun i hi => goodK_rectIndicator (hA i hi) (hB i hi))

lemma goodK_finset_weighted_rectIndicator_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (A B : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hB : ∀ i ∈ s, MeasurableSet (B i)) :
    GoodK (fun x y =>
      ∑ i ∈ s,
        c i *
          ((A i).indicator (fun _ : Ω => (1 : ℝ)) x *
            (B i).indicator (fun _ : Ω => (1 : ℝ)) y)) := by
  refine goodK_finset_sum s
    (fun i x y =>
      c i *
        ((A i).indicator (fun _ : Ω => (1 : ℝ)) x *
          (B i).indicator (fun _ : Ω => (1 : ℝ)) y)) ?_
  intro i hi
  simpa [mul_assoc] using
    goodK_separable
      (good_smul (c i) (good_indicator_one (Ω := Ω) (hA i hi)))
      (good_indicator_one (Ω := Ω) (hB i hi))

lemma finset_weighted_rectIndicator_sum_eq_separable_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (A B : ι → Set Ω) :
    (fun x y =>
      ∑ i ∈ s,
        c i *
          ((A i).indicator (fun _ : Ω => (1 : ℝ)) x *
            (B i).indicator (fun _ : Ω => (1 : ℝ)) y))
      =
    fun x y =>
      ∑ i ∈ s,
        (c i • (A i).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) x *
          (B i).indicator (fun _ : Ω => (1 : ℝ)) y := by
  funext x y
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [mul_assoc]

lemma good_finset_weighted_rectIndicator_left {ι : Type*}
    (c : ι → ℝ) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (i : ι) :
    Good (c i • (A i).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) :=
  good_smul (c i) (good_indicator_one (Ω := Ω) (hA i))

lemma good_finset_rectIndicator_right {ι : Type*}
    (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (i : ι) :
    Good ((B i).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) :=
  good_indicator_one (Ω := Ω) (hB i)

lemma abs_finset_weighted_rectIndicator_sum_le {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (A B : ι → Set Ω) (x y : Ω) :
    |∑ i ∈ s,
        c i *
          ((A i).indicator (fun _ : Ω => (1 : ℝ)) x *
            (B i).indicator (fun _ : Ω => (1 : ℝ)) y)|
      ≤ ∑ i ∈ s, |c i| := by
  refine (Finset.abs_sum_le_sum_abs
    (fun i =>
      c i *
        ((A i).indicator (fun _ : Ω => (1 : ℝ)) x *
          (B i).indicator (fun _ : Ω => (1 : ℝ)) y)) s).trans ?_
  refine Finset.sum_le_sum ?_
  intro i hi
  rw [abs_mul]
  have hA01 : |(A i).indicator (fun _ : Ω => (1 : ℝ)) x| ≤ 1 := by
    by_cases hx : x ∈ A i
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hB01 : |(B i).indicator (fun _ : Ω => (1 : ℝ)) y| ≤ 1 := by
    by_cases hy : y ∈ B i
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  calc
    |c i| *
        |(A i).indicator (fun _ : Ω => (1 : ℝ)) x *
          (B i).indicator (fun _ : Ω => (1 : ℝ)) y|
        = |c i| *
          (|(A i).indicator (fun _ : Ω => (1 : ℝ)) x| *
            |(B i).indicator (fun _ : Ω => (1 : ℝ)) y|) := by rw [abs_mul]
    _ ≤ |c i| * (1 * 1) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hA01 hB01 (abs_nonneg _) zero_le_one) (abs_nonneg _)
    _ = |c i| := by ring

/-! ### Measurable rectangle semiring -/

/-- Measurable rectangles in the product space. -/
def measurableRectangles (Ω : Type*) [MeasurableSpace Ω] : Set (Set (Ω × Ω)) :=
  Set.image2 (fun s t : Set Ω => s ×ˢ t)
    {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t}

lemma measurableRectangles.mem {s t : Set Ω}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    s ×ˢ t ∈ measurableRectangles Ω :=
  ⟨s, hs, t, ht, rfl⟩

noncomputable def measurableRectangles.left
    {R : Set (Ω × Ω)} (hR : R ∈ measurableRectangles Ω) : Set Ω :=
  Classical.choose hR

lemma measurableRectangles.left_meas
    {R : Set (Ω × Ω)} (hR : R ∈ measurableRectangles Ω) :
    MeasurableSet (measurableRectangles.left (Ω := Ω) hR) :=
  (Classical.choose_spec hR).1

noncomputable def measurableRectangles.right
    {R : Set (Ω × Ω)} (hR : R ∈ measurableRectangles Ω) : Set Ω :=
  Classical.choose (Classical.choose_spec hR).2

lemma measurableRectangles.right_meas
    {R : Set (Ω × Ω)} (hR : R ∈ measurableRectangles Ω) :
    MeasurableSet (measurableRectangles.right (Ω := Ω) hR) :=
  (Classical.choose_spec (Classical.choose_spec hR).2).1

lemma measurableRectangles.prod_eq
    {R : Set (Ω × Ω)} (hR : R ∈ measurableRectangles Ω) :
    measurableRectangles.left (Ω := Ω) hR ×ˢ
      measurableRectangles.right (Ω := Ω) hR = R :=
  (Classical.choose_spec (Classical.choose_spec hR).2).2

lemma measurableSet_of_mem_measurableRectangles
    {R : Set (Ω × Ω)} (hR : R ∈ measurableRectangles Ω) :
    MeasurableSet R := by
  rcases hR with ⟨s, hs, t, ht, rfl⟩
  exact hs.prod ht

lemma measurableSet_finpartition_sup_of_measurableRectangles
    {t : Set (Ω × Ω)} (P : Finpartition t)
    (hP : ↑P.parts ⊆ measurableRectangles Ω) :
    MeasurableSet (P.parts.sup id) := by
  rw [Finset.sup_set_eq_biUnion]
  exact MeasurableSet.biUnion P.parts.finite_toSet.countable
    fun R hR => measurableSet_of_mem_measurableRectangles (Ω := Ω) (hP hR)

lemma measurableRectangles_empty :
    (∅ : Set (Ω × Ω)) ∈ measurableRectangles Ω := by
  simpa using
    (measurableRectangles.mem (Ω := Ω)
      (s := (∅ : Set Ω)) (t := (∅ : Set Ω))
      MeasurableSet.empty MeasurableSet.empty)

lemma measurableRectangles_univ :
    (Set.univ : Set (Ω × Ω)) ∈ measurableRectangles Ω := by
  simpa [Set.univ_prod_univ] using
    (measurableRectangles.mem (Ω := Ω)
      (s := (Set.univ : Set Ω)) (t := (Set.univ : Set Ω))
      MeasurableSet.univ MeasurableSet.univ)

lemma measurableRectangles_inter_mem
    {A B : Set (Ω × Ω)}
    (hA : A ∈ measurableRectangles Ω) (hB : B ∈ measurableRectangles Ω) :
    A ∩ B ∈ measurableRectangles Ω := by
  rcases hA with ⟨s, hs, t, ht, rfl⟩
  rcases hB with ⟨u, hu, v, hv, rfl⟩
  simpa [Set.prod_inter_prod] using
    (measurableRectangles.mem (Ω := Ω)
      (s := s ∩ u) (t := t ∩ v)
      (hs.inter hu) (ht.inter hv))

lemma measurableRectangles_sdiff_eq_sUnion
    {A B : Set (Ω × Ω)}
    (hA : A ∈ measurableRectangles Ω) (hB : B ∈ measurableRectangles Ω) :
    ∃ I : Finset (Set (Ω × Ω)),
      ↑I ⊆ measurableRectangles Ω ∧
        (I : Set (Set (Ω × Ω))).PairwiseDisjoint id ∧
          A \ B = ⋃₀ (I : Set (Set (Ω × Ω))) := by
  classical
  rcases hA with ⟨s, hs, t, ht, rfl⟩
  rcases hB with ⟨u, hu, v, hv, rfl⟩
  let R₀ : Set (Ω × Ω) := (s \ u) ×ˢ t
  let R₁ : Set (Ω × Ω) := (s ∩ u) ×ˢ (t \ v)
  refine ⟨{R₀, R₁}, ?_, ?_, ?_⟩
  · intro R hR
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl
    · exact measurableRectangles.mem (Ω := Ω) (hs.diff hu) ht
    · exact measurableRectangles.mem (Ω := Ω) (hs.inter hu) (ht.diff hv)
  · rw [Set.PairwiseDisjoint, Set.Pairwise]
    intro a ha b hb hne
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hne rfl).elim
    · change Disjoint R₀ R₁
      rw [Set.disjoint_iff_inter_eq_empty]
      ext x
      simp [R₀, R₁]
      tauto
    · change Disjoint R₁ R₀
      rw [Set.disjoint_iff_inter_eq_empty]
      ext x
      simp [R₀, R₁]
      tauto
    · exact (hne rfl).elim
  · rw [Set.prod_sdiff_prod]
    ext x
    simp [R₀, R₁]
    tauto

/-- Measurable rectangles form a set semiring. -/
theorem isSetSemiring_measurableRectangles :
    IsSetSemiring (measurableRectangles Ω) where
  empty_mem := measurableRectangles_empty (Ω := Ω)
  inter_mem := fun _ hs _ ht => measurableRectangles_inter_mem hs ht
  sdiff_eq_sUnion' := fun _ hs _ ht => measurableRectangles_sdiff_eq_sUnion hs ht

lemma generateFrom_measurableRectangles :
    MeasurableSpace.generateFrom (measurableRectangles Ω) =
      (inferInstance : MeasurableSpace (Ω × Ω)) := by
  simpa [measurableRectangles] using
    (generateFrom_prod (α := Ω) (β := Ω))

lemma exists_prod_measure_symmDiff_lt_supClosure_measurableRectangles
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {s : Set (Ω × Ω)} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ supClosure (measurableRectangles Ω),
      μ.prod μ (t ∆ s) < ε := by
  have hcover :
      ∃ D : Set (Set (Ω × Ω)),
        D.Countable ∧ D ⊆ measurableRectangles Ω ∧
          μ.prod μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · intro t ht
      simpa using ht ▸ measurableRectangles_univ (Ω := Ω)
    · simp
  exact
    exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
      (μ := μ.prod μ)
      (mα := inferInstance)
      isSetSemiring_measurableRectangles hcover
      (by rw [eq_comm, generateFrom_measurableRectangles]) hs hε

lemma exists_finpartition_measurableRectangles_symmDiff_lt
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {s : Set (Ω × Ω)} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t, ∃ P : Finpartition t,
      ↑P.parts ⊆ measurableRectangles Ω ∧ μ.prod μ (t ∆ s) < ε := by
  rcases exists_prod_measure_symmDiff_lt_supClosure_measurableRectangles
      (Ω := Ω) μ hs hε with ⟨t, ht, hμt⟩
  rcases (isSetSemiring_measurableRectangles (Ω := Ω)).mem_supClosure_iff.mp ht with
    ⟨P, hP⟩
  exact ⟨t, P, hP, hμt⟩

/-- For `Good`K kernels, the inner integrand `z ↦ K x z · L z y` is integrable. -/
/- A finite partition into measurable rectangles gives an exact finite
rectangle-indicator expansion of the covered set.

This is the algebraic flattening step used after the rectangle semiring
approximation theorem: finite unions of measurable rectangles are finite
separable kernels. -/
lemma exists_rectIndicator_sum_eq_finpartition_sup
    {t : Set (Ω × Ω)} (P : Finpartition t)
    (hP : ↑P.parts ⊆ measurableRectangles Ω) :
    ∃ A B : Set (Ω × Ω) → Set Ω,
      (∀ R ∈ P.parts, MeasurableSet (A R)) ∧
      (∀ R ∈ P.parts, MeasurableSet (B R)) ∧
      (fun x y =>
          (P.parts.sup id).indicator
            (fun _ : Ω × Ω => (1 : ℝ)) (x, y))
        =
        fun x y =>
          P.parts.sum fun R =>
            (A R).indicator (fun _ : Ω => (1 : ℝ)) x *
              (B R).indicator (fun _ : Ω => (1 : ℝ)) y := by
  classical
  let A : Set (Ω × Ω) → Set Ω := fun R =>
    if hR : R ∈ measurableRectangles Ω then
      measurableRectangles.left (Ω := Ω) hR
    else ∅
  let B : Set (Ω × Ω) → Set Ω := fun R =>
    if hR : R ∈ measurableRectangles Ω then
      measurableRectangles.right (Ω := Ω) hR
    else ∅
  refine ⟨A, B, ?_, ?_, ?_⟩
  · intro R hR
    have hrect : R ∈ measurableRectangles Ω := hP hR
    simp [A, hrect, measurableRectangles.left_meas]
  · intro R hR
    have hrect : R ∈ measurableRectangles Ω := hP hR
    simp [B, hrect, measurableRectangles.right_meas]
  · funext x y
    rw [finpartition_sup_indicator_one_eq_sum_parts_indicator P (x, y)]
    refine Finset.sum_congr rfl ?_
    intro R hR
    have hrect : R ∈ measurableRectangles Ω := hP hR
    have hprod := measurableRectangles.prod_eq (Ω := Ω) hrect
    calc
      R.indicator (fun _ : Ω × Ω => (1 : ℝ)) (x, y)
          =
        (measurableRectangles.left (Ω := Ω) hrect ×ˢ
          measurableRectangles.right (Ω := Ω) hrect).indicator
            (fun _ : Ω × Ω => (1 : ℝ)) (x, y) := by
            rw [hprod]
      _ =
          (measurableRectangles.left (Ω := Ω) hrect).indicator
              (fun _ : Ω => (1 : ℝ)) x *
            (measurableRectangles.right (Ω := Ω) hrect).indicator
              (fun _ : Ω => (1 : ℝ)) y := by
            exact indicator_prod_one_eq_mul_indicator_one
              (measurableRectangles.left (Ω := Ω) hrect)
              (measurableRectangles.right (Ω := Ω) hrect) x y
      _ =
          (A R).indicator (fun _ : Ω => (1 : ℝ)) x *
            (B R).indicator (fun _ : Ω => (1 : ℝ)) y := by
            simp [A, B, hrect]

lemma exists_finpartition_sup_rectIndicator_finiteRank_data
    {t : Set (Ω × Ω)} (P : Finpartition t)
    (hP : ↑P.parts ⊆ measurableRectangles Ω) (c : ℝ) :
    ∃ A B : Set (Ω × Ω) → Set Ω,
      (∀ R ∈ P.parts, MeasurableSet (A R)) ∧
      (∀ R ∈ P.parts, MeasurableSet (B R)) ∧
      GoodK
        (fun x y =>
          c * (P.parts.sup id).indicator
            (fun _ : Ω × Ω => (1 : ℝ)) (x, y)) ∧
      (∀ x y,
        |c * (P.parts.sup id).indicator
            (fun _ : Ω × Ω => (1 : ℝ)) (x, y)| ≤ |c|) ∧
      (∀ x y,
        c * (P.parts.sup id).indicator
            (fun _ : Ω × Ω => (1 : ℝ)) (x, y) =
          P.parts.sum fun R =>
            (c • (A R).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) x *
              (B R).indicator (fun _ : Ω => (1 : ℝ)) y) ∧
      (∀ R ∈ P.parts,
        Good (c • (A R).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ)) ∧
      (∀ R ∈ P.parts,
        Good ((B R).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ)) := by
  classical
  rcases exists_rectIndicator_sum_eq_finpartition_sup
      (Ω := Ω) P hP with ⟨A, B, hA, hB, hsum⟩
  refine ⟨A, B, hA, hB, ?_, ?_, ?_, ?_, ?_⟩
  · have hKsum :
        GoodK
          (fun x y =>
            P.parts.sum fun R =>
              c * ((A R).indicator (fun _ : Ω => (1 : ℝ)) x *
                (B R).indicator (fun _ : Ω => (1 : ℝ)) y)) :=
      goodK_finset_weighted_rectIndicator_sum
        (Ω := Ω) P.parts (fun _ : Set (Ω × Ω) => c) A B hA hB
    convert hKsum using 2
    funext y
    rw [congrFun (congrFun hsum _) y, Finset.mul_sum]
  · intro x y
    have hind :
        |(P.parts.sup id).indicator
            (fun _ : Ω × Ω => (1 : ℝ)) (x, y)| ≤ 1 := by
      by_cases hxy : ∃ R ∈ P.parts, (x, y) ∈ R
      · simp [Set.indicator, hxy]
      · simp [Set.indicator, hxy]
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg c) hind
  · intro x y
    calc
      c * (P.parts.sup id).indicator
          (fun _ : Ω × Ω => (1 : ℝ)) (x, y)
          =
        c *
          (P.parts.sum fun R =>
            (A R).indicator (fun _ : Ω => (1 : ℝ)) x *
              (B R).indicator (fun _ : Ω => (1 : ℝ)) y) := by
            rw [congrFun (congrFun hsum x) y]
      _ =
          P.parts.sum fun R =>
            c * ((A R).indicator (fun _ : Ω => (1 : ℝ)) x *
              (B R).indicator (fun _ : Ω => (1 : ℝ)) y) := by
            rw [Finset.mul_sum]
      _ =
          P.parts.sum fun R =>
            (c • (A R).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) x *
              (B R).indicator (fun _ : Ω => (1 : ℝ)) y := by
            exact congrFun
              (congrFun
                (finset_weighted_rectIndicator_sum_eq_separable_sum
                  (Ω := Ω) P.parts (fun _ : Set (Ω × Ω) => c) A B) x) y
  · intro R hR
    exact good_smul c (good_indicator_one (Ω := Ω) (hA R hR))
  · intro R hR
    exact good_indicator_one (Ω := Ω) (hB R hR)

/-- Rectangle replacements of all level sets of a simple function form a
bounded measurable kernel.

This is the `GoodK` half of the finite-rank approximation package: each level
replacement is a finite union of measurable rectangles, hence a finite sum of
separable indicator kernels, and the finite sum over the levels is again
`GoodK`. -/
lemma goodK_simpleFunc_rectangular_replacement
    (S : SimpleFunc (Ω × Ω) ℝ)
    (T : ℝ → Set (Ω × Ω))
    (P : ∀ c, c ∈ SimpleFunc.range S → Finpartition (T c))
    (hP : ∀ c (hc : c ∈ SimpleFunc.range S),
      ↑(P c hc).parts ⊆ measurableRectangles Ω) :
    GoodK
      (fun x y =>
        (SimpleFunc.range S).sum fun c =>
          c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) (x, y)) := by
  classical
  refine goodK_finset_sum (Ω := Ω) (SimpleFunc.range S)
    (fun c x y =>
      c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) (x, y)) ?_
  intro c hc
  rcases exists_finpartition_sup_rectIndicator_finiteRank_data
      (Ω := Ω) (P c hc) (hP c hc) c with
    ⟨_A, _B, _hA, _hB, hGoodK, _hbound, _hsep, _ha, _hb⟩
  simpa [(P c hc).sup_parts] using hGoodK

/-- Uniform pointwise bound for a rectangle-step replacement of a simple
function. -/
lemma abs_simpleFunc_rectangular_replacement_le
    (S : SimpleFunc (Ω × Ω) ℝ)
    (T : ℝ → Set (Ω × Ω))
    (P : ∀ c, c ∈ SimpleFunc.range S → Finpartition (T c))
    (hP : ∀ c (hc : c ∈ SimpleFunc.range S),
      ↑(P c hc).parts ⊆ measurableRectangles Ω)
    (x y : Ω) :
    |(SimpleFunc.range S).sum fun c =>
        c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) (x, y)|
      ≤ (SimpleFunc.range S).sum fun c => |c| := by
  classical
  refine (Finset.abs_sum_le_sum_abs
    (fun c =>
      c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) (x, y))
    (SimpleFunc.range S)).trans ?_
  refine Finset.sum_le_sum ?_
  intro c hc
  rcases exists_finpartition_sup_rectIndicator_finiteRank_data
      (Ω := Ω) (P c hc) (hP c hc) c with
    ⟨_A, _B, _hA, _hB, _hGoodK, hbound, _hsep, _ha, _hb⟩
  simpa [(P c hc).sup_parts] using hbound x y

/-- Rectangle replacements of the level sets of a simple function are exact
finite separable kernels.

The finite index type is the dependent sum of a level value and one rectangle
piece in that level's finite partition.  This is the bookkeeping lemma needed
to turn the measure-theoretic rectangle approximation into the finite-rank
data consumed by the Hilbert-Schmidt compactness bridge. -/
lemma exists_simpleFunc_rectangular_replacement_finiteRank_data
    (S : SimpleFunc (Ω × Ω) ℝ)
    (T : ℝ → Set (Ω × Ω))
    (P : ∀ c, c ∈ SimpleFunc.range S → Finpartition (T c))
    (hP : ∀ c (hc : c ∈ SimpleFunc.range S),
      ↑(P c hc).parts ⊆ measurableRectangles Ω) :
    ∃ J : Type u, ∃ hJ : Fintype J,
    ∃ K : Ω → Ω → ℝ, ∃ Bnd : ℝ,
    ∃ a b : J → Ω → ℝ,
      (∀ x y,
        K x y =
          (SimpleFunc.range S).sum fun c =>
            c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) (x, y)) ∧
      GoodK K ∧
      0 ≤ Bnd ∧
      (∀ x y, |K x y| ≤ Bnd) ∧
      (∀ j, Good (a j)) ∧
      (∀ j, Good (b j)) ∧
      (∀ j, (Set.range (a j)).Finite) ∧
      (∀ j, (Set.range (b j)).Finite) ∧
      (∀ x y, K x y = (@Finset.univ J hJ).sum
        (fun j : J => a j x * b j y)) := by
  classical
  let Cidx := {c // c ∈ SimpleFunc.range S}
  have hdata :
      ∀ c : Cidx,
        ∃ A B : Set (Ω × Ω) → Set Ω,
          (∀ R ∈ (P c.1 c.2).parts, MeasurableSet (A R)) ∧
          (∀ R ∈ (P c.1 c.2).parts, MeasurableSet (B R)) ∧
          GoodK
            (fun x y =>
              c.1 * ((P c.1 c.2).parts.sup id).indicator
                (fun _ : Ω × Ω => (1 : ℝ)) (x, y)) ∧
          (∀ x y,
            |c.1 * ((P c.1 c.2).parts.sup id).indicator
              (fun _ : Ω × Ω => (1 : ℝ)) (x, y)| ≤ |c.1|) ∧
          (∀ x y,
            c.1 * ((P c.1 c.2).parts.sup id).indicator
              (fun _ : Ω × Ω => (1 : ℝ)) (x, y) =
              (P c.1 c.2).parts.sum fun R =>
                (c.1 • (A R).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) x *
                  (B R).indicator (fun _ : Ω => (1 : ℝ)) y) ∧
          (∀ R ∈ (P c.1 c.2).parts,
            Good (c.1 • (A R).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ)) ∧
          (∀ R ∈ (P c.1 c.2).parts,
            Good ((B R).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ)) := by
    intro c
    exact exists_finpartition_sup_rectIndicator_finiteRank_data
      (Ω := Ω) (P c.1 c.2) (hP c.1 c.2) c.1
  choose A B hA hB hGood hBound hSep ha hb using hdata
  let Ridx := fun c : Cidx =>
    {R : Set (Ω × Ω) // R ∈ (P c.1 c.2).parts}
  let J := Sigma Ridx
  letI : Fintype Cidx := Finset.Subtype.fintype (SimpleFunc.range S)
  letI : ∀ c : Cidx, Fintype (Ridx c) := fun c =>
    Finset.Subtype.fintype ((P c.1 c.2).parts)
  let hJ : Fintype J := inferInstance
  let K : Ω → Ω → ℝ := fun x y =>
    (SimpleFunc.range S).sum fun c =>
      c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) (x, y)
  let Bnd : ℝ := (SimpleFunc.range S).sum fun c => |c|
  let a : J → Ω → ℝ := fun j =>
    (j.1.1 • (A j.1 j.2.1).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ)
  let b : J → Ω → ℝ := fun j =>
    (B j.1 j.2.1).indicator (fun _ : Ω => (1 : ℝ))
  refine ⟨J, hJ, K, Bnd, a, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    rfl
  · dsimp [K]
    exact goodK_simpleFunc_rectangular_replacement (Ω := Ω) S T P hP
  · dsimp [Bnd]
    exact Finset.sum_nonneg fun c _hc => abs_nonneg c
  · intro x y
    dsimp [K, Bnd]
    exact abs_simpleFunc_rectangular_replacement_le (Ω := Ω) S T P hP x y
  · intro j
    dsimp [a]
    exact ha j.1 j.2.1 j.2.2
  · intro j
    dsimp [b]
    exact hb j.1 j.2.1 j.2.2
  · intro j
    refine (Set.finite_singleton (0 : ℝ)).insert (j.1.1 : ℝ) |>.subset ?_
    rintro z ⟨x, rfl⟩
    dsimp [a]
    by_cases hx : x ∈ A j.1 j.2.1 <;> simp [Set.indicator, hx]
  · intro j
    refine (Set.finite_singleton (0 : ℝ)).insert (1 : ℝ) |>.subset ?_
    rintro z ⟨x, rfl⟩
    dsimp [b]
    by_cases hx : x ∈ B j.1 j.2.1 <;> simp [Set.indicator, hx]
  · intro x y
    dsimp [K, a, b, J, Ridx]
    calc
      ((SimpleFunc.range S).sum fun c =>
          c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) (x, y))
          =
        (∑ c : Cidx,
          c.1 * (T c.1).indicator (fun _ : Ω × Ω => (1 : ℝ)) (x, y)) := by
            exact (Finset.sum_coe_sort (SimpleFunc.range S)
              (fun c =>
                c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) (x, y))).symm
      _ =
        (∑ c : Cidx,
          ((P c.1 c.2).parts.sum fun R =>
            (c.1 • (A c R).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) x *
              (B c R).indicator (fun _ : Ω => (1 : ℝ)) y)) := by
            refine Finset.sum_congr rfl ?_
            intro c _hc
            simpa [(P c.1 c.2).sup_parts] using hSep c x y
      _ =
        (∑ c : Cidx,
          ∑ R : {R : Set (Ω × Ω) // R ∈ (P c.1 c.2).parts},
            (c.1 • (A c R.1).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) x *
              (B c R.1).indicator (fun _ : Ω => (1 : ℝ)) y) := by
            refine Finset.sum_congr rfl ?_
            intro c _hc
            exact (Finset.sum_coe_sort ((P c.1 c.2).parts)
              (fun R =>
                (c.1 • (A c R).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) x *
                  (B c R).indicator (fun _ : Ω => (1 : ℝ)) y)).symm
      _ =
        (∑ j : Sigma (fun c : Cidx =>
            {R : Set (Ω × Ω) // R ∈ (P c.1 c.2).parts}),
          (j.1.1 • (A j.1 j.2.1).indicator (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) x *
            (B j.1 j.2.1).indicator (fun _ : Ω => (1 : ℝ)) y) := by
            exact (Fintype.sum_sigma
              (fun j : Sigma (fun c : Cidx =>
                {R : Set (Ω × Ω) // R ∈ (P c.1 c.2).parts}) =>
                (j.1.1 • (A j.1 j.2.1).indicator
                    (fun _ : Ω => (1 : ℝ)) : Ω → ℝ) x *
                  (B j.1 j.2.1).indicator
                    (fun _ : Ω => (1 : ℝ)) y)).symm

/-- Uniform square-error control for replacing the level sets of a simple
function on `Ω × Ω` by finite unions of measurable rectangles.

This is the deterministic estimate behind the finite-rank approximation
argument: once each atom of a simple function is approximated by a finite
rectangle union with real symmetric-difference mass at most `η`, the whole
simple-function error is bounded uniformly. -/
lemma integral_sq_simpleFunc_sub_rectangular_levelSet_replacements_le_uniform_symmDiff
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : SimpleFunc (Ω × Ω) ℝ)
    (T : ℝ → Set (Ω × Ω))
    (P : ∀ c, c ∈ SimpleFunc.range S → Finpartition (T c))
    (hP : ∀ c (hc : c ∈ SimpleFunc.range S),
      ↑(P c hc).parts ⊆ measurableRectangles Ω)
    {η : ℝ}
    (hη : ∀ c ∈ SimpleFunc.range S,
      (μ.prod μ).real ((S ⁻¹' {c}) ∆ T c) ≤ η) :
    ∫ p : Ω × Ω,
        (S p -
          ((SimpleFunc.range S).sum fun c =>
            c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) p)) ^ 2
        ∂(μ.prod μ)
      ≤ ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
        ((SimpleFunc.range S).card * η) := by
  classical
  refine
    integral_sq_simpleFunc_sub_levelSet_replacements_le_uniform_symmDiff
      (ν := μ.prod μ) S T ?_ hη
  intro c hc
  rw [← (P c hc).sup_parts]
  exact measurableSet_finpartition_sup_of_measurableRectangles
    (Ω := Ω) (P c hc) (hP c hc)

/-- Existence of finite-rectangle replacements for all level sets of a simple
function, with a uniform real symmetric-difference error bound. -/
lemma exists_rectangular_levelSet_replacements_uniform_symmDiff
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : SimpleFunc (Ω × Ω) ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ → Set (Ω × Ω),
    ∃ P : ∀ c, c ∈ SimpleFunc.range S → Finpartition (T c),
      (∀ c (hc : c ∈ SimpleFunc.range S),
        ↑(P c hc).parts ⊆ measurableRectangles Ω) ∧
      (∀ c ∈ SimpleFunc.range S,
        (μ.prod μ).real ((S ⁻¹' {c}) ∆ T c) ≤ η) := by
  classical
  have hex :
      ∀ c ∈ SimpleFunc.range S,
        ∃ t, ∃ P : Finpartition t,
          ↑P.parts ⊆ measurableRectangles Ω ∧
          μ.prod μ (t ∆ (S ⁻¹' {c})) < ENNReal.ofReal η := by
    intro c _hc
    exact exists_finpartition_measurableRectangles_symmDiff_lt
      (Ω := Ω) μ (S.measurableSet_fiber c)
      (ENNReal.ofReal_pos.mpr hη)
  choose Tatom Patom hrect herr using hex
  let T : ℝ → Set (Ω × Ω) := fun c =>
    if hc : c ∈ SimpleFunc.range S then Tatom c hc else ∅
  let P : ∀ c, c ∈ SimpleFunc.range S → Finpartition (T c) := fun c hc =>
    (Patom c hc).copy (by dsimp [T]; rw [dif_pos hc])
  refine ⟨T, P, ?_, ?_⟩
  · intro c hc
    dsimp [P]
    simpa using hrect c hc
  · intro c hc
    have hlt : μ.prod μ (T c ∆ (S ⁻¹' {c})) < ENNReal.ofReal η := by
      dsimp [T]
      rw [dif_pos hc]
      exact herr c hc
    have hle : μ.prod μ (T c ∆ (S ⁻¹' {c})) ≤ ENNReal.ofReal η := le_of_lt hlt
    have hreal :
        (μ.prod μ).real (T c ∆ (S ⁻¹' {c})) ≤ η :=
      ENNReal.toReal_le_of_le_ofReal hη.le hle
    simpa [symmDiff_comm] using hreal

/-- Combined rectangle-replacement theorem for simple functions: for any
positive uniform atom error `η`, there are finite-rectangle replacements of
all level sets, and the resulting rectangle-step function satisfies the
global square-integral estimate. -/
lemma exists_rectangular_levelSet_replacements_integral_sq_bound
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : SimpleFunc (Ω × Ω) ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ → Set (Ω × Ω),
    ∃ P : ∀ c, c ∈ SimpleFunc.range S → Finpartition (T c),
      (∀ c (hc : c ∈ SimpleFunc.range S),
        ↑(P c hc).parts ⊆ measurableRectangles Ω) ∧
      (∫ p : Ω × Ω,
          (S p -
            ((SimpleFunc.range S).sum fun c =>
              c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) p)) ^ 2
          ∂(μ.prod μ)
        ≤ ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
          ((SimpleFunc.range S).card * η)) := by
  classical
  rcases exists_rectangular_levelSet_replacements_uniform_symmDiff
      (Ω := Ω) μ S hη with ⟨T, P, hP, herr⟩
  refine ⟨T, P, hP, ?_⟩
  exact
    integral_sq_simpleFunc_sub_rectangular_levelSet_replacements_le_uniform_symmDiff
      (Ω := Ω) μ S T P hP herr

/-- Finite-rank rectangle-step approximation of a simple function, with the
same square-integral error bound as the underlying rectangle replacement.

This packages the measurable-rectangle approximation and the finite separable
kernel bookkeeping in one statement. -/
lemma exists_simpleFunc_rectangular_finiteRank_data_integral_sq_bound
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : SimpleFunc (Ω × Ω) ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ J : Type u, ∃ hJ : Fintype J,
    ∃ K : Ω → Ω → ℝ, ∃ Bnd : ℝ,
    ∃ a b : J → Ω → ℝ,
      GoodK K ∧
      0 ≤ Bnd ∧
      (∀ x y, |K x y| ≤ Bnd) ∧
      (∀ j, Good (a j)) ∧
      (∀ j, Good (b j)) ∧
      (∀ j, (Set.range (a j)).Finite) ∧
      (∀ j, (Set.range (b j)).Finite) ∧
      (∀ x y, K x y = (@Finset.univ J hJ).sum
        (fun j : J => a j x * b j y)) ∧
      (∫ p : Ω × Ω, (S p - K p.1 p.2) ^ 2 ∂(μ.prod μ)
        ≤ ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
          ((SimpleFunc.range S).card * η)) := by
  classical
  rcases exists_rectangular_levelSet_replacements_integral_sq_bound
      (Ω := Ω) μ S hη with
    ⟨T, P, hP, hInt⟩
  rcases exists_simpleFunc_rectangular_replacement_finiteRank_data
      (Ω := Ω) S T P hP with
    ⟨J, hJ, K, Bnd, a, b, hKdef, hK, hB0, hKB, ha, hb, hfa, hfb, hsep⟩
  refine ⟨J, hJ, K, Bnd, a, b, hK, hB0, hKB, ha, hb, hfa, hfb, hsep, ?_⟩
  calc
    ∫ p : Ω × Ω, (S p - K p.1 p.2) ^ 2 ∂(μ.prod μ)
        =
      ∫ p : Ω × Ω,
        (S p -
          ((SimpleFunc.range S).sum fun c =>
            c * (T c).indicator (fun _ : Ω × Ω => (1 : ℝ)) p)) ^ 2
        ∂(μ.prod μ) := by
          apply integral_congr_ae
          exact ae_of_all _ fun p => by
            simpa using
              congrArg (fun z : ℝ => (S p - z) ^ 2) (hKdef p.1 p.2)
    _ ≤ ((SimpleFunc.range S).sum fun c => |c|) ^ 2 *
          ((SimpleFunc.range S).card * η) := hInt

lemma integrable_KL {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) (x y : Ω) :
    Integrable (fun z => K x z * L z y) μ := by
  obtain ⟨Ck, _, hCk⟩ := hK.bdd
  obtain ⟨Cl, hCl0, hCl⟩ := hL.bdd
  have hmK : Measurable (fun z => K x z) := hK.meas.comp (measurable_prodMk_left)
  have hmL : Measurable (fun z => L z y) := hL.meas.comp (measurable_id.prodMk measurable_const)
  refine (integrable_const (Ck * Cl)).mono' (hmK.mul hmL).aestronglyMeasurable (ae_of_all _ ?_)
  intro z
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hCk x z) (hCl z y) (abs_nonneg _) (le_trans (abs_nonneg _) (hCk x z))

lemma goodK_comp {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) : GoodK (comp μ K L) := by
  obtain ⟨Ck, hCk0, hCk⟩ := hK.bdd
  obtain ⟨Cl, hCl0, hCl⟩ := hL.bdd
  refine ⟨?_, ⟨Ck * Cl, mul_nonneg hCk0 hCl0, fun x y => ?_⟩⟩
  · -- measurability of `(x,y) ↦ ∫ z, K x z * L z y`
    have hSM : StronglyMeasurable (fun q : (Ω × Ω) × Ω => K q.1.1 q.2 * L q.2 q.1.2) := by
      have h1 : Measurable (fun q : (Ω × Ω) × Ω => K q.1.1 q.2) :=
        hK.meas.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      have h2 : Measurable (fun q : (Ω × Ω) × Ω => L q.2 q.1.2) :=
        hL.meas.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
      exact (h1.mul h2).stronglyMeasurable
    exact (hSM.integral_prod_right').measurable
  · -- the bound
    calc |comp μ K L x y| ≤ ∫ z, |K x z * L z y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _z, Ck * Cl ∂μ := by
          refine integral_mono (integrable_KL hK hL x y).abs (integrable_const _) (fun z => ?_)
          rw [abs_mul]
          exact mul_le_mul (hCk x z) (hCl z y) (abs_nonneg _) hCk0
      _ = Ck * Cl := by simp

/-! ### Integrability helpers for `GoodK` kernels -/

lemma GoodK.integrable_row {K : Ω → Ω → ℝ} (hK : GoodK K) (x : Ω) :
    Integrable (fun y => K x y) μ := by
  obtain ⟨C, _, hC⟩ := hK.bdd
  have hm : Measurable (fun y => K x y) := hK.meas.comp measurable_prodMk_left
  exact (integrable_const C).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC x y)

lemma GoodK.integrable_col {K : Ω → Ω → ℝ} (hK : GoodK K) (y : Ω) :
    Integrable (fun x => K x y) μ := by
  obtain ⟨C, _, hC⟩ := hK.bdd
  have hm : Measurable (fun x => K x y) := hK.meas.comp (measurable_id.prodMk measurable_const)
  exact (integrable_const C).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x y)

lemma GoodK.integrable_prod {K : Ω → Ω → ℝ} (hK : GoodK K) :
    Integrable (Function.uncurry K) (μ.prod μ) := by
  obtain ⟨C, _, hC⟩ := hK.bdd
  exact (integrable_const C).mono' hK.meas.aestronglyMeasurable
    (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hC p.1 p.2)

lemma GoodK.colsum_stronglyMeasurable {K : Ω → Ω → ℝ} (hK : GoodK K) :
    StronglyMeasurable (fun y => ∫ x, K x y ∂μ) :=
  (show StronglyMeasurable (Function.uncurry K) from hK.meas.stronglyMeasurable).integral_prod_left

lemma GoodK.colsum_integrable {K : Ω → Ω → ℝ} (hK : GoodK K) :
    Integrable (fun y => ∫ x, K x y ∂μ) μ := by
  obtain ⟨C, _, hC⟩ := hK.bdd
  refine (integrable_const C).mono' hK.colsum_stronglyMeasurable.aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  calc |∫ x, K x y ∂μ| ≤ ∫ x, |K x y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, C ∂μ := integral_mono (hK.integrable_col y).abs (integrable_const C) (fun x => hC x y)
    _ = C := by simp

/-! ### Bilinearity of composition (in each argument) -/

lemma comp_add_left {K₁ K₂ L : Ω → Ω → ℝ} (hK₁ : GoodK K₁) (hK₂ : GoodK K₂) (hL : GoodK L) :
    comp μ (fun x y => K₁ x y + K₂ x y) L = fun x y => comp μ K₁ L x y + comp μ K₂ L x y := by
  funext x y
  simp only [comp]
  rw [← integral_add (integrable_KL hK₁ hL x y) (integrable_KL hK₂ hL x y)]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_add_right {K L₁ L₂ : Ω → Ω → ℝ} (hK : GoodK K) (hL₁ : GoodK L₁) (hL₂ : GoodK L₂) :
    comp μ K (fun x y => L₁ x y + L₂ x y) = fun x y => comp μ K L₁ x y + comp μ K L₂ x y := by
  funext x y
  simp only [comp]
  rw [← integral_add (integrable_KL hK hL₁ x y) (integrable_KL hK hL₂ x y)]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_smul_left (c : ℝ) (K L : Ω → Ω → ℝ) :
    comp μ (fun x y => c * K x y) L = fun x y => c * comp μ K L x y := by
  funext x y
  simp only [comp]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_smul_right (c : ℝ) (K L : Ω → Ω → ℝ) :
    comp μ K (fun x y => c * L x y) = fun x y => c * comp μ K L x y := by
  funext x y
  simp only [comp]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_neg_left (K L : Ω → Ω → ℝ) :
    comp μ (fun x y => -K x y) L = fun x y => -comp μ K L x y := by
  funext x y; simp only [comp]; rw [← integral_neg]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_sub_left {K₁ K₂ L : Ω → Ω → ℝ} (hK₁ : GoodK K₁) (hK₂ : GoodK K₂) (hL : GoodK L) :
    comp μ (fun x y => K₁ x y - K₂ x y) L = fun x y => comp μ K₁ L x y - comp μ K₂ L x y := by
  funext x y
  simp only [comp]
  rw [← integral_sub (integrable_KL hK₁ hL x y) (integrable_KL hK₂ hL x y)]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

lemma comp_sub_right {K L₁ L₂ : Ω → Ω → ℝ} (hK : GoodK K) (hL₁ : GoodK L₁) (hL₂ : GoodK L₂) :
    comp μ K (fun x y => L₁ x y - L₂ x y) = fun x y => comp μ K L₁ x y - comp μ K L₂ x y := by
  funext x y
  simp only [comp]
  rw [← integral_sub (integrable_KL hK hL₁ x y) (integrable_KL hK hL₂ x y)]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

/-! ### The cut lemma: `onesKernel ∘ M ∘ onesKernel = (∫∫ M) · onesKernel` -/

/-- Right multiplication by `onesKernel` integrates out the second variable: `(M ∘ onesKernel)(x,y) = ∫ M x ·`. -/
lemma comp_onesKernel_right (M : Ω → Ω → ℝ) :
    comp μ M onesKernel = fun x _ => ∫ z, M x z ∂μ := by
  funext x y; simp [comp, onesKernel]

/-- Left multiplication by `onesKernel` integrates out the first variable. -/
lemma comp_onesKernel_left (M : Ω → Ω → ℝ) :
    comp μ onesKernel M = fun _ y => ∫ z, M z y ∂μ := by
  funext x y; simp [comp, onesKernel]

/-- `onesKernel` is idempotent under composition. -/
lemma comp_onesKernel_onesKernel : comp μ (onesKernel (Ω := Ω)) onesKernel = onesKernel := by
  funext x y; simp [comp, onesKernel]

/-- **The cut lemma.**  `onesKernel ∘ M ∘ onesKernel = (∫∫ M) · onesKernel`: a `onesKernel`-flanked block collapses to its
double mean times `onesKernel`.  This is the arc-factorization mechanism. -/
lemma cut (M : Ω → Ω → ℝ) :
    comp μ onesKernel (comp μ M onesKernel) = fun _ _ => doubleMean μ M := by
  rw [comp_onesKernel_right]
  funext x y
  simp only [comp, onesKernel, one_mul]
  rfl

/-! ### Associativity of composition (Fubini) -/

lemma comp_assoc {K L M : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) (hM : GoodK M) :
    comp μ (comp μ K L) M = comp μ K (comp μ L M) := by
  funext x y
  obtain ⟨Ck, _, hCk⟩ := hK.bdd
  obtain ⟨Cl, _, hCl⟩ := hL.bdd
  obtain ⟨Cm, _, hCm⟩ := hM.bdd
  have hSM : StronglyMeasurable (Function.uncurry fun w z => K x z * L z w * M w y) := by
    have h1 : Measurable (fun p : Ω × Ω => K x p.2) := hK.meas.comp (measurable_const.prodMk measurable_snd)
    have h2 : Measurable (fun p : Ω × Ω => L p.2 p.1) := hL.meas.comp (measurable_snd.prodMk measurable_fst)
    have h3 : Measurable (fun p : Ω × Ω => M p.1 y) := hM.meas.comp (measurable_fst.prodMk measurable_const)
    exact ((h1.mul h2).mul h3).stronglyMeasurable
  have hInt : Integrable (Function.uncurry fun w z => K x z * L z w * M w y) (μ.prod μ) := by
    refine (integrable_const (Ck * Cl * Cm)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨w, z⟩
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (mul_le_mul (hCk x z) (hCl z w) (abs_nonneg _) (le_trans (abs_nonneg _) (hCk x z)))
      (hCm w y) (abs_nonneg _)
      (mul_nonneg (le_trans (abs_nonneg _) (hCk x z)) (le_trans (abs_nonneg _) (hCl z w)))
  have hL1 : ∀ w, comp μ K L x w * M w y = ∫ z, K x z * L z w * M w y ∂μ := by
    intro w; simp only [comp]; rw [← integral_mul_const]
  have hR1 : ∀ z, K x z * comp μ L M z y = ∫ w, K x z * L z w * M w y ∂μ := by
    intro z; simp only [comp]; rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun w => by ring)
  calc comp μ (comp μ K L) M x y
      = ∫ w, comp μ K L x w * M w y ∂μ := rfl
    _ = ∫ w, ∫ z, K x z * L z w * M w y ∂μ ∂μ := integral_congr_ae (ae_of_all _ hL1)
    _ = ∫ z, ∫ w, K x z * L z w * M w y ∂μ ∂μ := integral_integral_swap hInt
    _ = ∫ z, K x z * comp μ L M z y ∂μ := (integral_congr_ae (ae_of_all _ hR1)).symm
    _ = comp μ K (comp μ L M) x y := rfl

/-! ### Kernel powers and the cyclic trace -/

/-- `compPow K n` is the `(n+1)`-fold composition `K ∘ K ∘ ⋯ ∘ K` (so `compPow K 0 = K`). -/
noncomputable def compPow (μ : Measure Ω) (K : Ω → Ω → ℝ) : ℕ → (Ω → Ω → ℝ)
  | 0 => K
  | (n + 1) => comp μ K (compPow μ K n)

lemma goodK_compPow {K : Ω → Ω → ℝ} (hK : GoodK K) : ∀ n, GoodK (compPow μ K n)
  | 0 => hK
  | (n + 1) => goodK_comp hK (goodK_compPow hK n)

lemma compPow_onesKernel : ∀ n, compPow μ (onesKernel (Ω := Ω)) n = onesKernel
  | 0 => rfl
  | (n + 1) => by rw [compPow, compPow_onesKernel n, comp_onesKernel_onesKernel]

/-- The trace `trace K = ∫ x, K x x`.  The cycle density is `t(C_m, K) = trace (compPow K (m−1))`. -/
noncomputable def trace (μ : Measure Ω) (K : Ω → Ω → ℝ) : ℝ := ∫ x, K x x ∂μ

lemma trace_onesKernel : trace μ (onesKernel (Ω := Ω)) = 1 := by simp [trace, onesKernel]

/-- **Trace cyclic-invariance** (the necklace-rotation primitive): `trace (A ∘ B) = trace (B ∘ A)`. -/
lemma trace_comp_comm {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) :
    trace μ (comp μ A B) = trace μ (comp μ B A) := by
  obtain ⟨Ca, _, hCa⟩ := hA.bdd
  obtain ⟨Cb, _, hCb⟩ := hB.bdd
  have hint : Integrable (Function.uncurry fun x z => A x z * B z x) (μ.prod μ) := by
    have hm : Measurable (Function.uncurry fun x z => A x z * B z x) :=
      (hA.meas.comp (measurable_fst.prodMk measurable_snd)).mul
        (hB.meas.comp (measurable_snd.prodMk measurable_fst))
    refine (integrable_const (Ca * Cb)).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hCa p.1 p.2) (hCb p.2 p.1) (abs_nonneg _) (le_trans (abs_nonneg _) (hCa p.1 p.2))
  have h1 : trace μ (comp μ A B) = ∫ x, ∫ z, A x z * B z x ∂μ ∂μ := rfl
  have h2 : trace μ (comp μ B A) = ∫ x, ∫ z, B x z * A z x ∂μ ∂μ := rfl
  rw [h1, h2, integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun z => ?_))
  ring

/-- `trace (onesKernel ∘ M) = ∫∫ M`. -/
lemma trace_comp_onesKernel {M : Ω → Ω → ℝ} (hM : GoodK M) : trace μ (comp μ onesKernel M) = doubleMean μ M := by
  have hint : Integrable (Function.uncurry fun x z => M z x) (μ.prod μ) := by
    obtain ⟨C, _, hC⟩ := hM.bdd
    have hm : Measurable (Function.uncurry fun x z => M z x) :=
      hM.meas.comp (measurable_snd.prodMk measurable_fst)
    exact (integrable_const C).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hC p.2 p.1)
  show ∫ x, comp μ onesKernel M x x ∂μ = doubleMean μ M
  simp only [comp, onesKernel, one_mul]
  rw [integral_integral_swap hint]; rfl

/-- `trace (M ∘ onesKernel) = ∫∫ M`. -/
lemma trace_comp_onesKernel_right {M : Ω → Ω → ℝ} : trace μ (comp μ M onesKernel) = doubleMean μ M := by
  show ∫ x, comp μ M onesKernel x x ∂μ = doubleMean μ M
  simp only [comp, onesKernel, mul_one]; rfl

/-- The diagonal of a `GoodK` kernel is integrable. -/
lemma GoodK.diag_integrable {K : Ω → Ω → ℝ} (hK : GoodK K) :
    Integrable (fun x => K x x) μ := by
  obtain ⟨C, _, hC⟩ := hK.bdd
  have hm : Measurable (fun x => K x x) := hK.meas.comp (measurable_id.prodMk measurable_id)
  exact (integrable_const C).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x x)

/-- Additivity of the trace over a pointwise difference of `GoodK` kernels. -/
lemma trace_sub {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) :
    trace μ (fun x y => A x y - B x y) = trace μ A - trace μ B := by
  show ∫ x, (A x x - B x x) ∂μ = (∫ x, A x x ∂μ) - ∫ x, B x x ∂μ
  exact integral_sub hA.diag_integrable hB.diag_integrable

/-- The row-broadcast `(x,y) ↦ f x` of a `Good` function is a `GoodK` kernel. -/
lemma goodK_rowBroadcast {f : Ω → ℝ} (hf : Good f) : GoodK (fun _x _y => f _x) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  exact ⟨hf.meas.measurable.comp measurable_fst, ⟨C, hC0, fun x _ => hC x⟩⟩

end OddCycleBound
