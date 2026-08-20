import AlternatingCycle.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# From traces to integrals

`Defs.lean` defines the two densities as traces of kernel powers.  This file proves they are the
integrals over `Ω^r` of a cyclic product.

Everything runs through one statement, `trace_compList_eq_cycleIntegral`: for any list of bounded
measurable kernels `M₀, …, M_{r−1}`,

```
  trace (M₀ ∘ M₁ ∘ ⋯ ∘ M_{r−1}) = ∫_{Ω^r} ∏_{i<r} Mᵢ (xᵢ, x_{i+1})        (indices cyclic)
```

Both densities are instances: `t(C_r, K)` takes every `Mᵢ = K`, and `Alt_{2m}(W)` takes the
alternating list `W, U, W, U, …`, which is why the `m`-fold trace of `W ∘ U` becomes a `2m`-fold
integral without a separate argument.

The proof is an induction along an open path (`chainProd`), with `Fin.cons` peeling one coordinate
at a time out of the product measure (`integral_pi_succ`), and a final step closing the path into a
cycle (`cycleProd_eq_chainProd`).
-/

open MeasureTheory OddCycleBound Finset

set_option linter.unusedSectionVars false

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Fubini for `Measure.pi`, one coordinate at a time -/

/-- Peel the first coordinate off an integral against a finite product measure. -/
lemma integral_pi_succ {n : ℕ} (F : (Fin (n + 1) → Ω) → ℝ)
    (hF : Integrable F (Measure.pi fun _ => μ)) :
    ∫ x, F x ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫ a, ∫ z, F (Fin.cons a z) ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0 with he
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => μ)
      (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  have hsymm : MeasurePreserving e.symm (μ.prod (Measure.pi fun _ : Fin n => μ))
      (Measure.pi fun _ : Fin (n + 1) => μ) := hmp.symm e
  have hcomp : Integrable (fun p => F (e.symm p)) (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
    (hsymm.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  have hpoint : ∀ (a : Ω) (z : Fin n → Ω), e.symm (a, z) = Fin.cons a z := by
    intro a z
    exact Fin.insertNth_zero' a z
  calc ∫ x, F x ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫ x, (fun p => F (e.symm p)) (e x) ∂(Measure.pi fun _ : Fin (n + 1) => μ) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp
    _ = ∫ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) :=
        hmp.integral_comp' (fun p => F (e.symm p))
    _ = ∫ a, ∫ z, F (e.symm (a, z)) ∂(Measure.pi fun _ : Fin n => μ) ∂μ :=
        integral_prod _ hcomp
    _ = ∫ a, ∫ z, F (Fin.cons a z) ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
        simp only [hpoint]

/-! ### Paths -/

/-- The product of `n+1` kernel values along the path `x → w 0 → ⋯ → w (n−1) → y`. -/
def chainProd : ∀ {n : ℕ}, (Fin (n + 1) → (Ω → Ω → ℝ)) → Ω → (Fin n → Ω) → Ω → ℝ
  | 0, M, x, _, y => M 0 x y
  | _ + 1, M, x, w, y => M 0 x (w 0) * chainProd (fun i => M i.succ) (w 0) (fun i => w i.succ) y

@[simp] lemma chainProd_zero (M : Fin 1 → (Ω → Ω → ℝ)) (x : Ω) (w : Fin 0 → Ω) (y : Ω) :
    chainProd M x w y = M 0 x y := rfl

lemma chainProd_succ {n : ℕ} (M : Fin (n + 2) → (Ω → Ω → ℝ)) (x : Ω) (w : Fin (n + 1) → Ω)
    (y : Ω) :
    chainProd M x w y
      = M 0 x (w 0) * chainProd (fun i => M i.succ) (w 0) (fun i => w i.succ) y := rfl

/-- The ordered composition `M₀ ∘ M₁ ∘ ⋯ ∘ M_n`. -/
noncomputable def compList (μ : Measure Ω) :
    ∀ {n : ℕ}, (Fin (n + 1) → (Ω → Ω → ℝ)) → (Ω → Ω → ℝ)
  | 0, M => M 0
  | _ + 1, M => comp μ (M 0) (compList μ fun i => M i.succ)

@[simp] lemma compList_zero (M : Fin 1 → (Ω → Ω → ℝ)) : compList μ M = M 0 := rfl

lemma compList_succ {n : ℕ} (M : Fin (n + 2) → (Ω → Ω → ℝ)) :
    compList μ M = comp μ (M 0) (compList μ fun i => M i.succ) := rfl

lemma goodK_compList : ∀ {n : ℕ} (M : Fin (n + 1) → (Ω → Ω → ℝ)), (∀ i, GoodK (M i)) →
    GoodK (compList μ M)
  | 0, _, hM => hM 0
  | _ + 1, _, hM => goodK_comp (hM 0) (goodK_compList _ fun i => hM i.succ)

/-! ### Measurability and boundedness of the path product -/

lemma measurable_chainProd : ∀ {n : ℕ} (M : Fin (n + 1) → (Ω → Ω → ℝ)), (∀ i, GoodK (M i)) →
    ∀ y : Ω, Measurable fun p : Ω × (Fin n → Ω) => chainProd M p.1 p.2 y
  | 0, M, hM, y => (hM 0).meas.comp (measurable_fst.prodMk measurable_const)
  | n + 1, M, hM, y => by
      have h1 : Measurable fun p : Ω × (Fin (n + 1) → Ω) => M 0 p.1 (p.2 0) :=
        (hM 0).meas.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      have h2 := measurable_chainProd (fun i => M i.succ) (fun i => hM i.succ) y
      have h3 : Measurable fun p : Ω × (Fin (n + 1) → Ω) =>
          ((p.2 0 : Ω), fun i : Fin n => p.2 i.succ) :=
        ((measurable_pi_apply 0).comp measurable_snd).prodMk
          (measurable_pi_iff.2 fun i => (measurable_pi_apply i.succ).comp measurable_snd)
      exact h1.mul (h2.comp h3)

lemma abs_chainProd_le : ∀ {n : ℕ} (M : Fin (n + 1) → (Ω → Ω → ℝ)) (C : Fin (n + 1) → ℝ),
    (∀ i, 0 ≤ C i) → (∀ i x y, |M i x y| ≤ C i) →
    ∀ (x : Ω) (w : Fin n → Ω) (y : Ω), |chainProd M x w y| ≤ ∏ i, C i
  | 0, M, C, _, hC, x, w, y => by
      rw [chainProd_zero, Fin.prod_univ_one]
      exact hC 0 x y
  | n + 1, M, C, hC0, hC, x, w, y => by
      rw [chainProd_succ, abs_mul, Fin.prod_univ_succ]
      refine mul_le_mul (hC 0 x (w 0))
        (abs_chainProd_le (fun i => M i.succ) (fun i => C i.succ) (fun i => hC0 i.succ)
          (fun i => hC i.succ) (w 0) (fun i => w i.succ) y) (abs_nonneg _) (hC0 0)

lemma integrable_chainProd {n : ℕ} (M : Fin (n + 1) → (Ω → Ω → ℝ)) (hM : ∀ i, GoodK (M i))
    (x y : Ω) : Integrable (fun w : Fin n → Ω => chainProd M x w y)
      (Measure.pi fun _ => μ) := by
  classical
  obtain ⟨C, hC0, hC⟩ : ∃ C : Fin (n + 1) → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ i x y, |M i x y| ≤ C i := by
    refine ⟨fun i => (hM i).bdd.choose, fun i => (hM i).bdd.choose_spec.1,
      fun i => (hM i).bdd.choose_spec.2⟩
  have hmeas : Measurable fun w : Fin n → Ω => chainProd M x w y := by
    have := measurable_chainProd M hM y
    exact this.comp (measurable_const.prodMk measurable_id)
  refine Integrable.mono' (integrable_const (∏ i, C i)) hmeas.aestronglyMeasurable
    (ae_of_all _ fun w => ?_)
  rw [Real.norm_eq_abs]
  exact abs_chainProd_le M C hC0 hC x w y

/-! ### The composition is the path integral -/

/-- **The path form.**  Composing `n+1` kernels integrates the product along a path over the `n`
interior vertices. -/
theorem compList_eq_integral_chainProd : ∀ {n : ℕ} (M : Fin (n + 1) → (Ω → Ω → ℝ)),
    (∀ i, GoodK (M i)) → ∀ x y : Ω,
      compList μ M x y = ∫ w : Fin n → Ω, chainProd M x w y ∂(Measure.pi fun _ => μ)
  | 0, M, hM, x, y => by
      rw [compList_zero]
      simp
  | n + 1, M, hM, x, y => by
      have hM' : ∀ i : Fin (n + 1), GoodK (M i.succ) := fun i => hM i.succ
      rw [compList_succ]
      show (∫ z, M 0 x z * compList μ (fun i => M i.succ) z y ∂μ) = _
      rw [integral_pi_succ (fun w : Fin (n + 1) → Ω => chainProd M x w y)
        (integrable_chainProd M hM x y)]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      show M 0 x z * compList μ (fun i => M i.succ) z y
        = ∫ w : Fin n → Ω, chainProd M x (Fin.cons z w) y ∂(Measure.pi fun _ => μ)
      rw [compList_eq_integral_chainProd (fun i : Fin (n + 1) => M i.succ) hM' z y,
        ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      show M 0 x z * chainProd (fun i => M i.succ) z w y = chainProd M x (Fin.cons z w) y
      conv_rhs => rw [chainProd_succ]
      simp

/-! ### Closing the path into a cycle -/

/-- The cyclic product `∏ᵢ Mᵢ (vᵢ, v_{i+1})`, indices read in `Fin (n+1)`, so `v_{n+1} = v_0`. -/
def cycleProd {n : ℕ} (M : Fin (n + 1) → (Ω → Ω → ℝ)) (v : Fin (n + 1) → Ω) : ℝ :=
  ∏ i, M i (v i) (v (i + 1))

/-- Stepping one vertex forward in a cycle written as `Fin.cons`. -/
lemma cons_add_one {n : ℕ} (x : Ω) (w : Fin n → Ω) (i : Fin (n + 1)) :
    (Fin.cons x w : Fin (n + 1) → Ω) (i + 1) = (Fin.snoc w x : Fin (n + 1) → Ω) i := by
  refine Fin.lastCases ?_ ?_ i
  · have hlast : (Fin.last n) + 1 = (0 : Fin (n + 1)) := by
      ext; simp
    rw [hlast, Fin.cons_zero, Fin.snoc_last]
  · intro j
    have hstep : (j.castSucc : Fin (n + 1)) + 1 = j.succ := by
      have hj : (j : ℕ) < n := j.isLt
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega)
      ext
      rw [Fin.val_add, Fin.val_castSucc, hone, Fin.val_succ]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hstep, Fin.cons_succ, Fin.snoc_castSucc]

/-- `snoc` commutes with taking the tail. -/
lemma snoc_succ {n : ℕ} (w : Fin (n + 1) → Ω) (y : Ω) (i : Fin (n + 1)) :
    (Fin.snoc w y : Fin (n + 2) → Ω) i.succ
      = (Fin.snoc (fun j : Fin n => w j.succ) y : Fin (n + 1) → Ω) i := by
  refine Fin.lastCases ?_ ?_ i
  · have hl : (Fin.last n).succ = Fin.last (n + 1) := rfl
    rw [hl, Fin.snoc_last, Fin.snoc_last]
  · intro j
    have h1 : (j.castSucc : Fin (n + 1)).succ = (j.succ : Fin (n + 1)).castSucc := rfl
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- Re-assembling a tuple from its head and tail. -/
lemma cons_head_tail {n : ℕ} (w : Fin (n + 1) → Ω) (i : Fin (n + 1)) :
    (Fin.cons (w 0) (fun j : Fin n => w j.succ) : Fin (n + 1) → Ω) i = w i := by
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero]
  · intro j; rw [Fin.cons_succ]

/-- **The path product, in vector form.**  The `Fin`-indexed product of the kernels along
`x → w 0 → ⋯ → w (n−1) → y` is `chainProd`. -/
theorem prod_path_eq_chainProd : ∀ {n : ℕ} (M : Fin (n + 1) → (Ω → Ω → ℝ)) (x : Ω)
    (w : Fin n → Ω) (y : Ω),
    (∏ i, M i ((Fin.cons x w : Fin (n + 1) → Ω) i) ((Fin.snoc w y : Fin (n + 1) → Ω) i))
      = chainProd M x w y
  | 0, M, x, w, y => by
      rw [Fin.prod_univ_one, chainProd_zero]
      have h0 : (Fin.snoc w y : Fin 1 → Ω) 0 = y := by
        have hz : (0 : Fin 1) = Fin.last 0 := rfl
        rw [hz, Fin.snoc_last]
      rw [Fin.cons_zero, h0]
  | n + 1, M, x, w, y => by
      rw [Fin.prod_univ_succ, chainProd_succ]
      have hhead : M 0 ((Fin.cons x w : Fin (n + 2) → Ω) 0) ((Fin.snoc w y : Fin (n + 2) → Ω) 0)
          = M 0 x (w 0) := by
        have hz : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
        rw [Fin.cons_zero, hz, Fin.snoc_castSucc]
      have htail : (∏ i : Fin (n + 1), M i.succ ((Fin.cons x w : Fin (n + 2) → Ω) i.succ)
            ((Fin.snoc w y : Fin (n + 2) → Ω) i.succ))
          = chainProd (fun i => M i.succ) (w 0) (fun i => w i.succ) y := by
        rw [← prod_path_eq_chainProd (fun i => M i.succ) (w 0) (fun i => w i.succ) y]
        exact Finset.prod_congr rfl fun i _ => by
          rw [Fin.cons_succ, snoc_succ, cons_head_tail]
      rw [hhead, htail]

/-- **The cyclic form.**  The trace of an ordered composition is the integral of the cyclic
product over `Ω^{n+1}`. -/
theorem trace_compList_eq_cycleIntegral {n : ℕ} (M : Fin (n + 1) → (Ω → Ω → ℝ))
    (hM : ∀ i, GoodK (M i)) :
    trace μ (compList μ M)
      = ∫ v : Fin (n + 1) → Ω, cycleProd M v ∂(Measure.pi fun _ => μ) := by
  classical
  obtain ⟨C, hC0, hC⟩ : ∃ C : Fin (n + 1) → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ i x y, |M i x y| ≤ C i :=
    ⟨fun i => (hM i).bdd.choose, fun i => (hM i).bdd.choose_spec.1,
      fun i => (hM i).bdd.choose_spec.2⟩
  have hfac : ∀ i : Fin (n + 1), Measurable fun v : Fin (n + 1) → Ω => M i (v i) (v (i + 1)) := by
    intro i
    have h : Measurable fun v : Fin (n + 1) → Ω => ((v i : Ω), (v (i + 1) : Ω)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply (i + 1))
    exact (hM i).meas.comp h
  have hmeas : Measurable fun v : Fin (n + 1) → Ω => cycleProd M v :=
    Finset.measurable_prod _ fun i _ => hfac i
  have hint : Integrable (fun v : Fin (n + 1) → Ω => cycleProd M v) (Measure.pi fun _ => μ) := by
    refine Integrable.mono' (integrable_const (∏ i, C i)) hmeas.aestronglyMeasurable
      (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, cycleProd, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hC i _ _
  rw [integral_pi_succ _ hint, trace]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show compList μ M x x = ∫ w : Fin n → Ω, cycleProd M (Fin.cons x w) ∂(Measure.pi fun _ => μ)
  rw [compList_eq_integral_chainProd M hM x x]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  show chainProd M x w x = cycleProd M (Fin.cons x w)
  rw [cycleProd, ← prod_path_eq_chainProd M x w x]
  exact Finset.prod_congr rfl fun i _ => by rw [cons_add_one]

/-! ### The two densities as integrals -/

/-- A kernel power is the composition of a constant list. -/
lemma compPow_eq_compList (K : Ω → Ω → ℝ) : ∀ n : ℕ,
    compPow μ K n = compList μ (fun _ : Fin (n + 1) => K)
  | 0 => rfl
  | n + 1 => by
      rw [compPow, compList_succ, compPow_eq_compList K n]

/-- **`t(C_r, K)` is the cyclic integral.**  For a bounded measurable kernel and `r = n+1`
vertices. -/
theorem signedCycleDensity_eq_integral {K : Ω → Ω → ℝ} (hK : GoodK K) (n : ℕ) :
    signedCycleDensity K μ (n + 1)
      = ∫ v : Fin (n + 1) → Ω, ∏ i, K (v i) (v (i + 1)) ∂(Measure.pi fun _ => μ) := by
  rw [signedCycleDensity, Nat.add_sub_cancel, compPow_eq_compList,
    trace_compList_eq_cycleIntegral _ (fun _ => hK)]
  rfl

/-- The alternating list `W, 1−W, W, 1−W, …` of `2t+2` kernels. -/
def altKernels (W : Ω → Ω → ℝ) (t : ℕ) : Fin (2 * t + 2) → (Ω → Ω → ℝ) :=
  fun i => if Even (i : ℕ) then W else cmpl W

lemma altKernels_zero (W : Ω → Ω → ℝ) (t : ℕ) : altKernels W t 0 = W := by
  simp [altKernels]

lemma altKernels_one (W : Ω → Ω → ℝ) (t : ℕ) : altKernels W t 1 = cmpl W := by
  simp [altKernels, Nat.mod_eq_of_lt]

lemma altKernels_succ_succ (W : Ω → Ω → ℝ) (t : ℕ) (i : Fin (2 * t + 2)) :
    altKernels W (t + 1) i.succ.succ = altKernels W t i := by
  have hval : ((i.succ.succ : Fin (2 * (t + 1) + 2)) : ℕ) = (i : ℕ) + 2 := rfl
  simp only [altKernels, hval]
  congr 1
  simp [Nat.even_add]

lemma goodK_altKernels (hW : IsGraphon W μ) (t : ℕ) (i : Fin (2 * t + 2)) :
    GoodK (altKernels W t i) := by
  rw [altKernels]
  split
  · exact goodK_of_isGraphon hW
  · exact goodK_cmpl hW

/-- The alternating list of `2t+2` kernels composes to the `(t+1)`-fold composite of `W ∘ (1−W)`. -/
lemma compList_altKernels (hW : IsGraphon W μ) : ∀ t : ℕ,
    compList μ (altKernels W t) = compPow μ (comp μ W (cmpl W)) t
  | 0 => by
      show comp μ (altKernels W 0 0) (compList μ fun i => altKernels W 0 i.succ) = _
      rw [altKernels_zero]
      show comp μ W (altKernels W 0 (1 : Fin 1).succ) = _
      norm_num [altKernels, compPow]
  | t + 1 => by
      have hWg := goodK_of_isGraphon hW
      have hUg := goodK_cmpl hW
      show comp μ (altKernels W (t + 1) 0)
        (compList μ fun i => altKernels W (t + 1) i.succ) = _
      have hstep : (compList μ fun i => altKernels W (t + 1) i.succ)
          = comp μ (cmpl W) (compPow μ (comp μ W (cmpl W)) t) := by
        show comp μ (altKernels W (t + 1) (0 : Fin (2 * (t + 1) + 1)).succ)
          (compList μ fun i => altKernels W (t + 1) i.succ.succ) = _
        rw [show (altKernels W (t + 1) (0 : Fin (2 * (t + 1) + 1)).succ) = cmpl W from
          altKernels_one W (t + 1)]
        congr 1
        rw [← compList_altKernels hW t]
        congr 1
        funext i
        exact altKernels_succ_succ W t i
      rw [hstep, altKernels_zero, ← comp_assoc hWg hUg (goodK_compPow (goodK_comp hWg hUg) t)]
      rfl

/-- **`Alt_{2m}(W)` is the alternating cyclic integral**, over `Ω^{2m}`. -/
theorem altDensity_eq_integral (hW : IsGraphon W μ) (t : ℕ) :
    altDensity W μ (t + 1)
      = ∫ v : Fin (2 * t + 2) → Ω,
          ∏ i, altKernels W t i (v i) (v (i + 1)) ∂(Measure.pi fun _ => μ) := by
  rw [altDensity, Nat.add_sub_cancel, ← compList_altKernels hW t,
    trace_compList_eq_cycleIntegral _ (goodK_altKernels hW t)]
  rfl

end AlternatingCycle
