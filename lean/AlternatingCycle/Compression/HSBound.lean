import AlternatingCycle.Compression.L2

/-!
# The Hilbert–Schmidt bound

For any finite orthonormal family `v` in `L²(μ)`,

```
  ∑ᵢ ‖X vᵢ‖²  =  ∫ₓ ∑ᵢ ⟨K(x,·), vᵢ⟩² dx  ≤  ∫ₓ ‖K(x,·)‖² dx  =  ∫∫ K²  ≤  1,
```

the middle step being Bessel's inequality applied for each fixed `x` to a *finite* orthonormal
family; no Hilbert–Schmidt theory, no Parseval and no trace-class are needed.  The first equality
is `coeFn_opX` of `Compression/L2.lean`: the rows of `X` are `K(x, ·)`.

`Compression/Krylov.lean` applies this to an orthonormal eigenbasis of the Krylov compression `C`,
where `‖C vᵢ‖ ≤ ‖X vᵢ‖` because `C = Π X` on the Krylov space; that turns the sum on the left into
`Tr(A²)` for the diagonal matrix `A` of eigenvalues.
-/

open MeasureTheory OddCycleBound OddCycleBound.Spectral.L2Kernel Finset
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ}

/-! ### `Good`-ness of the signed transform on arbitrary `L²` inputs -/

lemma good_const (c : ℝ) : Good (fun _ : Ω => c) :=
  ⟨stronglyMeasurable_const, |c|, abs_nonneg c, fun _ => le_rfl⟩

lemma good_kernelOp_sgn_l2 (hW : IsGraphon W μ) (f : Lp ℝ 2 μ) :
    Good (kernelOp (sgn W) μ (fun y => f y)) := by
  have h : kernelOp (sgn W) μ (fun y => f y)
      = fun x => 2 * kernelOp W μ (fun y => f y) x - (∫ y, f y ∂μ) :=
    funext (kernelOp_sgn_apply hW f)
  rw [h]
  exact good_sub (good_smul 2 (good_kernelOp_l2 (mu := μ) hW f)) (good_const _)

/-- The row functional `x ↦ ⟨K(x,·), f⟩`. -/
lemma rowInner_eq (hW : IsGraphon W μ) (f : Lp ℝ 2 μ) (x : Ω) :
    inner ℝ (goodL2 (mu := μ) (goodK_row (goodK_sgn hW) x)) f
      = kernelOp (sgn W) μ (fun y => f y) x :=
  inner_goodK_row_l2_eq_kernelOp (mu := μ) (goodK_sgn hW) f x

lemma integrable_rowInner_sq (hW : IsGraphon W μ) (f : Lp ℝ 2 μ) :
    Integrable (fun x => (inner ℝ (goodL2 (mu := μ) (goodK_row (goodK_sgn hW) x)) f) ^ 2) μ := by
  have hgood : Good (fun x : Ω =>
      kernelOp (sgn W) μ (fun y => f y) x * kernelOp (sgn W) μ (fun y => f y) x) :=
    (good_kernelOp_sgn_l2 hW f).mul (good_kernelOp_sgn_l2 hW f)
  refine hgood.integrable.congr (ae_of_all _ fun x => ?_)
  show kernelOp (sgn W) μ (fun y => f y) x * kernelOp (sgn W) μ (fun y => f y) x
      = (inner ℝ (goodL2 (mu := μ) (goodK_row (goodK_sgn hW) x)) f) ^ 2
  rw [rowInner_eq hW f x, sq]

/-! ### The row-energy identity for `X` -/

lemma norm_sq_eq_integral_mul (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, (f x) * (f x) ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun x => by simp [sq])

/-- `‖X f‖²` is the integrated square of the row functional. -/
theorem norm_opX_sq_eq (hW : IsGraphon W μ) (f : Lp ℝ 2 μ) :
    ‖opX hW f‖ ^ 2
      = ∫ x, (inner ℝ (goodL2 (mu := μ) (goodK_row (goodK_sgn hW) x)) f) ^ 2 ∂μ := by
  rw [norm_sq_eq_integral_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_opX hW f] with x hx
  rw [hx, rowInner_eq hW f x, sq]

/-! ### The bound -/

/-- `∫∫ K² ≤ 1` for `K = 2W − 1` on a probability space. -/
theorem kernelSqNorm_sgn_le_one (hW : IsGraphon W μ) : kernelSqNorm μ (sgn W) ≤ 1 := by
  have hrow : ∀ x : Ω, (∫ y, sgn W x y * sgn W x y ∂μ) ≤ 1 := by
    intro x
    have hbdd : ∀ y, sgn W x y * sgn W x y ≤ 1 := by
      intro y
      have h0 := hW.nonneg x y
      have h1 := hW.le_one x y
      show (2 * W x y - 1) * (2 * W x y - 1) ≤ 1
      nlinarith
    have hint : Integrable (fun y => sgn W x y * sgn W x y) μ :=
      ((goodK_row (goodK_sgn hW) x).mul (goodK_row (goodK_sgn hW) x)).integrable
    calc (∫ y, sgn W x y * sgn W x y ∂μ) ≤ ∫ _y : Ω, (1 : ℝ) ∂μ :=
          integral_mono hint (integrable_const 1) hbdd
      _ = 1 := by simp
  have hintrow : Integrable (fun x => ∫ y, sgn W x y * sgn W x y ∂μ) μ :=
    (good_kernelSqRow (mu := μ) (goodK_sgn hW)).integrable
  calc kernelSqNorm μ (sgn W) = ∫ x, (∫ y, sgn W x y * sgn W x y ∂μ) ∂μ := rfl
    _ ≤ ∫ _x : Ω, (1 : ℝ) ∂μ := integral_mono hintrow (integrable_const 1) hrow
    _ = 1 := by simp

/-- **The Hilbert–Schmidt bound.**  Bessel for each fixed `x`, then integrate. -/
theorem sum_norm_opX_sq_le (hW : IsGraphon W μ) {ι : Type*} [Fintype ι] {v : ι → Lp ℝ 2 μ}
    (hv : Orthonormal ℝ v) : ∑ i, ‖opX hW (v i)‖ ^ 2 ≤ 1 := by
  classical
  set row : Ω → Lp ℝ 2 μ := fun x => goodL2 (mu := μ) (goodK_row (goodK_sgn hW) x) with hrow
  -- each term is an integrated square of the row functional
  have hterm : ∀ i, ‖opX hW (v i)‖ ^ 2 = ∫ x, (inner ℝ (row x) (v i)) ^ 2 ∂μ :=
    fun i => norm_opX_sq_eq hW (v i)
  have hint : ∀ i, Integrable (fun x => (inner ℝ (row x) (v i)) ^ 2) μ :=
    fun i => integrable_rowInner_sq hW (v i)
  -- Bessel, for each fixed `x`
  have hbessel : ∀ x : Ω, ∑ i, (inner ℝ (row x) (v i)) ^ 2 ≤ ‖row x‖ ^ 2 := by
    intro x
    have := hv.sum_inner_products_le (s := (univ : Finset ι)) (row x)
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (row x) (v i), Real.norm_eq_abs, sq_abs]
  have hnormrow : Integrable (fun x => ‖row x‖ ^ 2) μ := by
    refine (integrable_goodK_row_inner_self (mu := μ) (goodK_sgn hW)).congr
      (ae_of_all _ fun x => ?_)
    exact real_inner_self_eq_norm_sq _
  calc ∑ i, ‖opX hW (v i)‖ ^ 2 = ∑ i, ∫ x, (inner ℝ (row x) (v i)) ^ 2 ∂μ := by
        exact Finset.sum_congr rfl fun i _ => hterm i
    _ = ∫ x, ∑ i, (inner ℝ (row x) (v i)) ^ 2 ∂μ :=
        (integral_finsetSum _ fun i _ => hint i).symm
    _ ≤ ∫ x, ‖row x‖ ^ 2 ∂μ :=
        integral_mono (integrable_finsetSum _ fun i _ => hint i) hnormrow hbessel
    _ = kernelSqNorm μ (sgn W) := by
        refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_))
          (integral_goodK_row_inner_self_eq_kernelSqNorm (mu := μ) (goodK_sgn hW))
        exact (real_inner_self_eq_norm_sq _).symm
    _ ≤ 1 := kernelSqNorm_sgn_le_one hW

end AlternatingCycle
