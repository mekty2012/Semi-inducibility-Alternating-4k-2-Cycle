import AlternatingCycle.Defs
import AlternatingCycle.Foundation.GraphonL2Operator

/-!
# Even cycle densities are nonnegative

For a symmetric kernel `K` and even cycle length `2m`,

```
  t(C_{2m}, K) = trace (K^{∘(2m−1)}) = trace (M ∘ M) = ∫∫ M²  ≥  0,      M := K^{∘(m−1)},
```

because the `2m`-fold composite splits as the square of the `m`-fold one, and powers of a symmetric
kernel are symmetric.  This is what turns the strengthened inequality of `Main.lean` into the bound
`Alt_{2m}(W) ≤ 4^{-m}`.
-/

open MeasureTheory OddCycleBound OddCycleBound.Spectral.L2Kernel

set_option linter.unusedSectionVars false

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A kernel commutes with its own powers. -/
lemma compPow_comm {K : Ω → Ω → ℝ} (hK : GoodK K) : ∀ n : ℕ,
    comp μ (compPow μ K n) K = comp μ K (compPow μ K n)
  | 0 => rfl
  | n + 1 => by
      show comp μ (comp μ K (compPow μ K n)) K = comp μ K (comp μ K (compPow μ K n))
      rw [comp_assoc hK (goodK_compPow hK n) hK, compPow_comm hK n]

/-- Powers of a symmetric kernel are symmetric. -/
lemma compPow_symm {K : Ω → Ω → ℝ} (hK : GoodK K) (hs : ∀ x y, K x y = K y x) :
    ∀ (n : ℕ) (x y : Ω), compPow μ K n x y = compPow μ K n y x
  | 0, x, y => hs x y
  | n + 1, x, y => by
      have h1 : comp μ K (compPow μ K n) y x = comp μ (compPow μ K n) K x y := by
        show (∫ z, K y z * compPow μ K n z x ∂μ) = ∫ z, compPow μ K n x z * K z y ∂μ
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        show K y z * compPow μ K n z x = compPow μ K n x z * K z y
        rw [hs y z, compPow_symm hK hs n z x]
        ring
      show comp μ K (compPow μ K n) x y = comp μ K (compPow μ K n) y x
      rw [h1, compPow_comm hK n]

/-- Composites add: `K^{∘(a+b+1)} = K^{∘a} ∘ K^{∘b}`. -/
lemma compPow_add {K : Ω → Ω → ℝ} (hK : GoodK K) (b : ℕ) : ∀ a : ℕ,
    compPow μ K (a + b + 1) = comp μ (compPow μ K a) (compPow μ K b)
  | 0 => by
      have hidx : 0 + b + 1 = b + 1 := by omega
      rw [hidx]
      rfl
  | a + 1 => by
      have hidx : a + 1 + b + 1 = a + b + 1 + 1 := by omega
      rw [hidx]
      show comp μ K (compPow μ K (a + b + 1)) = _
      rw [compPow_add hK b a, ← comp_assoc hK (goodK_compPow hK a) (goodK_compPow hK b)]
      rfl

/-- **Even cycle densities are nonnegative.**  `t(C_{2m}, K) = ∫∫ (K^{∘m})² ≥ 0` for symmetric
`K`. -/
theorem signedCycleDensity_nonneg {K : Ω → Ω → ℝ} (hK : GoodK K) (hs : ∀ x y, K x y = K y x)
    (t : ℕ) : 0 ≤ signedCycleDensity K μ (2 * (t + 1)) := by
  have hidx : 2 * (t + 1) - 1 = t + t + 1 := by omega
  rw [signedCycleDensity, hidx, compPow_add hK t t]
  have hsq : comp μ (compPow μ K t) (compPow μ K t) = compPow μ (compPow μ K t) 1 := rfl
  rw [hsq, trace_compPow_one_eq_kernelSqNorm_of_symm (compPow_symm hK hs t)]
  exact kernelSqNorm_nonneg

/-- The signed kernel of a graphon is symmetric. -/
lemma sgn_symm (hW : IsGraphon W μ) (x y : Ω) : sgn W x y = sgn W y x := by
  show 2 * W x y - 1 = 2 * W y x - 1
  rw [hW.symm x y]

end AlternatingCycle
