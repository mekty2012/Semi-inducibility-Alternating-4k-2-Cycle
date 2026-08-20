import AlternatingCycle.Compression.Krylov
import AlternatingCycle.Necklace.MatrixInstance
import AlternatingCycle.Fubini
import AlternatingCycle.Positivity

/-!
# The alternating-cycle theorem for arbitrary graphons

The two halves of the proof meet here.

* **Fact A** (`Necklace/KernelInstance.lean` and `Necklace/MatrixInstance.lean`) writes both the
  graphon densities and the matrix traces as the *same* universal expression `N_m` in the moments —
  `∑ coeff alt μ (2m) a b · μ_{a+b}`, with the coefficients defined once in `Necklace/RankOne.lean`.
* **Fact B** (`Compression/L2.lean`, `Compression/HSBound.lean`, `Compression/Krylov.lean`) produces
  symmetric matrix `A` and a unit vector `e` whose moments `⟨e, Aʲ e⟩` are the graphon moments for
  every `j ≤ 2m`, with `Tr(A²) ≤ ∫∫K² ≤ 1`.

Since `coeff alt μ (2m) a b` only involves `μ_g` for `g < 2m`, and vanishes unless `a + b < 2m`,
the two expressions are equal, and `matrix_main_general` bounds the matrix one by `1`.

`Ω` is an arbitrary probability space: there is no reduction to step graphons and no passage to a
limit.  The file ends with the same inequality written as integrals over `Ω^{2m}`, using the two
identities of `Fubini.lean`.
-/

open MeasureTheory OddCycleBound Finset

set_option linter.unusedSectionVars false

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ}

/-- **The theorem.**  `eq:main-strengthened` of `alternating_cycles_schur_proof.tex`, for an
arbitrary graphon on an arbitrary probability space:

```
  4^m · Alt_{2m}(W) + t(C_{2m}, 2W − 1) ≤ 1        (m odd).
```

`IsGraphon`, `altDensity` and `signedCycleDensity` are all defined in `Defs.lean`. -/
theorem alt_add_cycle_le_one (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) :
    4 ^ m * altDensity W μ m + signedCycleDensity (sgn W) μ (2 * m) ≤ 1 := by
  classical
  obtain ⟨N, A, e, hAsymm, hunit, htrace, hmom⟩ := exists_matrix_model hW m
  -- the two moment families agree below the cutoff
  have hagree : ∀ g, g < 2 * m → kMoment hW g = matMoment A e g := fun g hg =>
    (hmom g (le_of_lt hg)).symm
  -- hence the two universal expressions agree term by term
  have hterm : ∀ a ∈ range (2 * m + 1), ∀ b ∈ range (2 * m + 1),
      RankOne.coeff RankOne.alt (kMoment hW) (2 * m) a b * kMoment hW (a + b)
        = RankOne.coeff RankOne.alt (matMoment A e) (2 * m) a b * matMoment A e (a + b) := by
    intro a _ b _
    by_cases hab : a + b < 2 * m
    · rw [RankOne.coeff_congr RankOne.alt (2 * m) hagree a b, hagree (a + b) hab]
    · rw [RankOne.coeff_eq_zero_of_le_add RankOne.alt (kMoment hW) (2 * m) a b (by omega),
        RankOne.coeff_eq_zero_of_le_add RankOne.alt (matMoment A e) (2 * m) a b (by omega),
        zero_mul, zero_mul]
  rw [alt_add_cycle_eq_necklace hW hm]
  calc ∑ a ∈ range (2 * m + 1), ∑ b ∈ range (2 * m + 1),
        RankOne.coeff RankOne.alt (kMoment hW) (2 * m) a b * kMoment hW (a + b)
      = ∑ a ∈ range (2 * m + 1), ∑ b ∈ range (2 * m + 1),
          RankOne.coeff RankOne.alt (matMoment A e) (2 * m) a b * matMoment A e (a + b) :=
        Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hterm a ha b hb
    _ ≤ 1 := necklace_le_one hAsymm hunit htrace hm

/-- **The alternating cycle is semi-inducible with density `4^{-m}`.**  Since `t(C_{2m}, 2W−1)` is
nonnegative, the strengthened inequality gives

```
  Alt_{2m}(W) ≤ 4^{-m}        (m odd),
```

attained at the constant graphon `W ≡ 1/2` by `Sharp.half_alt`. -/
theorem altDensity_le (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) :
    altDensity W μ m ≤ 1 / 4 ^ m := by
  obtain ⟨t, rfl⟩ := hm
  have hmain := alt_add_cycle_le_one hW ⟨t, rfl⟩
  have hpos : 0 ≤ signedCycleDensity (sgn W) μ (2 * (2 * t + 1)) :=
    signedCycleDensity_nonneg (goodK_sgn hW) (sgn_symm hW) (2 * t)
  have hpow : (0 : ℝ) < 4 ^ (2 * t + 1) := by positivity
  rw [le_div_iff₀ hpow, mul_comm]
  linarith

/-- **The theorem, in the integral form of `alternating_cycles_schur_proof.tex`.**

For an arbitrary graphon `W` on an arbitrary probability space and every odd `m = 2s+1`, with all
indices read cyclically in `Fin (2m)`:

```
  4^m · ∫_{Ω^{2m}} ∏_{i<2m} (W or 1−W)(xᵢ, x_{i+1})
    + ∫_{Ω^{2m}} ∏_{i<2m} (2W−1)(xᵢ, x_{i+1})  ≤  1,
```

where the first integrand alternates `W` on even `i` and `1 − W` on odd `i`, i.e. it is
`∏_{k<m} W(x_{2k}, x_{2k+1}) · (1 − W(x_{2k+1}, x_{2k+2}))`. -/
theorem alt_add_cycle_le_one_integral (hW : IsGraphon W μ) (s : ℕ) :
    4 ^ (2 * s + 1) *
        (∫ v : Fin (2 * (2 * s) + 2) → Ω,
            ∏ i, altKernels W (2 * s) i (v i) (v (i + 1)) ∂(Measure.pi fun _ => μ))
      + (∫ v : Fin (2 * (2 * s) + 2) → Ω,
            ∏ i, sgn W (v i) (v (i + 1)) ∂(Measure.pi fun _ => μ)) ≤ 1 := by
  have h := alt_add_cycle_le_one hW (⟨s, rfl⟩ : Odd (2 * s + 1))
  have hlen : 2 * (2 * s + 1) = 2 * (2 * s) + 1 + 1 := by ring
  rw [altDensity_eq_integral hW (2 * s), hlen,
    signedCycleDensity_eq_integral (goodK_sgn hW) (2 * (2 * s) + 1)] at h
  exact h

end AlternatingCycle
