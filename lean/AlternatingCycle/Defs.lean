import AlternatingCycle.Foundation.Kernel

/-!
# The definitions in the statement of the theorem

`Main.lean` states the theorem in terms of `IsGraphon`, `altDensity`, `signedCycleDensity` and
`sgn`.  The last three are defined below; `IsGraphon` is in `Foundation/Graphon.lean`, and the kernel
operations they are built from — `comp`, `compPow`, `trace` — are in `Foundation/Kernel.lean`.

`IsGraphon W μ` is a graphon over a probability space `(Ω, μ)`: a symmetric, jointly measurable,
`[0,1]`-valued kernel.  `Ω` is an arbitrary measurable space throughout; nothing here or later
assumes `Ω = [0,1]`, that `Ω` is finite, or that `W` is a step function.

`altDensity W μ m` is `Alt_{2m}(W)` and `signedCycleDensity K μ r` is `t(C_r, K)`, in the form the
proof uses: traces of kernel powers.  `Fubini.lean` proves they are the integrals

```
  Alt_{2m}(W) = ∫_{Ω^{2m}} ∏_{k<m} W(x_{2k}, x_{2k+1}) · (1 − W(x_{2k+1}, x_{2k+2}))
  t(C_r, K)   = ∫_{Ω^r}    ∏_{i<r} K(x_i, x_{i+1})
```

with cyclic indices, and `Main.lean` closes with the theorem written in that form.
-/

open MeasureTheory OddCycleBound

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The signed kernel `K = 2W − 1`, symmetric with `|K| ≤ 1`. -/
def sgn (W : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 2 * W x y - 1

/-- The complementary graphon `U = 1 − W`. -/
def cmpl (W : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 1 - W x y

/-- `Alt_{2m}(W)`: the alternating-cycle density, the probability that a uniformly random cyclic
`2m`-tuple alternates between `W`-edges and `U`-edges. -/
noncomputable def altDensity (W : Ω → Ω → ℝ) (μ : Measure Ω) (m : ℕ) : ℝ :=
  trace μ (compPow μ (comp μ W (cmpl W)) (m - 1))

/-- `t(C_r, K)`: the cycle density of a kernel. -/
noncomputable def signedCycleDensity (K : Ω → Ω → ℝ) (μ : Measure Ω) (r : ℕ) : ℝ :=
  trace μ (compPow μ K (r - 1))

/-! ### The two kernels are bounded and measurable

These are the only facts about `sgn` and `cmpl` the rest of the development needs from this file.
-/

variable {μ : Measure Ω} {W : Ω → Ω → ℝ}

lemma goodK_sgn (hW : IsGraphon W μ) : GoodK (sgn W) := by
  refine ⟨(measurable_const.mul hW.meas).sub measurable_const, 1, zero_le_one, fun x y => ?_⟩
  have h0 := hW.nonneg x y
  have h1 := hW.le_one x y
  show |2 * W x y - 1| ≤ 1
  rw [abs_le]
  constructor <;> linarith

lemma goodK_cmpl (hW : IsGraphon W μ) : GoodK (cmpl W) := by
  refine ⟨measurable_const.sub hW.meas, 1, zero_le_one, fun x y => ?_⟩
  have h0 := hW.nonneg x y
  have h1 := hW.le_one x y
  show |1 - W x y| ≤ 1
  rw [abs_le]
  constructor <;> linarith

lemma altDensity_def (W : Ω → Ω → ℝ) (μ : Measure Ω) (m : ℕ) :
    altDensity W μ m = trace μ (compPow μ (comp μ W (cmpl W)) (m - 1)) := rfl

lemma signedCycleDensity_def (K : Ω → Ω → ℝ) (μ : Measure Ω) (r : ℕ) :
    signedCycleDensity K μ r = trace μ (compPow μ K (r - 1)) := rfl

end AlternatingCycle
