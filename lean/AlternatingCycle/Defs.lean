import AlternatingCycle.Foundation.Kernel
import AlternatingCycle.Parameters

/-!
# The definitions in the statement of the theorem

The graphon statements use `IsGraphon`, `altDensity`, `signedCycleDensity`, and the centered,
complementary, and signed kernels defined below.  `IsGraphon` is in `Foundation/Graphon.lean`, and
the kernel operations `comp`, `compPow`, and `trace` are in `Foundation/Kernel.lean`.

`IsGraphon W μ` is a graphon over a probability space `(Ω, μ)`: a symmetric, jointly measurable,
`[0,1]`-valued kernel.  `Ω` is an arbitrary measurable space throughout; nothing here or later
assumes `Ω = [0,1]`, that `Ω` is finite, or that `W` is a step function.

`altDensity W μ m` is `Alt_{2m}(W)` and `signedCycleDensity K μ r` is `t(C_r, K)`, in the form the
proof uses: traces of kernel powers.  `Fubini.lean` proves they are the integrals

```
  Alt_{2m}(W) = ∫_{Ω^{2m}} ∏_{k<m} W(x_{2k}, x_{2k+1}) · (1 − W(x_{2k+1}, x_{2k+2}))
  t(C_r, K)   = ∫_{Ω^r}    ∏_{i<r} K(x_i, x_{i+1})
```

with cyclic indices.  `Main.lean` and `DensityMain.lean` provide the corresponding integral
theorems.
-/

open MeasureTheory OddCycleBound

namespace AlternatingCycle

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The signed kernel `K = 2W − 1`, symmetric with `|K| ≤ 1`. -/
def sgn (W : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 2 * W x y - 1

/-- The complementary graphon `U = 1 − W`. -/
def cmpl (W : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 1 - W x y

/-- The kernel centered at the prescribed edge density. -/
def centered (W : Ω → Ω → ℝ) (p : ℝ) : Ω → Ω → ℝ := fun x y => W x y - p

/-- The centered kernel normalized by a positive scale. -/
noncomputable def normalizedCentered (W : Ω → Ω → ℝ) (p s : ℝ) : Ω → Ω → ℝ :=
  fun x y => (W x y - p) / s

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

lemma goodK_centered (hW : IsGraphon W μ) (p : ℝ) : GoodK (centered W p) := by
  refine ⟨hW.meas.sub measurable_const, 1 + |p|, by positivity, fun x y => ?_⟩
  have habs : |W x y| ≤ 1 := by
    rw [abs_of_nonneg (hW.nonneg x y)]
    exact hW.le_one x y
  show |W x y - p| ≤ 1 + |p|
  calc
    |W x y - p| ≤ |W x y| + |p| := abs_sub _ _
    _ ≤ 1 + |p| := by linarith

lemma goodK_normalizedCentered (hW : IsGraphon W μ) (p s : ℝ) :
    GoodK (normalizedCentered W p s) := by
  obtain ⟨C, hC0, hC⟩ := (goodK_centered hW p).bdd
  refine ⟨?_, |s⁻¹| * C, mul_nonneg (abs_nonneg _) hC0, fun x y => ?_⟩
  · change Measurable (fun z : Ω × Ω => (W z.1 z.2 - p) * s⁻¹)
    exact (goodK_centered hW p).meas.mul measurable_const
  rw [normalizedCentered, div_eq_mul_inv, mul_comm, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x y) (abs_nonneg _)

lemma centered_symm (hW : IsGraphon W μ) (p : ℝ) (x y : Ω) :
    centered W p x y = centered W p y x := by
  simp only [centered]
  rw [hW.symm x y]

lemma normalizedCentered_symm (hW : IsGraphon W μ) (p s : ℝ) (x y : Ω) :
    normalizedCentered W p s x y = normalizedCentered W p s y x := by
  simp only [normalizedCentered]
  rw [hW.symm x y]

lemma edgeDensity_eq_doubleMean (W : Ω → Ω → ℝ) (μ : Measure Ω) :
    edgeDensity W μ = doubleMean μ W := rfl

omit [MeasurableSpace Ω] in
lemma centered_eq_s_mul_normalizedCentered (W : Ω → Ω → ℝ) (p : ℝ) {s : ℝ}
    (hs : s ≠ 0) :
    centered W p = fun x y => s * normalizedCentered W p s x y := by
  funext x y
  simp only [centered, normalizedCentered]
  field_simp

lemma altDensity_def (W : Ω → Ω → ℝ) (μ : Measure Ω) (m : ℕ) :
    altDensity W μ m = trace μ (compPow μ (comp μ W (cmpl W)) (m - 1)) := rfl

lemma signedCycleDensity_def (K : Ω → Ω → ℝ) (μ : Measure Ω) (r : ℕ) :
    signedCycleDensity K μ r = trace μ (compPow μ K (r - 1)) := rfl

end AlternatingCycle
