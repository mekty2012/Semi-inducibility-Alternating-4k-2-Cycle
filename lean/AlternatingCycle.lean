-- The definitions in the statement, the theorem, and its sharpness at the constant graphon.
import AlternatingCycle.Defs
import AlternatingCycle.Main
import AlternatingCycle.Fubini
import AlternatingCycle.Positivity
import AlternatingCycle.Sharp
-- Fact A: the rank-one normal form and its two instantiations.
import AlternatingCycle.Necklace.RankOne
import AlternatingCycle.Necklace.Trace
import AlternatingCycle.Necklace.MatrixInstance
import AlternatingCycle.Necklace.Unitize
import AlternatingCycle.Necklace.KernelInstance
-- Fact B: the L² operator, the Hilbert–Schmidt bound, and the matrix model.
import AlternatingCycle.Compression.L2
import AlternatingCycle.Compression.HSBound
import AlternatingCycle.Compression.Krylov
-- The finite-dimensional engine.
import AlternatingCycle.Matrix.Scalar.Cn
import AlternatingCycle.Matrix.Scalar.LogDeriv
import AlternatingCycle.Matrix.Scalar.OddLog
import AlternatingCycle.Matrix.Series.Resolvent
import AlternatingCycle.Matrix.Series.Schur
import AlternatingCycle.Matrix.Series.Jacobi2
import AlternatingCycle.Matrix.Model
import AlternatingCycle.Matrix.Spectral
import AlternatingCycle.Matrix.Beta
import AlternatingCycle.Matrix.MatrixMain
import AlternatingCycle.Matrix.Conjugation

/-!
# The alternating-cycle theorem

The deliverable is `AlternatingCycle.alt_add_cycle_le_one` in `Main.lean`: for **every** graphon
`W` on **every** probability space `(Ω, μ)` and every odd `m` — equivalently, for every cycle of
length `2m = 4k+2` —

```
  4^m · Alt_{2m}(W) + t(C_{2m}, 2W − 1) ≤ 1,
```

and since `Positivity.lean` shows the second term is nonnegative, `altDensity_le`:

```
  Alt_{2m}(W) ≤ 4^{-m}.
```

`Sharp.lean` attains both at the constant graphon `W ≡ 1/2`, so neither is improvable.

`Ω` is an arbitrary probability space: there is no reduction to step graphons and no passage to a
limit anywhere in the development.  `README.md` says how to build and how to audit.

## Reading the statement

Everything the theorem mentions is defined in `Defs.lean` — `sgn`, `cmpl`, `altDensity`,
`signedCycleDensity` — on top of four notions taken from `Foundation/`: `IsGraphon`, `comp`, `compPow`
and `trace`, whose definitions `Defs.lean` also spells out.  **An audit of the statement is two
files: `Defs.lean`, then `Main.lean`.**

`altDensity` and `signedCycleDensity` are defined as traces of kernel powers, which is the form
the proof runs in.  `Fubini.lean` proves they are the integrals of the source note —
`altDensity_eq_integral` and `signedCycleDensity_eq_integral` — and `Main.lean` ends with
`alt_add_cycle_le_one_integral`, the theorem written entirely as integrals over `Ω^{2m}` against
the product measure, with no trace anywhere in the statement.

## Reading the proof

The proof has two halves, which meet in `Main.lean`.

**Fact A — moment determinacy** (`Necklace/`).  `RankOne.lean` proves a normal form for signed
words `∏ (j + εᵢ k)` in any unital `ℝ`-algebra with a rank-one element `j`, and `Trace.lean` takes
its trace.  The result is a universal expression `∑ coeff alt μ (2m) a b · μ_{a+b}` in the moments
alone.  It is instantiated twice — at matrices (`MatrixInstance.lean`) and at kernels
(`Unitize.lean`, `KernelInstance.lean`) — and the two instantiations produce the *same* numbers,
which is what removes the need for an approximation argument.

**Fact B — the matrix model** (`Compression/`).  `L2.lean` realises `2W − 1` as a symmetric
operator `X` on `L²(μ)`, `HSBound.lean` bounds `∑ ‖X vᵢ‖²` by `∫∫(2W−1)² ≤ 1` for any finite
orthonormal family, and `Krylov.lean` compresses `X` to `span{1, X1, …, X^{2m}1}` and diagonalises,
producing a symmetric matrix and a unit vector carrying the graphon's moments
(`AlternatingCycle.exists_matrix_model`).

**The engine** (`Matrix/`).  Applying Fact B needs the finite-dimensional theorem
`matrix_main_general` (`Matrix/Conjugation.lean`), proved in `Matrix/MatrixMain.lean` from the
Schur-complement identity of `Matrix/Series/` and the scalar estimates of `Matrix/Scalar/`, via
`Matrix/Model.lean`, `Matrix/Spectral.lean` and `Matrix/Beta.lean`.  These files are machinery for
the graphon theorem; none of them mentions a graphon.

**`Positivity.lean`** proves `t(C_{2m}, K) = ∫∫ (K^{∘m})² ≥ 0` for symmetric `K`, which is what
turns the strengthened inequality into `Alt_{2m}(W) ≤ 4^{-m}`.

**`Foundation/`** holds the kernel algebra — `GoodK`, `comp`, `compPow`, `trace`, `IsGraphon` and their
calculus — and the `L²` operator of a graphon kernel.
-/
