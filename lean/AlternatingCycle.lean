-- Definitions, graphon theorems, integral forms, and constant-graphon sharpness.
import AlternatingCycle.Defs
import AlternatingCycle.Main
import AlternatingCycle.Fubini
import AlternatingCycle.Positivity
import AlternatingCycle.Sharp
-- The universal rank-one normal form and its matrix and kernel instances.
import AlternatingCycle.Necklace.RankOne
import AlternatingCycle.Necklace.Trace
import AlternatingCycle.Necklace.MatrixInstance
import AlternatingCycle.Necklace.Unitize
import AlternatingCycle.Necklace.KernelInstance
-- L² operators, Hilbert--Schmidt bounds, Krylov compression, and the cubic constraint.
import AlternatingCycle.Compression.L2
import AlternatingCycle.Compression.DensityL2
import AlternatingCycle.Compression.HSBound
import AlternatingCycle.Compression.DensityHSBound
import AlternatingCycle.Compression.Krylov
import AlternatingCycle.Compression.DensityKrylov
import AlternatingCycle.Compression.DensityCubic
-- The finite-dimensional engine.
import AlternatingCycle.Matrix.Scalar.Cn
import AlternatingCycle.Matrix.Scalar.LogDeriv
import AlternatingCycle.Matrix.Scalar.OddLog
import AlternatingCycle.Matrix.Series.Resolvent
import AlternatingCycle.Matrix.Series.Schur
import AlternatingCycle.Matrix.Series.Jacobi2
import AlternatingCycle.Matrix.Model
import AlternatingCycle.Matrix.DensityModel
import AlternatingCycle.Matrix.Spectral
import AlternatingCycle.Matrix.Beta
import AlternatingCycle.Matrix.DensityBeta
import AlternatingCycle.Matrix.DensityCoefficients
import AlternatingCycle.Matrix.MatrixMain
import AlternatingCycle.Matrix.Conjugation
import AlternatingCycle.DensityMain

/-!
# Alternating-cycle semi-inducibility and its fixed-density refinement

For every graphon `W` and every odd `m`, `Main.lean` proves

```
  4^m · Alt_{2m}(W) + t(C_{2m}, 2W-1) ≤ 1,
```

and hence `Alt_{2m}(W) ≤ 4^{-m}`.  The constant graphon `W ≡ 1/2` attains equality.

Let `W` be a graphon of edge density `p`, where `q = 1-p`, and let `m ≥ 3` be odd.  If

```
  (5 - √5)/10 ≤ p ≤ (5 + √5)/10,
```

then `DensityMain.lean` proves

```
  Alt_{2m}(W) + t(C_{2m}, W-p) ≤ (p*q)^m
```

and consequently `Alt_{2m}(W) ≤ (p*q)^m`.  Both statements are also available as cyclic
integrals, and the constant graphon `W ≡ p` attains equality.  This refines the universal profile
bound except at `p = 1/2`.  Both theorems are formulated on an
arbitrary probability space `(Ω, μ)`; no step-graphon reduction or limiting argument is used.

## Reading the statement

The fixed-density statements are `fixedDensity_alt_add_centeredCycle_le`, `fixedDensity_alt_le`,
`fixedDensity_alt_add_centeredCycle_le_integral`, and `fixedDensity_alt_le_integral` in
`DensityMain.lean`.
`Defs.lean` defines `centered`, `normalizedCentered`, `altDensity`, and `signedCycleDensity` on top
of `IsGraphon`, `comp`, `compPow`, and `trace` from `Foundation/`.  `Parameters.lean` proves that
the closed interval above is equivalent to the scalar condition used by the matrix argument.

`altDensity` and `signedCycleDensity` are traces of kernel powers.  `Fubini.lean` identifies these
traces with cyclic integrals over `Ω^{2m}`.

## Reading the proof

`Necklace/` expresses the period-two kernel word and its diagonal matrix counterpart as the same
universal polynomial in moments.  `Compression/DensityL2.lean`, `DensityHSBound.lean`, and
`DensityKrylov.lean` compress the normalized centered operator to a finite spectrum while
preserving all required moments and a unit spectral bound.  `DensityCubic.lean` obtains the first
coefficient constraint from the pointwise nonnegative red--blue--red and blue--red--blue kernels.
The density-parameterized Schur-complement model and monotone coefficients in `Matrix/` then bound
the diagonal word by one.  `DensityMain.lean` transfers the bound back to the graphon moments and
uses even-cycle positivity to obtain the profile inequality.

`Foundation/` holds the kernel calculus and the `L²` operator of a graphon kernel.  `README.md`
gives the build and audit commands and states the exact formalization scope.
-/
