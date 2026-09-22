# Semi-inducibility of alternating cycles

This Lean 4 development verifies a universal alternating-cycle inequality and its fixed-density
refinement. For every graphon `W` and every odd `m`,

```text
4^m Alt_{2m}(W) + t(C_{2m}, 2W - 1) <= 1,
```

and consequently `Alt_{2m}(W) <= 4^{-m}`. The constant graphon `W = 1/2` attains equality.

Now let `p` be the edge density of `W`, let `m >= 3`, and assume

```text
(5 - sqrt 5) / 10 <= p <= (5 + sqrt 5) / 10.
```

Then

```text
Alt_{2m}(W) + t(C_{2m}, W - p) <= (p(1-p))^m,
```

and hence, by nonnegativity of the centered even-cycle density,

```text
Alt_{2m}(W) <= (p(1-p))^m.
```

This fixed-density inequality is stronger than the universal profile bound except at `p = 1/2`.
The development proves the universal and fixed-density statements in cyclic-integral form and
verifies equality at the corresponding constant graphons. It does not formalize uniqueness of
either equality case.

The corresponding mathematical proof is
[`alternating_cycles_density_semi_inducibility.pdf`](alternating_cycles_density_semi_inducibility.pdf).

## Disclaimer

After communicating with the author, I was informed that the paper [Generalized Turán problem for directed cycles](https://arxiv.org/pdf/2505.22189) proves the same result (in stronger form), where one can view alternating 4k+2 cycle as directed 2k+1 cycle.
This result is stronger as we have stability result and partial edge profile result, wherea the Grzesik et al.'s result is stronger as it proves for more general cases. 

## Main declarations

All declarations below are in the `AlternatingCycle` namespace.

| Declaration | Content |
|---|---|
| `alt_add_cycle_le_one` | The universal inequality including the signed even-cycle term |
| `altDensity_le` | The universal bound `Alt_{2m}(W) <= 4^{-m}` |
| `alt_add_cycle_le_one_integral` | The same universal inequality as cyclic integrals |
| `half_sharp`, `half_alt` | Equality at the constant graphon `W = 1/2` |
| `fixedDensity_alt_add_centeredCycle_le` | The fixed-density inequality including the centered even-cycle term |
| `fixedDensity_alt_le` | The fixed-density profile upper bound |
| `fixedDensity_alt_add_centeredCycle_le_integral` | The same fixed-density inequality written as cyclic integrals |
| `fixedDensity_alt_le_integral` | The profile bound written as a cyclic integral |
| `constant_fixedDensity_sharp` | Equality in the fixed-density inequality for `W = p` |
| `density_cubic_head_le_one` | The cubic constraint from nonnegative red/blue triple products |
| `exists_fixedDensity_spectrum_cubic` | Finite spectral compression with the required moments and cubic constraint |

The theorems are stated for an arbitrary probability space. `Main.lean` is the entry point for the
universal result and `DensityMain.lean` for the fixed-density refinement. `Defs.lean` contains the
density definitions, and `Parameters.lean` proves the equivalence between the displayed interval
and the scalar condition used by the fixed-density matrix argument.

## Build

The project uses Lean `v4.31.0` and the corresponding pinned mathlib release. From `lean/` run:

```console
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

A successful axiom audit reports only

```text
[propext, Classical.choice, Quot.sound]
```

for each audited theorem. The source contains no `sorry`, `admit`, `native_decide`, or custom
`axiom` declarations.

## Proof organization

```text
lean/AlternatingCycle.lean
lean/AlternatingCycle/
  DensityMain.lean                 public fixed-density theorems
  Defs.lean                        graphon and density definitions
  Parameters.lean                  density-interval parameter identities
  Fubini.lean                      trace densities as cyclic integrals
  Positivity.lean                  nonnegativity of signed even-cycle densities
  Compression/
    DensityL2.lean                 normalized centered operator
    DensityHSBound.lean            Hilbert--Schmidt bound
    DensityKrylov.lean             finite moment-preserving compression
    DensityCubic.lean              cubic head constraint
  Necklace/                        universal moment expansion
  Matrix/
    DensityModel.lean              density-parameterized rank-two model
    DensityBeta.lean               determinant-series coefficients
    DensityCoefficients.lean       monotonicity and diagonal matrix inequality
    Scalar/                        polynomial and odd-coefficient lemmas
    Series/                        resolvent and two-dimensional Schur-complement identities
  Foundation/                      measurable kernel algebra and L2 operators
```

The proof compresses the normalized centered kernel to a finite spectrum while preserving the
moments needed by the period-two word. Pointwise nonnegativity of the normalized red and blue
kernels supplies the cubic initial constraint. The finite-dimensional Schur-complement calculation produces
a nonincreasing coefficient sequence, and the odd-coefficient lemma yields the final bound.

## Audit reading order

For the public statement and its translation to integrals, read:

1. `AlternatingCycle/DensityMain.lean`
2. `AlternatingCycle/Defs.lean`
3. `AlternatingCycle/Parameters.lean`
4. `AlternatingCycle/Fubini.lean`
5. `AlternatingCycle/Foundation/Graphon.lean`
6. `AlternatingCycle/Foundation/Kernel.lean`

For the proof, continue with `Compression/DensityCubic.lean`,
`Compression/DensityKrylov.lean`, `Necklace/`, and `Matrix/DensityCoefficients.lean`.
