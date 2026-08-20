# Semi-inducibility of alternating (4k+2)-cycles

For every graphon `W` on every probability space `(Ω, μ)` and every odd `m` — equivalently, for
every cycle of length `2m = 4k+2` —

```
  4^m · Alt_{2m}(W) + t(C_{2m}, 2W − 1)  ≤  1,
```

and since the cycle density of a symmetric kernel at even length is nonnegative,

```
  Alt_{2m}(W)  ≤  4^{-m},
```

both attained at the constant graphon `W ≡ 1/2`, where `t(C_{2m}, 2W − 1) = 0` and
`Alt_{2m}(W) = 4^{-m}`.  So the alternating `(4k+2)`-cycle is semi-inducible with density `4^{-m}`,
and the random-like graphon is extremal.  The note is `alternating_cycles_schur_proof.pdf`; the
Lean development is in `lean/`.

The results, all in `AlternatingCycle`:

| | |
|---|---|
| `alt_add_cycle_le_one` | the strengthened inequality, in the trace convention the proof runs in |
| `altDensity_le` | `Alt_{2m}(W) ≤ 4^{-m}` |
| `alt_add_cycle_le_one_integral` | the strengthened inequality with both densities as integrals over `Ω^{2m}` against the product measure, the form the note uses |
| `half_alt`, `half_sharp` | `Alt_{2m}(1/2) = 4^{-m}`, and equality in the strengthened inequality |

## Building

Requires Lean `v4.31.0` (via `elan`); the pinned mathlib `v4.31.0` is fetched automatically.  In
`lean/`:

```
lake exe cache get                # download the prebuilt mathlib cache
lake build                        # builds everything; must end "Build completed successfully"
lake env lean CheckAxioms.lean    # axiom audit; see below
```

A clean build produces no warnings.

## Auditing the statement

The claim to check is that the Lean theorem says what the note says.  Four files, in this order —
nothing else needs to be read to establish it.

| Read | For |
|---|---|
| `lean/AlternatingCycle/Main.lean` | the statements: lines 43, 76 and 98 |
| `lean/AlternatingCycle/Defs.lean` | `sgn`, `cmpl`, `altDensity`, `signedCycleDensity` (lines 32–44) |
| `lean/AlternatingCycle/Foundation/Graphon.lean` | `IsGraphon`, line 35 — the hypothesis on `W` |
| `lean/AlternatingCycle/Foundation/Kernel.lean` | `comp` (40), `compPow` (1432), `trace` (1445) |

These are the definitions the theorem is actually stated in; there is no separate summary to trust.
Points worth checking explicitly:

* `IsGraphon W μ` asks only for joint measurability, symmetry and `0 ≤ W ≤ 1`.  `Ω` is an arbitrary
  `MeasurableSpace` with an `IsProbabilityMeasure`; it is never assumed to be `[0,1]`, finite, or
  standard Borel, and `W` is never assumed to be a step function.
* `altDensity W μ m` is `trace (compPow (comp W (cmpl W)) (m−1))` — the `m`-fold composite of
  `W ∘ (1−W)`, traced.  `signedCycleDensity K μ r` is `trace (compPow K (r−1))`.
* For the integral form, the two integrands are `altKernels` (`Fubini.lean`, line 281: `W` at even
  positions, `1 − W` at odd ones) and `sgn W`, both under `cycleProd` (line 166), the product
  `∏ᵢ Mᵢ (vᵢ, v_{i+1})` with indices cyclic in `Fin (2m)`.  The two forms are connected by
  `altDensity_eq_integral` and `signedCycleDensity_eq_integral`.
* `Sharp.lean`, lines 73 and 84: `half_alt` and `half_sharp` give `Alt_{2m}(1/2) = 4^{-m}` and
  equality in the strengthened inequality, so neither bound can be improved.

## Auditing the proof

`lake env lean CheckAxioms.lean` prints, for each named result, the axioms it depends on.  Every
line must read

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three are the standard classical axioms of mathlib.  Anything else — in particular
`sorryAx` — means something is unproved.  Equivalently: `grep -rn "sorry\|native_decide" lean/`
returns nothing, and `grep -rn "^axiom" lean/` returns nothing.

The development is laid out as follows.

```
lean/AlternatingCycle.lean         index and architecture
lean/AlternatingCycle/
  Defs.lean        the definitions the statement uses
  Main.lean        the theorem, in both forms
  Sharp.lean       equality at the constant graphon
  Fubini.lean      traces = integrals over Ω^r
  Positivity.lean  t(C_{2m}, K) = ∫∫ (K^{∘m})² ≥ 0 for symmetric K
  Necklace/        both densities as one universal expression in the moments ⟨1, X^j 1⟩
  Compression/     a finite symmetric matrix carrying those moments, with Tr(A²) ≤ 1
  Matrix/          the finite-dimensional theorem the compression is fed into
  Foundation/      kernel algebra and the L² operator of a kernel
```
