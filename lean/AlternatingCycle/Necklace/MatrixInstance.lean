import AlternatingCycle.Necklace.Trace
import AlternatingCycle.Matrix.Conjugation

/-!
# Fact A for matrices

With `𝒜 = Matrix (Fin n) (Fin n) ℝ`, `τ = trace`,
`j = P = e ⊗ e` and `k = A`, the three hypotheses of `Necklace/Trace.lean` are

```
  P * A ^ b * P = ⟨e, Aᵇ e⟩ • P        (`vecMulVec_pow_vecMulVec`)
  trace (M * N) = trace (N * M)        (`Matrix.trace_mul_comm`)
  trace (P * A ^ g) = ⟨e, Aᵍ e⟩        (`trace_vecMulVec_mul_pow`)
```

none of which needs `A` symmetric, `e` a unit vector, or any bound on the trace.  So

```
  Tr(((P + A)(P − A))^m) + Tr(A^{2m}) = ∑_{a,b} c_{2m}(a,b) · ⟨e, A^{a+b} e⟩        (m odd)
```

holds unconditionally, and `matrix_main_general` bounds the right-hand side by `1` under the
hypotheses of `thm:matrix`.  The right-hand side is the same expression the kernel instantiation
produces, which is what lets the two be compared.

The `m = 1` coefficients are computed at the end of the file.
-/

namespace AlternatingCycle

open Matrix Finset RankOne

variable {n : ℕ}

noncomputable section

/-- The vector moments `μ_g = ⟨e, A^g e⟩`. -/
def matMoment (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) (g : ℕ) : ℝ := e ⬝ᵥ (A ^ g *ᵥ e)

@[simp] lemma matMoment_zero (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) :
    matMoment A e 0 = e ⬝ᵥ e := by simp [matMoment]

lemma vecMulVec_smul_right (c : ℝ) (u v : Fin n → ℝ) :
    Matrix.vecMulVec u (c • v) = c • Matrix.vecMulVec u v := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.smul_apply]
  ring

/-- `P` is rank one: `P M P = ⟨e, M e⟩ • P`, here only at `M = A ^ b`. -/
lemma vecMulVec_pow_vecMulVec (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) (b : ℕ) :
    Matrix.vecMulVec e e * A ^ b * Matrix.vecMulVec e e
      = matMoment A e b • Matrix.vecMulVec e e := by
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, vecMulVec_smul_right, matMoment,
    Matrix.dotProduct_mulVec]

/-- The trace against `P` reads off a moment. -/
lemma trace_vecMulVec_mul_pow (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) (g : ℕ) :
    Matrix.trace (Matrix.vecMulVec e e * A ^ g) = matMoment A e g := by
  rw [Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, matMoment, Matrix.dotProduct_mulVec,
    dotProduct_comm]

/-- **Fact A for matrices.**  Unconditional: no symmetry, no normalisation, no trace bound. -/
theorem trace_alt_matrix (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) (m : ℕ) :
    Matrix.trace (((Matrix.vecMulVec e e + A) * (Matrix.vecMulVec e e - A)) ^ m)
      = (-1) ^ m * Matrix.trace (A ^ (2 * m))
        + ∑ a ∈ range (2 * m + 1), ∑ b ∈ range (2 * m + 1),
            coeff alt (matMoment A e) (2 * m) a b * matMoment A e (a + b) :=
  tau_alt (matMoment A e) (Matrix.vecMulVec e e) A (Matrix.traceLinearMap (Fin n) ℝ ℝ)
    (vecMulVec_pow_vecMulVec A e) (fun M N => Matrix.trace_mul_comm M N)
    (trace_vecMulVec_mul_pow A e) m

/-- The odd-`m` form: both traces on the same side. -/
theorem trace_alt_matrix_add (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) {m : ℕ} (hm : Odd m) :
    Matrix.trace (((Matrix.vecMulVec e e + A) * (Matrix.vecMulVec e e - A)) ^ m)
        + Matrix.trace (A ^ (2 * m))
      = ∑ a ∈ range (2 * m + 1), ∑ b ∈ range (2 * m + 1),
          coeff alt (matMoment A e) (2 * m) a b * matMoment A e (a + b) :=
  tau_alt_add (matMoment A e) (Matrix.vecMulVec e e) A (Matrix.traceLinearMap (Fin n) ℝ ℝ)
    (vecMulVec_pow_vecMulVec A e) (fun M N => Matrix.trace_mul_comm M N)
    (trace_vecMulVec_mul_pow A e) hm

/-- **`thm:matrix`, in moment form.**  Under the hypotheses of `matrix_main_general` the universal
expression `N_m` is at most `1`.  Since `N_m` depends on `(A, e)` only through the moments, this is
the inequality the graphon layer will transport. -/
theorem necklace_le_one {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : Aᵀ = A) {e : Fin n → ℝ}
    (he : e ⬝ᵥ e = 1) (htau : Matrix.trace (A * A) ≤ 1) {m : ℕ} (hm : Odd m) :
    ∑ a ∈ range (2 * m + 1), ∑ b ∈ range (2 * m + 1),
        coeff alt (matMoment A e) (2 * m) a b * matMoment A e (a + b) ≤ 1 := by
  rw [← trace_alt_matrix_add A e hm]
  exact matrix_main_general hsymm he htau hm

end

section Regression

/-! ### The coefficients at `m = 1`

`α₂ = −1`, `c₂(0,0) = μ₀`, `c₂(1,0) = 1`, `c₂(0,1) = −1`, whence `4·Alt₂(W) + t(C₂, K) = μ₀²`,
which is `1` exactly when `e` is a unit vector. -/

variable (μ : ℕ → ℝ)

example : alphaC alt 2 = -1 := by norm_num [alphaC, alt]

example : coeff alt μ 2 0 0 = μ 0 := by norm_num [coeff, alphaC, alt, Finset.sum_range_succ]

example : coeff alt μ 2 1 0 = 1 := by norm_num [coeff, alphaC, alt, Finset.sum_range_succ]

example : coeff alt μ 2 0 1 = -1 := by norm_num [coeff, alphaC, alt, Finset.sum_range_succ]

/-- The plan's sanity check: at `m = 1` the universal expression is `μ₀²`, hence `1`. -/
example (h0 : μ 0 = 1) :
    ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, coeff alt μ 2 a b * μ (a + b) = 1 := by
  norm_num [coeff, alphaC, alt, Finset.sum_range_succ, h0]

end Regression

end AlternatingCycle
