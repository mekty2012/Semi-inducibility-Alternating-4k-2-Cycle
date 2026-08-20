import AlternatingCycle.Matrix.MatrixMain
import Mathlib.Analysis.Matrix.Spectrum

/-!
# `thm:matrix` for an arbitrary symmetric matrix

`MatrixMain.lean` proves the abstract trace inequality in a diagonalizing basis.  Everything in
`thm:matrix` — the two traces and the unit vector — is invariant under orthogonal conjugation, so
the general case follows by one application of the spectral theorem.  This is the only place in the
development where the spectral theorem is used.
-/

namespace AlternatingCycle

open Matrix

variable {n : ℕ}

/-- On real matrices the star operation is transposition. -/
lemma star_eq_transpose (M : Matrix (Fin n) (Fin n) ℝ) : star M = Mᵀ := by
  ext i j
  simp [Matrix.star_apply, Matrix.transpose_apply]

lemma conj_pow {Q R L : Matrix (Fin n) (Fin n) ℝ} (h1 : Q * R = 1) (h2 : R * Q = 1) :
    ∀ m : ℕ, (Q * L * R) ^ m = Q * L ^ m * R
  | 0 => by simp [h1]
  | m + 1 => by
      rw [pow_succ, conj_pow h1 h2 m, pow_succ]
      calc Q * L ^ m * R * (Q * L * R) = Q * L ^ m * (R * Q) * L * R := by
            simp only [Matrix.mul_assoc]
        _ = Q * (L ^ m * L) * R := by rw [h2]; simp only [Matrix.mul_assoc, Matrix.mul_one]

lemma trace_conj {Q R L : Matrix (Fin n) (Fin n) ℝ} (h : R * Q = 1) :
    Matrix.trace (Q * L * R) = Matrix.trace L := by
  rw [Matrix.trace_mul_comm (Q * L) R, ← Matrix.mul_assoc, h, Matrix.one_mul]

lemma dot_mulVec_self {M : Matrix (Fin n) (Fin n) ℝ} (h : Mᵀ * M = 1) (v : Fin n → ℝ) :
    (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

lemma vecMulVec_conj {Q R : Matrix (Fin n) (Fin n) ℝ} (hQR : Qᵀ = R) (e : Fin n → ℝ) :
    Q * Matrix.vecMulVec e e * R = Matrix.vecMulVec (Q *ᵥ e) (Q *ᵥ e) := by
  refine Matrix.ext fun i j => ?_
  have hright : ∑ k, e k * R k j = (Q *ᵥ e) j := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => by rw [← hQR, Matrix.transpose_apply]; ring
  rw [Matrix.mul_apply, Matrix.vecMulVec_apply, ← hright, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by rw [Matrix.vecMulVec_apply]; ring

/-- **`thm:matrix`.**  For a symmetric `A` with `Tr(A²) ≤ 1`, a unit vector `e`,
`P = e ⊗ e` and odd `m`, `Tr(((P+A)(P−A))^m) + Tr(A^{2m}) ≤ 1`. -/
theorem matrix_main_general {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : Aᵀ = A)
    {e : Fin n → ℝ} (he : e ⬝ᵥ e = 1) (htau : Matrix.trace (A * A) ≤ 1)
    {m : ℕ} (hm : Odd m) :
    Matrix.trace (((Matrix.vecMulVec e e + A) * (Matrix.vecMulVec e e - A)) ^ m)
      + Matrix.trace (A ^ (2 * m)) ≤ 1 := by
  classical
  have hA : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hsymm]
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  set Q : Matrix (Fin n) (Fin n) ℝ := star U with hQ
  have hQU : Q * U = 1 := Unitary.coe_star_mul_self _
  have hUQ : U * Q = 1 := Unitary.coe_mul_star_self _
  have hQt : Qᵀ = U := by rw [hQ, star_eq_transpose, Matrix.transpose_transpose]
  have hdiag : Q * A * U = Matrix.diagonal hA.eigenvalues := by
    have := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    simpa [hQ, hU] using this
  -- the spectral data
  set lam : Fin n → ℝ := hA.eigenvalues with hlam
  set e' : Fin n → ℝ := Q *ᵥ e with he'
  have hQtQ : Qᵀ * Q = 1 := by rw [hQt]; exact hUQ
  have he'unit : ∑ i, e' i ^ 2 = 1 := by
    have h1 : e' ⬝ᵥ e' = 1 := by rw [he', dot_mulVec_self hQtQ e, he]
    rw [← h1, dotProduct]
    exact Finset.sum_congr rfl fun i _ => pow_two (e' i)
  have htaule : ∑ i, lam i ^ 2 ≤ 1 := by
    have hd : Matrix.trace (Matrix.diagonal lam * Matrix.diagonal lam) = ∑ i, lam i ^ 2 := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      exact Finset.sum_congr rfl fun i _ => (pow_two (lam i)).symm
    rw [← hd, ← hdiag]
    have : Q * A * U * (Q * A * U) = Q * (A * A) * U := by
      calc Q * A * U * (Q * A * U) = Q * A * (U * Q) * A * U := by simp only [Matrix.mul_assoc]
        _ = Q * (A * A) * U := by rw [hUQ]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    rw [this, trace_conj hUQ]
    exact htau
  set T : Spectrum n := ⟨lam, e', he'unit, htaule⟩ with hT
  -- transport the two traces
  have hTA : T.model.A = Q * A * U := by rw [model_A, hT, hdiag]
  have hTe : T.model.e = Q *ᵥ e := rfl
  have hTP : T.model.P = Q * Matrix.vecMulVec e e * U := by
    rw [Model.P, hTe, vecMulVec_conj hQt e]
  have haddc : Q * Matrix.vecMulVec e e * U + Q * A * U
      = Q * (Matrix.vecMulVec e e + A) * U := by
    simp only [Matrix.add_mul, Matrix.mul_add]
  have hsubc : Q * Matrix.vecMulVec e e * U - Q * A * U
      = Q * (Matrix.vecMulVec e e - A) * U := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
  have hTL : T.model.L = Q * ((Matrix.vecMulVec e e + A) * (Matrix.vecMulVec e e - A)) * U := by
    rw [Model.L, hTP, hTA, haddc, hsubc]
    calc Q * (Matrix.vecMulVec e e + A) * U * (Q * (Matrix.vecMulVec e e - A) * U)
        = Q * (Matrix.vecMulVec e e + A) * (U * Q) * (Matrix.vecMulVec e e - A) * U := by
          simp only [Matrix.mul_assoc]
      _ = Q * ((Matrix.vecMulVec e e + A) * (Matrix.vecMulVec e e - A)) * U := by
          rw [hUQ]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  have hmain := matrix_main T hm
  rw [hTL, hTA, conj_pow hQU hUQ, conj_pow hQU hUQ, trace_conj hUQ, trace_conj hUQ] at hmain
  exact hmain

end AlternatingCycle
