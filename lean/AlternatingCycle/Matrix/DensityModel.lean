import AlternatingCycle.Matrix.Model
import AlternatingCycle.Matrix.Spectral

/-!
# The fixed-density rank-two model

For a symmetric matrix `A`, a unit vector `e`, and scalars `a*b=1`, this module factors the
resolvent of `(P+aA)(P-bA)`, where `P=e ⊗ e`, through a two-dimensional Schur complement.
-/

namespace AlternatingCycle

open PowerSeries Matrix Finset

noncomputable section

namespace Model

variable {n : ℕ} (S : Model n)

/-- The period-two matrix product `(P+aA)(P-bA)`. -/
def densityL (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (S.P + a • S.A) * (S.P - b • S.A)

/-- The columns `[e,-aAe]` in the rank-two factorization. -/
def densityU0 (a : ℝ) : Matrix (Fin n) (Fin 2) ℝ :=
  Matrix.of fun i => ![S.e i, -(a * S.u i)]

/-- The rows `[bAe-e;e]` in the rank-two factorization. -/
def densityV0 (b : ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun s j => (![b * S.u j - S.e j, S.e j] : Fin 2 → ℝ) s

@[simp] lemma densityU0_zero (a : ℝ) (i : Fin n) : S.densityU0 a i 0 = S.e i := rfl
@[simp] lemma densityU0_one (a : ℝ) (i : Fin n) : S.densityU0 a i 1 = -(a * S.u i) := rfl
@[simp] lemma densityV0_zero (b : ℝ) (j : Fin n) : S.densityV0 b 0 j = b * S.u j - S.e j := rfl
@[simp] lemma densityV0_one (b : ℝ) (j : Fin n) : S.densityV0 b 1 j = S.e j := rfl

lemma densityL_add_Y (a b : ℝ) (hab : a * b = 1) :
    S.densityL a b + S.Y = S.P - b • (S.P * S.A) + a • (S.A * S.P) := by
  have hba : b * a = 1 := by rw [mul_comm, hab]
  rw [densityL, Y, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, S.P_mul_P]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hba, one_smul]
  abel

lemma densityU0_mul_densityV0 (a b : ℝ) (hab : a * b = 1) :
    S.densityU0 a * S.densityV0 b = -(S.densityL a b + S.Y) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Fin.sum_univ_two, densityU0_zero, densityU0_one,
    densityV0_zero, densityV0_one, S.densityL_add_Y a b hab]
  simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    S.P_apply, S.P_mul_A, S.A_mul_P, Matrix.of_apply]
  ring

/-- The inverse series of `I-z(P+aA)(P-bA)`. -/
def densityRm (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ⟦X⟧ := resolvent (S.densityL a b)

/-- The power-series columns `z[e,-aAe]`. -/
def densityUps (a : ℝ) : Matrix (Fin n) (Fin 2) ℝ⟦X⟧ :=
  (X : ℝ⟦X⟧) • toPS (S.densityU0 a)

/-- The constant power-series rows `[bAe-e;e]`. -/
def densityVps (b : ℝ) : Matrix (Fin 2) (Fin n) ℝ⟦X⟧ := toPS (S.densityV0 b)

/-- The two-dimensional fixed-density Schur-complement matrix. -/
def densityM2 (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ⟦X⟧ :=
  1 + S.densityVps b * S.Nm * S.densityUps a

lemma density_decomposition (a b : ℝ) (hab : a * b = 1) :
    (1 - (X : ℝ⟦X⟧) • toPS (S.densityL a b)) =
      (1 - (X : ℝ⟦X⟧) • toPS (-S.Y)) + S.densityUps a * S.densityVps b := by
  have h : S.densityUps a * S.densityVps b =
      -((X : ℝ⟦X⟧) • (toPS (S.densityL a b) + toPS S.Y)) := by
    rw [densityUps, densityVps, Matrix.smul_mul, ← toPS_mul,
      S.densityU0_mul_densityV0 a b hab, toPS_neg, toPS_add, smul_neg]
  rw [h, toPS_neg, smul_neg, sub_neg_eq_add, smul_add]
  abel

lemma density_hderiv (a b : ℝ) :
    (S.densityVps b * S.Nm) * (S.Nm * S.densityUps a) =
      (X : ℝ⟦X⟧) • matDeriv (S.densityM2 a b) := by
  have hsq : S.Nm * S.Nm = S.Nm + (X : ℝ⟦X⟧) • matDeriv S.Nm := resolvent_sq _
  have hlhs : (S.densityVps b * S.Nm) * (S.Nm * S.densityUps a) =
      S.densityVps b * S.Nm * S.densityUps a +
        (X : ℝ⟦X⟧) • (S.densityVps b * matDeriv S.Nm * S.densityUps a) := by
    have : (S.densityVps b * S.Nm) * (S.Nm * S.densityUps a) =
        S.densityVps b * (S.Nm * S.Nm) * S.densityUps a := by
      simp only [Matrix.mul_assoc]
    rw [this, hsq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hV : matDeriv (S.densityVps b) = 0 := by
    rw [densityVps]
    exact matDeriv_toPS _
  have hU : matDeriv (S.densityUps a) = toPS (S.densityU0 a) := by
    rw [densityUps, matDeriv_X_smul, matDeriv_toPS, smul_zero, add_zero]
  have hM : matDeriv (S.densityM2 a b) =
      S.densityVps b * matDeriv S.Nm * S.densityUps a +
        S.densityVps b * S.Nm * toPS (S.densityU0 a) := by
    rw [densityM2, matDeriv_add', matDeriv_one, zero_add, matDeriv_mul, matDeriv_mul,
      hV, hU, Matrix.zero_mul, zero_add]
  have hscale : S.densityVps b * S.Nm * S.densityUps a =
      (X : ℝ⟦X⟧) • (S.densityVps b * S.Nm * toPS (S.densityU0 a)) := by
    rw [densityUps, Matrix.mul_smul]
  rw [hlhs, hM, smul_add, hscale]
  abel

lemma density_constantCoeff_det_M2 (a b : ℝ) :
    constantCoeff (Matrix.det (S.densityM2 a b)) = 1 := by
  have hmap : (S.densityM2 a b).map (constantCoeff (R := ℝ)) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    refine Matrix.ext fun s t => ?_
    have hscale : S.densityVps b * S.Nm * S.densityUps a =
        (X : ℝ⟦X⟧) • (S.densityVps b * S.Nm * toPS (S.densityU0 a)) := by
      rw [densityUps, Matrix.mul_smul]
    have h0 : constantCoeff ((S.densityVps b * S.Nm * S.densityUps a) s t) = 0 := by
      rw [hscale, Matrix.smul_apply, smul_eq_mul, map_mul, constantCoeff_X, zero_mul]
    rw [Matrix.map_apply, densityM2, Matrix.add_apply, map_add, h0, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one]

/-- The resolvent trace difference is the logarithmic derivative of the determinant of the
fixed-density Schur-complement matrix. -/
theorem density_traceSeries_sub (a b : ℝ) (hab : a * b = 1) :
    traceSeries (S.densityL a b) - traceSeries (-S.Y) =
      logDeriv (Matrix.det (S.densityM2 a b)) := by
  have hND : S.Nm * (1 - (X : ℝ⟦X⟧) • toPS (-S.Y)) = 1 :=
    resolvent_mul_one_sub_smul _
  have hRR : (1 - (X : ℝ⟦X⟧) • toPS (S.densityL a b)) * S.densityRm a b = 1 :=
    one_sub_smul_mul_resolvent _
  have key := trace_sub_eq_logDeriv
      (Dm := 1 - (X : ℝ⟦X⟧) • toPS (-S.Y)) (Nm := S.Nm)
      (Rinv := 1 - (X : ℝ⟦X⟧) • toPS (S.densityL a b)) (Rm := S.densityRm a b)
      (U := S.densityUps a) (V := S.densityVps b) hND hRR
      (S.density_decomposition a b hab) (S.density_hderiv a b)
      (S.density_constantCoeff_det_M2 a b)
  rw [densityRm, Nm, trace_resolvent, trace_resolvent] at key
  exact key

end Model

end

end AlternatingCycle
