import AlternatingCycle.Matrix.Series.Jacobi2

/-!
# The rank-one model and the trace identity

The data are a symmetric matrix `A` and a unit vector `e`; we write

```
  P = e ⊗ e,   u = A e,   Y = A²,   L = (P + A)(P − A).
```

Expanding `L` and using `P² = P`, `PA = e ⊗ u`, and `AP = u ⊗ e` gives

```
  I − zL = (I + zY) + 𝒰 𝒱,        𝒰 = z·[e, −u],   𝒱 = [u − e; e],
```

a rank-two perturbation of `D = I + zY`.  `Series/Schur.lean` then turns this into a `2 × 2`
statement, `Series/Resolvent.lean` supplies `N² = N + zN'`, and `Series/Jacobi2.lean` closes the
loop, giving the main result of this file:

```
  traceSeries L − traceSeries (−Y) = Λ (det M₂),        M₂ = I₂ + 𝒱 N 𝒰.
```

For odd `m`, coefficient extraction yields the required trace expression.  `Beta.lean` identifies
`det M₂` with `1 − zF(z)`.
-/

namespace AlternatingCycle

open PowerSeries Matrix Finset

noncomputable section

/-- A symmetric matrix together with a distinguished unit vector. -/
structure Model (n : ℕ) where
  /-- The self-adjoint matrix. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The distinguished unit vector. -/
  e : Fin n → ℝ
  A_symm : A.transpose = A
  e_unit : e ⬝ᵥ e = 1

namespace Model

variable {n : ℕ} (S : Model n)

/-- `u = A e`. -/
def u : Fin n → ℝ := S.A *ᵥ S.e

/-- The rank-one projection `P = e ⊗ e`. -/
def P : Matrix (Fin n) (Fin n) ℝ := Matrix.vecMulVec S.e S.e

/-- `Y = A²`. -/
def Y : Matrix (Fin n) (Fin n) ℝ := S.A * S.A

/-- The alternating product `L = (P + A)(P − A)`. -/
def L : Matrix (Fin n) (Fin n) ℝ := (S.P + S.A) * (S.P - S.A)

@[simp] lemma P_apply (i j : Fin n) : S.P i j = S.e i * S.e j := rfl

lemma A_apply_symm (i j : Fin n) : S.A i j = S.A j i := by
  conv_lhs => rw [← S.A_symm]
  rfl

lemma u_apply (i : Fin n) : S.u i = ∑ k, S.A i k * S.e k := rfl

/-! ### The rank-one algebra -/

lemma P_mul_P : S.P * S.P = S.P := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply]
  simp only [P_apply]
  have : ∑ k, S.e i * S.e k * (S.e k * S.e j) = (S.e i * S.e j) * ∑ k, S.e k * S.e k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  have he : ∑ k, S.e k * S.e k = 1 := S.e_unit
  rw [he, mul_one]

lemma P_mul_A : S.P * S.A = Matrix.of fun i j => S.e i * S.u j := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply]
  simp only [P_apply, Matrix.of_apply, u_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [S.A_apply_symm j k]; ring

lemma A_mul_P : S.A * S.P = Matrix.of fun i j => S.u i * S.e j := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply]
  simp only [P_apply, Matrix.of_apply, u_apply]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Expanding `L` and cancelling `A²`. -/
lemma L_add_Y : S.L + S.Y = S.P - S.P * S.A + S.A * S.P := by
  rw [L, Y, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, P_mul_P]
  abel

/-! ### The rank-two factors -/

/-- The columns `[e, −u]` of `𝒰`; the factor `z` is attached in `Ups`. -/
def U₀ : Matrix (Fin n) (Fin 2) ℝ := Matrix.of fun i => ![S.e i, -(S.u i)]

/-- The rows `[u − e; e]` of `𝒱`. -/
def Vm : Matrix (Fin 2) (Fin n) ℝ := Matrix.of fun s j => (![S.u j - S.e j, S.e j] : Fin 2 → ℝ) s

@[simp] lemma U₀_zero (i : Fin n) : S.U₀ i 0 = S.e i := rfl
@[simp] lemma U₀_one (i : Fin n) : S.U₀ i 1 = -(S.u i) := rfl
@[simp] lemma Vm_zero (j : Fin n) : S.Vm 0 j = S.u j - S.e j := rfl
@[simp] lemma Vm_one (j : Fin n) : S.Vm 1 j = S.e j := rfl

lemma U₀_mul_Vm : S.U₀ * S.Vm = -(S.L + S.Y) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Fin.sum_univ_two, U₀_zero, U₀_one, Vm_zero, Vm_one, L_add_Y]
  simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.sub_apply, P_apply, P_mul_A, A_mul_P,
    Matrix.of_apply]
  ring

/-! ### The power-series objects -/

/-- `N = (I + zY)⁻¹`. -/
def Nm : Matrix (Fin n) (Fin n) ℝ⟦X⟧ := resolvent (-S.Y)

/-- `R = (I − zL)⁻¹`. -/
def Rm : Matrix (Fin n) (Fin n) ℝ⟦X⟧ := resolvent S.L

/-- `𝒰 = z·[e, −u]`. -/
def Ups : Matrix (Fin n) (Fin 2) ℝ⟦X⟧ := (X : ℝ⟦X⟧) • toPS S.U₀

/-- `𝒱 = [u − e; e]`. -/
def Vps : Matrix (Fin 2) (Fin n) ℝ⟦X⟧ := toPS S.Vm

/-- The `2 × 2` Schur-complement matrix `M₂ = I₂ + 𝒱 N 𝒰`. -/
def M2 : Matrix (Fin 2) (Fin 2) ℝ⟦X⟧ := 1 + S.Vps * S.Nm * S.Ups

/-- **The rank-two decomposition `I − zL = D + 𝒰𝒱`.** -/
lemma decomposition :
    (1 - (X : ℝ⟦X⟧) • toPS S.L) = (1 - (X : ℝ⟦X⟧) • toPS (-S.Y)) + S.Ups * S.Vps := by
  have h : S.Ups * S.Vps = -((X : ℝ⟦X⟧) • (toPS S.L + toPS S.Y)) := by
    rw [Ups, Vps, Matrix.smul_mul, ← toPS_mul, U₀_mul_Vm, toPS_neg, toPS_add, smul_neg]
  rw [h, toPS_neg, smul_neg, sub_neg_eq_add, smul_add]
  abel

/-! ### Matrix derivatives -/

lemma matDeriv_toPS {p q : Type*} (M : Matrix p q ℝ) : matDeriv (toPS M) = 0 :=
  Matrix.ext fun i j => by simp [matDeriv, toPS]

lemma matDeriv_add' {p q : Type*} (M N : Matrix p q ℝ⟦X⟧) :
    matDeriv (M + N) = matDeriv M + matDeriv N :=
  Matrix.ext fun i j => by simp [matDeriv]

lemma matDeriv_one {p : Type*} [DecidableEq p] : matDeriv (1 : Matrix p p ℝ⟦X⟧) = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [matDeriv_apply, Matrix.one_apply]
  split_ifs <;> simp

lemma matDeriv_mul {p q r : Type*} [Fintype q] (M : Matrix p q ℝ⟦X⟧) (N : Matrix q r ℝ⟦X⟧) :
    matDeriv (M * N) = matDeriv M * N + M * matDeriv N := by
  refine Matrix.ext fun i j => ?_
  rw [matDeriv_apply, Matrix.mul_apply, map_sum, Matrix.add_apply, Matrix.mul_apply,
    Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.leibniz]
  simp [smul_eq_mul]
  ring

lemma matDeriv_X_smul {p q : Type*} (M : Matrix p q ℝ⟦X⟧) :
    matDeriv ((X : ℝ⟦X⟧) • M) = M + (X : ℝ⟦X⟧) • matDeriv M := by
  refine Matrix.ext fun i j => ?_
  rw [matDeriv_apply, Matrix.smul_apply, smul_eq_mul, Derivation.leibniz]
  simp only [smul_eq_mul, derivative_X, mul_one, Matrix.add_apply, Matrix.smul_apply,
    matDeriv_apply]
  ring

/-- **The derivative hypothesis of `trace_sub_eq_logDeriv`**, i.e. `𝒱 N² 𝒰 = z · (d⁄dX M₂)`.
It rests only on `N² = N + zN'` (`resolvent_sq`). -/
lemma hderiv : (S.Vps * S.Nm) * (S.Nm * S.Ups) = (X : ℝ⟦X⟧) • matDeriv S.M2 := by
  have hsq : S.Nm * S.Nm = S.Nm + (X : ℝ⟦X⟧) • matDeriv S.Nm := resolvent_sq _
  have hlhs : (S.Vps * S.Nm) * (S.Nm * S.Ups)
      = S.Vps * S.Nm * S.Ups + (X : ℝ⟦X⟧) • (S.Vps * matDeriv S.Nm * S.Ups) := by
    have : (S.Vps * S.Nm) * (S.Nm * S.Ups) = S.Vps * (S.Nm * S.Nm) * S.Ups := by
      simp only [Matrix.mul_assoc]
    rw [this, hsq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have h1 : matDeriv S.Vps = 0 := by rw [Vps]; exact matDeriv_toPS _
  have h2 : matDeriv S.Ups = toPS S.U₀ := by
    rw [Ups, matDeriv_X_smul, matDeriv_toPS, smul_zero, add_zero]
  have hM : matDeriv S.M2 = S.Vps * matDeriv S.Nm * S.Ups + S.Vps * S.Nm * toPS S.U₀ := by
    rw [M2, matDeriv_add', matDeriv_one, zero_add, matDeriv_mul, matDeriv_mul, h1, h2,
      Matrix.zero_mul, zero_add]
  have hU : S.Vps * S.Nm * S.Ups = (X : ℝ⟦X⟧) • (S.Vps * S.Nm * toPS S.U₀) := by
    rw [Ups, Matrix.mul_smul]
  rw [hlhs, hM, smul_add, hU]
  abel

/-- The constant term of `det M₂` is `1`, because `𝒰` carries an explicit factor `z`. -/
lemma constantCoeff_det_M2 : constantCoeff (Matrix.det S.M2) = 1 := by
  have hmap : S.M2.map (constantCoeff (R := ℝ)) = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    refine Matrix.ext fun s t => ?_
    have hU : S.Vps * S.Nm * S.Ups = (X : ℝ⟦X⟧) • (S.Vps * S.Nm * toPS S.U₀) := by
      rw [Ups, Matrix.mul_smul]
    have h0 : constantCoeff ((S.Vps * S.Nm * S.Ups) s t) = 0 := by
      rw [hU, Matrix.smul_apply, smul_eq_mul, map_mul, constantCoeff_X, zero_mul]
    rw [Matrix.map_apply, M2, Matrix.add_apply, map_add, h0, add_zero, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one]

/-- The trace identity in resolvent form.  It uses neither an `n × n` determinant nor a formal
logarithm. -/
theorem traceSeries_sub :
    traceSeries S.L - traceSeries (-S.Y) = logDeriv (Matrix.det S.M2) := by
  have hND : S.Nm * (1 - (X : ℝ⟦X⟧) • toPS (-S.Y)) = 1 := resolvent_mul_one_sub_smul _
  have hRR : (1 - (X : ℝ⟦X⟧) • toPS S.L) * S.Rm = 1 := one_sub_smul_mul_resolvent _
  have key := trace_sub_eq_logDeriv (Dm := 1 - (X : ℝ⟦X⟧) • toPS (-S.Y)) (Nm := S.Nm)
      (Rinv := 1 - (X : ℝ⟦X⟧) • toPS S.L) (Rm := S.Rm) (U := S.Ups) (V := S.Vps)
      hND hRR S.decomposition S.hderiv S.constantCoeff_det_M2
  rw [Rm, Nm, trace_resolvent, trace_resolvent] at key
  exact key

end Model

end

end AlternatingCycle
