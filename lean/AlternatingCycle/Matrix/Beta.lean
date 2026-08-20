import AlternatingCycle.Matrix.Model
import AlternatingCycle.Matrix.Spectral

/-!
# `det M₂ = 1 − z F(z)`

This is `lem:det-factor` finished: the `2 × 2` Schur determinant of `Model.lean` is identified with
the series `F` of `Spectral.lean`.

We work in the **diagonal** model `A = diagonal λ`, where `N(z)` is diagonal and every bilinear form
`⟨a, N(z) b⟩` collapses to a single sum.  Then

```
  M₂ = ⎡ 1 + z(k − h)   z(k − ℓ) ⎤,      det M₂ = 1 − z(h² + zk²) = 1 − z F(z),
       ⎣    z h          1 − z k ⎦
```

the last step by `eq:h-ell` (`h + zℓ = 1`), exactly as in the note.  Working in a diagonalizing
basis costs nothing: `thm:matrix` only involves traces and a unit vector, both invariant under
orthogonal conjugation, so the spectral theorem is needed once at the interface and never inside
the argument.
-/

namespace AlternatingCycle

open PowerSeries Matrix Finset

noncomputable section

variable {n : ℕ} (T : Spectrum n)

/-- The rank-one model attached to spectral data, in a diagonalizing basis. -/
def Spectrum.model : Model n where
  A := Matrix.diagonal T.lam
  e := T.e
  A_symm := Matrix.diagonal_transpose T.lam
  e_unit := by
    have h : ∑ i, T.e i * T.e i = ∑ i, T.e i ^ 2 :=
      Finset.sum_congr rfl fun i _ => (pow_two (T.e i)).symm
    simpa [dotProduct, h] using T.e_unit

@[simp] lemma model_A : T.model.A = Matrix.diagonal T.lam := rfl
@[simp] lemma model_e : T.model.e = T.e := rfl

lemma model_u (i : Fin n) : T.model.u i = T.lam i * T.e i := by
  rw [Model.u, model_A, Matrix.mulVec_diagonal, model_e]

lemma model_Y : T.model.Y = Matrix.diagonal fun i => T.lam i ^ 2 := by
  rw [Model.Y, model_A, Matrix.diagonal_mul_diagonal]
  exact congrArg _ (funext fun i => (pow_two (T.lam i)).symm)

lemma model_neg_Y : -T.model.Y = Matrix.diagonal fun i => -(T.lam i ^ 2) := by
  rw [model_Y]
  exact Matrix.diagonal_neg (fun i => T.lam i ^ 2)

/-- The diagonal entries of `N(z)`, namely `∑_r (−λ_i²)^r z^r`. -/
def Ndiag (j : Fin n) : ℝ⟦X⟧ := PowerSeries.mk fun r => (-(T.lam j ^ 2)) ^ r

lemma model_Nm_apply (i j : Fin n) :
    T.model.Nm i j = if i = j then Ndiag T i else 0 := by
  refine PowerSeries.ext fun r => ?_
  rw [Model.Nm, resolvent, Matrix.of_apply, coeff_mk, model_neg_Y, Matrix.diagonal_pow]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, if_pos rfl, Ndiag, coeff_mk]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, if_neg h, map_zero]

/-! ### The entries of `M₂` -/

lemma VNU_eq (s t : Fin 2) :
    (T.model.Vps * T.model.Nm * T.model.Ups) s t
      = X * PowerSeries.mk fun r =>
          (-1) ^ r * ∑ j, T.model.Vm s j * T.model.U₀ j t * T.lam j ^ (2 * r) := by
  have hVN : ∀ j : Fin n, (T.model.Vps * T.model.Nm) s j = C (T.model.Vm s j) * Ndiag T j := by
    intro j
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [model_Nm_apply, if_pos rfl, Model.Vps, toPS_apply]
    · intro i _ hij
      rw [model_Nm_apply, if_neg hij, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hU : ∀ j : Fin n, T.model.Ups j t = X * C (T.model.U₀ j t) := by
    intro j
    rw [Model.Ups, Matrix.smul_apply, toPS_apply, smul_eq_mul]
  have hall : (T.model.Vps * T.model.Nm * T.model.Ups) s t
      = X * ∑ j, C (T.model.Vm s j * T.model.U₀ j t) * Ndiag T j := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hVN j, hU j, map_mul]
    ring
  rw [hall]
  congr 1
  refine PowerSeries.ext fun r => ?_
  rw [map_sum, coeff_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_C_mul, Ndiag, coeff_mk]
  have hpow : (-(T.lam j ^ 2)) ^ r = (-1) ^ r * T.lam j ^ (2 * r) := by
    rw [neg_pow, ← pow_mul]
  rw [hpow]
  ring

lemma model_Vm_zero (j : Fin n) : T.model.Vm 0 j = T.lam j * T.e j - T.e j := by
  rw [Model.Vm_zero, model_u, model_e]

lemma model_Vm_one (j : Fin n) : T.model.Vm 1 j = T.e j := rfl

lemma model_U₀_zero (j : Fin n) : T.model.U₀ j 0 = T.e j := rfl

lemma model_U₀_one (j : Fin n) : T.model.U₀ j 1 = -(T.lam j * T.e j) := by
  rw [Model.U₀_one, model_u]

lemma M2_00 : T.model.M2 0 0 = 1 + X * (T.kSer - T.hSer) := by
  have hser : (PowerSeries.mk fun r =>
      (-1) ^ r * ∑ j, T.model.Vm 0 j * T.model.U₀ j 0 * T.lam j ^ (2 * r))
      = T.kSer - T.hSer := by
    refine PowerSeries.ext fun r => ?_
    have hsum : ∑ j, T.model.Vm 0 j * T.model.U₀ j 0 * T.lam j ^ (2 * r) = T.nu r - T.mu r := by
      rw [Spectrum.nu, Spectrum.mu, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [model_Vm_zero, model_U₀_zero]
      ring
    rw [coeff_mk, hsum, map_sub, T.coeff_kSer, T.coeff_hSer]
    ring
  rw [Model.M2, Matrix.add_apply, Matrix.one_apply_eq, VNU_eq, hser]

lemma M2_01 : T.model.M2 0 1 = X * (T.kSer - T.lSer) := by
  have hser : (PowerSeries.mk fun r =>
      (-1) ^ r * ∑ j, T.model.Vm 0 j * T.model.U₀ j 1 * T.lam j ^ (2 * r))
      = T.kSer - T.lSer := by
    refine PowerSeries.ext fun r => ?_
    have hsum : ∑ j, T.model.Vm 0 j * T.model.U₀ j 1 * T.lam j ^ (2 * r)
        = T.nu r - T.mu (r + 1) := by
      rw [Spectrum.nu, Spectrum.mu, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [model_Vm_zero, model_U₀_one]
      ring
    rw [coeff_mk, hsum, map_sub, T.coeff_kSer, T.coeff_lSer]
    ring
  rw [Model.M2, Matrix.add_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), zero_add,
    VNU_eq, hser]

lemma M2_10 : T.model.M2 1 0 = X * T.hSer := by
  have hser : (PowerSeries.mk fun r =>
      (-1) ^ r * ∑ j, T.model.Vm 1 j * T.model.U₀ j 0 * T.lam j ^ (2 * r)) = T.hSer := by
    refine PowerSeries.ext fun r => ?_
    have hsum : ∑ j, T.model.Vm 1 j * T.model.U₀ j 0 * T.lam j ^ (2 * r) = T.mu r := by
      rw [Spectrum.mu]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [model_Vm_one, model_U₀_zero]
      ring
    rw [coeff_mk, hsum, T.coeff_hSer]
  rw [Model.M2, Matrix.add_apply, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), zero_add,
    VNU_eq, hser]

lemma M2_11 : T.model.M2 1 1 = 1 - X * T.kSer := by
  have hser : (PowerSeries.mk fun r =>
      (-1) ^ r * ∑ j, T.model.Vm 1 j * T.model.U₀ j 1 * T.lam j ^ (2 * r)) = -T.kSer := by
    refine PowerSeries.ext fun r => ?_
    have hsum : ∑ j, T.model.Vm 1 j * T.model.U₀ j 1 * T.lam j ^ (2 * r) = -T.nu r := by
      rw [Spectrum.nu, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [model_Vm_one, model_U₀_one]
      ring
    rw [coeff_mk, hsum, map_neg, T.coeff_kSer]
    ring
  rw [Model.M2, Matrix.add_apply, Matrix.one_apply_eq, VNU_eq, hser, mul_neg, ← sub_eq_add_neg]

/-! ### The determinant -/

/-- **`eq:det-factor`.**  `det M₂ = 1 − z F(z)` with `F = ∑ (-1)^n β_n z^n`. -/
theorem det_M2 : Matrix.det T.model.M2 = 1 - X * betaSeries T.beta := by
  rw [Matrix.det_fin_two, M2_00, M2_01, M2_10, M2_11, ← T.hSer_sq_add]
  linear_combination (X * T.hSer) * T.hSer_add_X_mul_lSer

end

end AlternatingCycle
