import AlternatingCycle.Matrix.DensityModel
import AlternatingCycle.Matrix.Beta

/-!
# The determinant of the fixed-density Schur complement

For diagonal spectral data, the determinant of the two-dimensional Schur-complement matrix is
expressed through the even and odd scalar resolvent moments.
-/

namespace AlternatingCycle

open PowerSeries Matrix Finset

noncomputable section

namespace Spectrum

variable {n : ℕ} (T : Spectrum n)

lemma densityVNU_eq (a b : ℝ) (s t : Fin 2) :
    (T.model.densityVps b * T.model.Nm * T.model.densityUps a) s t =
      X * PowerSeries.mk fun r =>
        (-1) ^ r * ∑ j,
          T.model.densityV0 b s j * T.model.densityU0 a j t * T.lam j ^ (2 * r) := by
  have hVN : ∀ j : Fin n,
      (T.model.densityVps b * T.model.Nm) s j =
        C (T.model.densityV0 b s j) * Ndiag T j := by
    intro j
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [model_Nm_apply, if_pos rfl, Model.densityVps, toPS_apply]
    · intro i _ hij
      rw [model_Nm_apply, if_neg hij, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hU : ∀ j : Fin n,
      T.model.densityUps a j t = X * C (T.model.densityU0 a j t) := by
    intro j
    rw [Model.densityUps, Matrix.smul_apply, toPS_apply, smul_eq_mul]
  have hall :
      (T.model.densityVps b * T.model.Nm * T.model.densityUps a) s t =
        X * ∑ j, C (T.model.densityV0 b s j * T.model.densityU0 a j t) * Ndiag T j := by
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

lemma densityM2_00 (a b : ℝ) :
    T.model.densityM2 a b 0 0 = 1 + X * (b • T.kSer - T.hSer) := by
  have hser : (PowerSeries.mk fun r =>
      (-1) ^ r * ∑ j,
        T.model.densityV0 b 0 j * T.model.densityU0 a j 0 * T.lam j ^ (2 * r)) =
      b • T.kSer - T.hSer := by
    refine PowerSeries.ext fun r => ?_
    have hsum : ∑ j,
        T.model.densityV0 b 0 j * T.model.densityU0 a j 0 * T.lam j ^ (2 * r) =
        b * T.nu r - T.mu r := by
      rw [Spectrum.nu, Spectrum.mu, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Model.densityV0_zero, Model.densityU0_zero, model_u, model_e]
      ring
    rw [coeff_mk, hsum, map_sub, coeff_smul, T.coeff_kSer, T.coeff_hSer]
    simp only [smul_eq_mul]
    ring
  rw [Model.densityM2, Matrix.add_apply, Matrix.one_apply_eq, densityVNU_eq, hser]

lemma densityM2_01 (a b : ℝ) (hab : a * b = 1) :
    T.model.densityM2 a b 0 1 = X * (a • T.kSer - T.lSer) := by
  have hser : (PowerSeries.mk fun r =>
      (-1) ^ r * ∑ j,
        T.model.densityV0 b 0 j * T.model.densityU0 a j 1 * T.lam j ^ (2 * r)) =
      a • T.kSer - T.lSer := by
    refine PowerSeries.ext fun r => ?_
    have hsum : ∑ j,
        T.model.densityV0 b 0 j * T.model.densityU0 a j 1 * T.lam j ^ (2 * r) =
        a * T.nu r - T.mu (r + 1) := by
      rw [Spectrum.nu, Spectrum.mu, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Model.densityV0_zero, Model.densityU0_one, model_u, model_e]
      have hba : b * a = 1 := by rw [mul_comm, hab]
      rw [show 2 * (r + 1) = 2 * r + 2 by omega]
      rw [show T.lam j ^ (2 * r + 1) = T.lam j ^ (2 * r) * T.lam j by rw [pow_succ],
        show T.lam j ^ (2 * r + 2) = T.lam j ^ (2 * r) * T.lam j ^ 2 by rw [pow_add]]
      linear_combination -(T.e j ^ 2 * T.lam j ^ (2 * r) * T.lam j ^ 2) * hba
    rw [coeff_mk, hsum, map_sub, coeff_smul, T.coeff_kSer, T.coeff_lSer]
    simp only [smul_eq_mul]
    ring
  rw [Model.densityM2, Matrix.add_apply,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), zero_add, densityVNU_eq, hser]

lemma densityM2_10 (a b : ℝ) :
    T.model.densityM2 a b 1 0 = X * T.hSer := by
  have hser : (PowerSeries.mk fun r =>
      (-1) ^ r * ∑ j,
        T.model.densityV0 b 1 j * T.model.densityU0 a j 0 * T.lam j ^ (2 * r)) =
      T.hSer := by
    refine PowerSeries.ext fun r => ?_
    have hsum : ∑ j,
        T.model.densityV0 b 1 j * T.model.densityU0 a j 0 * T.lam j ^ (2 * r) =
        T.mu r := by
      rw [Spectrum.mu]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Model.densityV0_one, Model.densityU0_zero, model_e]
      ring
    rw [coeff_mk, hsum, T.coeff_hSer]
  rw [Model.densityM2, Matrix.add_apply,
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), zero_add, densityVNU_eq, hser]

lemma densityM2_11 (a b : ℝ) :
    T.model.densityM2 a b 1 1 = 1 - X * (a • T.kSer) := by
  have hser : (PowerSeries.mk fun r =>
      (-1) ^ r * ∑ j,
        T.model.densityV0 b 1 j * T.model.densityU0 a j 1 * T.lam j ^ (2 * r)) =
      -(a • T.kSer) := by
    refine PowerSeries.ext fun r => ?_
    have hsum : ∑ j,
        T.model.densityV0 b 1 j * T.model.densityU0 a j 1 * T.lam j ^ (2 * r) =
        -(a * T.nu r) := by
      rw [Spectrum.nu, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Model.densityV0_one, Model.densityU0_one, model_u, model_e]
      ring
    rw [coeff_mk, hsum, map_neg, coeff_smul, T.coeff_kSer]
    simp only [smul_eq_mul]
    ring
  rw [Model.densityM2, Matrix.add_apply, Matrix.one_apply_eq, densityVNU_eq, hser,
    mul_neg, ← sub_eq_add_neg]

/-- The determinant is governed by `h²-(b-a)k+zk²`. -/
theorem det_densityM2 (a b : ℝ) (hab : a * b = 1) :
    Matrix.det (T.model.densityM2 a b) =
      1 - X * (T.hSer ^ 2 - (b - a) • T.kSer + X * T.kSer ^ 2) := by
  have hab' : C a * C b = (1 : ℝ⟦X⟧) := by
    rw [← map_mul, hab, map_one]
  rw [Matrix.det_fin_two, densityM2_00, densityM2_01 T a b hab,
    densityM2_10, densityM2_11]
  simp only [Algebra.smul_def, map_sub, PowerSeries.algebraMap_eq]
  linear_combination
    (X * T.hSer) * T.hSer_add_X_mul_lSer +
    -(X * T.kSer) * (X * T.kSer) * hab'

/-- At an odd coefficient, the fixed-density Schur-complement identity gives the sum of the period-two trace
and the even spectral trace. -/
theorem density_trace_coefficient (a b : ℝ) (hab : a * b = 1) {m : ℕ} (hm : Odd m) :
    Matrix.trace (T.model.densityL a b ^ m) + Matrix.trace (T.model.A ^ (2 * m)) =
      coeff m (logDeriv (Matrix.det (T.model.densityM2 a b))) := by
  have hY : T.model.Y ^ m = T.model.A ^ (2 * m) := by
    rw [Model.Y, ← pow_two, ← pow_mul]
  have hneg : coeff m (traceSeries (-T.model.Y)) =
      -Matrix.trace (T.model.A ^ (2 * m)) := by
    rw [coeff_traceSeries, hm.neg_pow, hY, Matrix.trace_neg]
  have hkey := congrArg (coeff m) (T.model.density_traceSeries_sub a b hab)
  rw [map_sub, coeff_traceSeries, hneg] at hkey
  rw [← hkey]
  ring

end Spectrum

end

end AlternatingCycle
