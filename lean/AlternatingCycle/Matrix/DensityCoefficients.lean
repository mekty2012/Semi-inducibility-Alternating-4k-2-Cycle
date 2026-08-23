import AlternatingCycle.Matrix.DensityBeta

/-!
# Weighted fixed-density coefficients

The fixed-density scalar series is controlled by spectral coefficients that weight each pair of
eigenvalues according to the density asymmetry.
-/

namespace AlternatingCycle

open PowerSeries Finset

noncomputable section

namespace Spectrum

variable {n : ℕ} (T : Spectrum n)

/-- The fixed-density coefficient `beta n - delta*nu n`. -/
def densityBeta (delta : ℝ) (r : ℕ) : ℝ := T.beta r - delta * T.nu r

/-- The two-eigenvalue weight attached to the density asymmetry. -/
def densityWeight (delta x y : ℝ) : ℝ := 1 - delta * (x + y) / 2

/-- The scalar series is the alternating generating series of `densityBeta`. -/
lemma densityBeta_series (delta : ℝ) :
    T.hSer ^ 2 - delta • T.kSer + X * T.kSer ^ 2 = betaSeries (T.densityBeta delta) := by
  calc
    T.hSer ^ 2 - delta • T.kSer + X * T.kSer ^ 2 =
        betaSeries T.beta - delta • T.kSer := by rw [← T.hSer_sq_add]; abel
    _ = betaSeries (T.densityBeta delta) := by
      ext r
      rw [map_sub, coeff_betaSeries, coeff_smul, T.coeff_kSer, coeff_betaSeries]
      simp only [densityBeta, smul_eq_mul]
      ring

lemma odd_weighted_double_sum (r : ℕ) :
    ∑ i, ∑ j, T.e i ^ 2 * T.e j ^ 2 *
        ((T.lam i + T.lam j) * cn r (T.lam i) (T.lam j)) = 2 * T.nu r := by
  calc
    ∑ i, ∑ j, T.e i ^ 2 * T.e j ^ 2 *
        ((T.lam i + T.lam j) * cn r (T.lam i) (T.lam j)) =
      ∑ i, ∑ j, ((T.e i ^ 2 * T.lam i ^ (2 * r + 1)) * T.e j ^ 2 +
          T.e i ^ 2 * (T.e j ^ 2 * T.lam j ^ (2 * r + 1))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [add_mul_cn]
        ring
    _ = 2 * T.nu r := by
      have hinner : ∀ i : Fin n,
          ∑ j, ((T.e i ^ 2 * T.lam i ^ (2 * r + 1)) * T.e j ^ 2 +
            T.e i ^ 2 * (T.e j ^ 2 * T.lam j ^ (2 * r + 1))) =
            T.e i ^ 2 * T.lam i ^ (2 * r + 1) + T.e i ^ 2 * T.nu r := by
        intro i
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, T.e_unit]
        simp [Spectrum.nu]
      rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_add_distrib,
        ← Finset.sum_mul, T.e_unit, one_mul, Spectrum.nu]
      ring

/-- `densityBeta` is the double spectral sum with the fixed-density weight. -/
lemma densityBeta_eq_weighted_sum (delta : ℝ) (r : ℕ) :
    T.densityBeta delta r =
      ∑ i, ∑ j, T.e i ^ 2 * T.e j ^ 2 * cn r (T.lam i) (T.lam j) *
        densityWeight delta (T.lam i) (T.lam j) := by
  have hodd := T.odd_weighted_double_sum r
  calc
    T.densityBeta delta r = T.beta r - (delta / 2) * (2 * T.nu r) := by
      simp only [densityBeta]
      ring
    _ = T.beta r - (delta / 2) *
        (∑ i, ∑ j, T.e i ^ 2 * T.e j ^ 2 *
          ((T.lam i + T.lam j) * cn r (T.lam i) (T.lam j))) := by rw [hodd]
    _ = ∑ i, ∑ j, T.e i ^ 2 * T.e j ^ 2 * cn r (T.lam i) (T.lam j) *
        densityWeight delta (T.lam i) (T.lam j) := by
      rw [Spectrum.beta, Finset.mul_sum]
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [densityWeight]
      ring

lemma lam_abs_le_one (i : Fin n) : |T.lam i| ≤ 1 := by
  have hs : T.lam i ^ 2 ≤ 1 := le_trans (T.lam_sq_le_tau i) T.tau_le_one
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (T.lam i - 1), sq_nonneg (T.lam i + 1)]

lemma densityWeight_nonneg {delta : ℝ} (hdelta : |delta| ≤ 1) (i j : Fin n) :
    0 ≤ densityWeight delta (T.lam i) (T.lam j) := by
  have hi := T.lam_abs_le_one i
  have hj := T.lam_abs_le_one j
  have havg : |(T.lam i + T.lam j) / 2| ≤ 1 := by
    calc
      |(T.lam i + T.lam j) / 2| = |T.lam i + T.lam j| / 2 := by rw [abs_div]; norm_num
      _ ≤ (|T.lam i| + |T.lam j|) / 2 := by gcongr; exact abs_add_le _ _
      _ ≤ 1 := by linarith
  have hprod : |delta * ((T.lam i + T.lam j) / 2)| ≤ 1 := by
    rw [abs_mul]
    calc
      |delta| * |(T.lam i + T.lam j) / 2| ≤ 1 * 1 :=
        mul_le_mul hdelta havg (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have := le_trans (le_abs_self (delta * ((T.lam i + T.lam j) / 2))) hprod
  simp only [densityWeight]
  linarith

lemma densityBeta_nonneg {delta : ℝ} (hdelta : |delta| ≤ 1) (r : ℕ) :
    0 ≤ T.densityBeta delta r := by
  rw [T.densityBeta_eq_weighted_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (cn_nonneg _ _ _))
      (T.densityWeight_nonneg hdelta i j)

lemma densityBeta_zero {delta : ℝ} (hnu0 : T.nu 0 = 0) : T.densityBeta delta 0 = 1 := by
  rw [densityBeta, T.beta_zero, hnu0, mul_zero, sub_zero]

lemma densityBeta_one {delta : ℝ} (hnu0 : T.nu 0 = 0) :
    T.densityBeta delta 1 = 2 * T.mu 1 - delta * T.nu 1 := by
  rw [densityBeta, T.beta_one_eq, hnu0]
  ring

/-- From the second coefficient onward, the weighted coefficients satisfy the recursive spectral
inequality. -/
lemma densityBeta_succ_le_tau {delta : ℝ} (hdelta : |delta| ≤ 1) (r : ℕ) :
    T.densityBeta delta (r + 2) ≤ T.tau * T.densityBeta delta (r + 1) := by
  rw [T.densityBeta_eq_weighted_sum, T.densityBeta_eq_weighted_sum, Finset.mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  let c := T.e i ^ 2 * T.e j ^ 2 * densityWeight delta (T.lam i) (T.lam j)
  have hc : 0 ≤ c :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (T.densityWeight_nonneg hdelta i j)
  calc
    T.e i ^ 2 * T.e j ^ 2 * cn (r + 2) (T.lam i) (T.lam j) *
        densityWeight delta (T.lam i) (T.lam j) =
      c * cn (r + 2) (T.lam i) (T.lam j) := by ring
    _ ≤ c * (T.tau * cn (r + 1) (T.lam i) (T.lam j)) :=
      mul_le_mul_of_nonneg_left (T.cn_step r i j) hc
    _ = T.tau *
        (T.e i ^ 2 * T.e j ^ 2 * cn (r + 1) (T.lam i) (T.lam j) *
          densityWeight delta (T.lam i) (T.lam j)) := by ring

/-- The inequality for the first coefficient and the spectral bound give the complete
nonincreasing chain. -/
lemma densityBeta_antitone {delta : ℝ} (hdelta : |delta| ≤ 1)
    (hnu0 : T.nu 0 = 0) (hhead : 2 * T.mu 1 - delta * T.nu 1 ≤ 1) :
    ∀ r, T.densityBeta delta (r + 1) ≤ T.densityBeta delta r := by
  intro r
  cases r with
  | zero =>
      rw [T.densityBeta_zero hnu0, T.densityBeta_one hnu0]
      exact hhead
  | succ r =>
      have hstep := T.densityBeta_succ_le_tau hdelta r
      have hnonneg := T.densityBeta_nonneg hdelta (r + 1)
      have htau := T.tau_le_one
      nlinarith [mul_nonneg T.tau_nonneg hnonneg]

/-- The diagonal fixed-density matrix inequality. -/
theorem matrix_fixedDensity_diagonal (a b delta : ℝ) (hab : a * b = 1)
    (hdelta_eq : delta = b - a) (hdelta : |delta| ≤ 1)
    (hnu0 : T.nu 0 = 0) (hhead : 2 * T.mu 1 - delta * T.nu 1 ≤ 1)
    {m : ℕ} (hm : Odd m) :
    Matrix.trace (T.model.densityL a b ^ m) + Matrix.trace (T.model.A ^ (2 * m)) ≤ 1 := by
  rw [T.density_trace_coefficient a b hab hm, T.det_densityM2 a b hab, ← hdelta_eq,
    T.densityBeta_series delta]
  exact coeff_logDeriv_betaSeries_le_one (T.densityBeta_zero hnu0)
    (T.densityBeta_antitone hdelta hnu0 hhead) hm

end Spectrum

end

end AlternatingCycle
