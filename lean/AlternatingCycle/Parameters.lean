import AlternatingCycle.Foundation.Graphon

/-!
# Density parameters

The central density condition supplies positive red and blue densities together with normalized
color coefficients `a`, `b` satisfying `a * b = 1`.  The scalar `delta = b - a` has absolute value
at most one.
-/

namespace AlternatingCycle

/-- The polynomial form of the central density interval. -/
def CentralDensity (p : ℝ) : Prop :=
  0 < p ∧ p < 1 ∧ (2 * p - 1) ^ 2 ≤ p * (1 - p)

lemma CentralDensity.p_pos {p : ℝ} (hp : CentralDensity p) : 0 < p := hp.1

lemma CentralDensity.p_lt_one {p : ℝ} (hp : CentralDensity p) : p < 1 := hp.2.1

lemma CentralDensity.q_pos {p : ℝ} (hp : CentralDensity p) : 0 < 1 - p := by
  linarith [hp.p_lt_one]

lemma CentralDensity.square_le {p : ℝ} (hp : CentralDensity p) :
    (2 * p - 1) ^ 2 ≤ p * (1 - p) := hp.2.2

/-- The polynomial condition is exactly the closed central density interval. -/
theorem centralDensity_iff_interval (p : ℝ) :
    CentralDensity p ↔
      (5 - Real.sqrt 5) / 10 ≤ p ∧ p ≤ (5 + Real.sqrt 5) / 10 := by
  let r : ℝ := Real.sqrt 5
  have hr0 : 0 ≤ r := by simp [r]
  have hr2 : r ^ 2 = 5 := by norm_num [r]
  have hr5 : r < 5 := by nlinarith
  constructor
  · intro hp
    have hquad : 5 * (2 * p - 1) ^ 2 ≤ 1 := by
      nlinarith [hp.square_le]
    have hscaled : (5 * (2 * p - 1)) ^ 2 ≤ r ^ 2 := by
      nlinarith
    have habs : |5 * (2 * p - 1)| ≤ r := by
      have := sq_le_sq.mp hscaled
      simpa [abs_of_nonneg hr0] using this
    have hb := abs_le.mp habs
    constructor <;> nlinarith
  · rintro ⟨hlow, hupp⟩
    have hp0 : 0 < p := by nlinarith
    have hp1 : p < 1 := by nlinarith
    have hscaled : |5 * (2 * p - 1)| ≤ r := by
      apply abs_le.mpr
      constructor <;> nlinarith
    have hsq : (5 * (2 * p - 1)) ^ 2 ≤ r ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hr0] using hscaled)
    refine ⟨hp0, hp1, ?_⟩
    nlinarith

/-- Normalized scalar data attached to a central edge density. -/
structure DensityParams where
  p : ℝ
  q : ℝ
  s : ℝ
  a : ℝ
  b : ℝ
  delta : ℝ
  q_eq : q = 1 - p
  p_pos : 0 < p
  q_pos : 0 < q
  s_pos : 0 < s
  s_sq : s ^ 2 = p * q
  a_eq : a = s / p
  b_eq : b = s / q
  ab_eq : a * b = 1
  delta_eq : delta = b - a
  delta_formula : delta = (p - q) / s
  abs_delta_le_one : |delta| ≤ 1

namespace DensityParams

/-- Construct the normalized scalar data from a central density. -/
noncomputable def ofCentral (p : ℝ) (hp : CentralDensity p) : DensityParams := by
  let q : ℝ := 1 - p
  let s : ℝ := Real.sqrt (p * q)
  let a : ℝ := s / p
  let b : ℝ := s / q
  let delta : ℝ := b - a
  have hp0 : 0 < p := hp.p_pos
  have hq0 : 0 < q := by simpa [q] using hp.q_pos
  have hpq0 : 0 < p * q := mul_pos hp0 hq0
  have hs0 : 0 < s := by simpa [s] using Real.sqrt_pos.2 hpq0
  have hs2 : s ^ 2 = p * q := by
    simpa [s] using Real.sq_sqrt (le_of_lt hpq0)
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hab : a * b = 1 := by
    rw [show a = s / p by rfl, show b = s / q by rfl]
    field_simp
    nlinarith [hs2]
  have hdelta : delta = (p - q) / s := by
    rw [show delta = b - a by rfl, show a = s / p by rfl, show b = s / q by rfl]
    field_simp
    nlinarith [hs2]
  have hnum : p - q = 2 * p - 1 := by simp [q]; ring
  have hratio : ((p - q) / s) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (sq_pos_of_pos hs0)]
    rw [hs2, hnum]
    simpa [q] using hp.square_le
  have habs : |delta| ≤ 1 := by
    rw [hdelta]
    nlinarith [sq_abs ((p - q) / s), abs_nonneg ((p - q) / s)]
  exact
    { p := p
      q := q
      s := s
      a := a
      b := b
      delta := delta
      q_eq := rfl
      p_pos := hp0
      q_pos := hq0
      s_pos := hs0
      s_sq := hs2
      a_eq := rfl
      b_eq := rfl
      ab_eq := hab
      delta_eq := rfl
      delta_formula := hdelta
      abs_delta_le_one := habs }

end DensityParams

end AlternatingCycle
