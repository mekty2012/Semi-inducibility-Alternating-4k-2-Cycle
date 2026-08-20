import AlternatingCycle.Matrix.Scalar.Cn
import AlternatingCycle.Matrix.Scalar.OddLog

/-!
# The coefficients `β_n` and their monotonicity

This is `eq:def-beta`–`lem:beta-monotone` of `alternating_cycles_schur_proof.tex`.  A `Spectrum`
is the spectral data of the
symmetric operator `X` relative to the distinguished unit vector: eigenvalues `λ_i` (with
multiplicity) and coordinates `e_i = ⟨e, v_i⟩`, so that `ω_i = e_i²` and `τ = ∑ λ_i² ≤ 1`.  The
moments are

```
  μ_r = ∑_i ω_i λ_i^{2r} = ⟨e, X^{2r} e⟩,      ν_r = ∑_i ω_i λ_i^{2r+1} = ⟨e, X^{2r+1} e⟩,
```

and `eq:def-beta` reads `β_n = ∑_{i,j} ω_i ω_j c_n(λ_i, λ_j)`.

Main results:

* `beta_zero` — `β₀ = 1` (`eq:spectral-budget`);
* `beta_nonneg` — from `cn_nonneg`;
* `beta_one_le_tau` — `β₁ ≤ τ`, the `n = 0` step of `lem:beta-monotone`;
* `beta_le_tau_mul` — `β_{n+1} ≤ τ β_n` for `n ≥ 1` (`eq:beta-tau-contract`);
* `beta_antitone` — the chain `1 = β₀ ≥ β₁ ≥ … ≥ 0`;
* `beta_succ_conv` — the Cauchy-product shape needed to identify `∑ (-1)^n β_n z^n` with
  `h(z)² + z k(z)²`.

The paper proves `β₁ ≤ τ` by writing `X` in a basis adapted to `e` and reading off `Tr(A²) ≥ 0`
for the compression `A`.  We instead exhibit the compression's Frobenius norm directly: with
`a = ν₀`, `τ − β₁` dominates `∑_i (λ_i − ω_i(2λ_i − a))²`, because the off-diagonal sum
`∑_{i,j} (e_i e_j(λ_i + λ_j − a))²` equals `2μ₁ − a²` and dominates its own diagonal.  No basis
change and no `Submodule` bookkeeping.
-/

namespace AlternatingCycle

open Finset

/-- Spectral data of a symmetric operator relative to a unit vector. -/
structure Spectrum (n : ℕ) where
  /-- The eigenvalues, with multiplicity. -/
  lam : Fin n → ℝ
  /-- The coordinates of the distinguished unit vector in the eigenbasis. -/
  e : Fin n → ℝ
  e_unit : ∑ i, e i ^ 2 = 1
  tau_le : ∑ i, lam i ^ 2 ≤ 1

namespace Spectrum

variable {n : ℕ} (T : Spectrum n)

/-- `τ = Tr(X²)`. -/
def tau : ℝ := ∑ i, T.lam i ^ 2

/-- `μ_r = ⟨e, X^{2r} e⟩`. -/
def mu (r : ℕ) : ℝ := ∑ i, T.e i ^ 2 * T.lam i ^ (2 * r)

/-- `ν_r = ⟨e, X^{2r+1} e⟩`. -/
def nu (r : ℕ) : ℝ := ∑ i, T.e i ^ 2 * T.lam i ^ (2 * r + 1)

/-- `eq:def-beta`. -/
def beta (r : ℕ) : ℝ := ∑ i, ∑ j, T.e i ^ 2 * T.e j ^ 2 * cn r (T.lam i) (T.lam j)

lemma tau_nonneg : 0 ≤ T.tau := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma tau_le_one : T.tau ≤ 1 := T.tau_le

lemma mu_zero : T.mu 0 = 1 := by simp [mu, T.e_unit]

lemma mu_one_eq : T.mu 1 = ∑ i, T.e i ^ 2 * T.lam i ^ 2 := by
  simp [mu]

lemma nu_zero_eq : T.nu 0 = ∑ i, T.e i ^ 2 * T.lam i := by
  simp [nu]

/-! ### Elementary consequences -/

lemma beta_zero : T.beta 0 = 1 := by
  have : T.beta 0 = ∑ i, ∑ j, T.e i ^ 2 * T.e j ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [cn_zero, mul_one]
  rw [this, ← Finset.sum_mul_sum, T.e_unit, mul_one]

lemma beta_nonneg (r : ℕ) : 0 ≤ T.beta r :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (cn_nonneg _ _ _)

lemma lam_sq_le_tau (i : Fin n) : T.lam i ^ 2 ≤ T.tau :=
  Finset.single_le_sum (fun k _ => sq_nonneg (T.lam k)) (Finset.mem_univ i)

lemma lam_sq_add_le_tau {i j : Fin n} (hij : i ≠ j) : T.lam i ^ 2 + T.lam j ^ 2 ≤ T.tau := by
  have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => sq_nonneg (T.lam k))
  rwa [Finset.sum_pair hij] at this

/-! ### `eq:beta-tau-contract` -/

lemma cn_step (r : ℕ) (i j : Fin n) :
    cn (r + 2) (T.lam i) (T.lam j) ≤ T.tau * cn (r + 1) (T.lam i) (T.lam j) := by
  by_cases hij : i = j
  · subst hij
    rw [cn_diag, cn_diag]
    have h1 : T.lam i ^ (2 * (r + 2)) = T.lam i ^ 2 * T.lam i ^ (2 * (r + 1)) := by ring
    have h2 : (0 : ℝ) ≤ T.lam i ^ (2 * (r + 1)) := by rw [pow_mul]; positivity
    rw [h1]
    exact mul_le_mul_of_nonneg_right (T.lam_sq_le_tau i) h2
  · have h1 := cn_le_mul r (T.lam i) (T.lam j)
    have h2 : (T.lam i ^ 2 + T.lam j ^ 2) * cn (r + 1) (T.lam i) (T.lam j)
        ≤ T.tau * cn (r + 1) (T.lam i) (T.lam j) :=
      mul_le_mul_of_nonneg_right (T.lam_sq_add_le_tau hij) (cn_nonneg _ _ _)
    linarith

/-- **`eq:beta-tau-contract`.** -/
lemma beta_le_tau_mul (r : ℕ) : T.beta (r + 2) ≤ T.tau * T.beta (r + 1) := by
  rw [beta, beta, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hw : (0 : ℝ) ≤ T.e i ^ 2 * T.e j ^ 2 := by positivity
  have := T.cn_step r i j
  nlinarith [this, hw]

/-! ### `β₁ ≤ τ` -/

lemma beta_one_eq : T.beta 1 = 2 * T.mu 1 - T.nu 0 ^ 2 := by
  have hexp : ∀ i j, T.e i ^ 2 * T.e j ^ 2 * cn 1 (T.lam i) (T.lam j)
      = (T.e i ^ 2 * T.lam i ^ 2) * T.e j ^ 2 + T.e i ^ 2 * (T.e j ^ 2 * T.lam j ^ 2)
        - (T.e i ^ 2 * T.lam i) * (T.e j ^ 2 * T.lam j) := by
    intro i j; rw [cn_one]; ring
  rw [beta, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hexp i j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [T.e_unit, ← mu_one_eq, ← nu_zero_eq]
  ring

/-- The off-diagonal sum `∑_{i,j} (e_i e_j (λ_i + λ_j − a))² = 2μ₁ − a²`. -/
lemma offdiag_sum_sq : ∑ i, ∑ j, (T.e i * T.e j * (T.lam i + T.lam j - T.nu 0)) ^ 2
    = 2 * T.mu 1 - T.nu 0 ^ 2 := by
  set a := T.nu 0 with ha
  have hsum1 : ∑ j, T.e j ^ 2 = 1 := T.e_unit
  have hsuma : ∑ j, T.e j ^ 2 * T.lam j = a := (T.nu_zero_eq).symm
  have hsum2 : ∑ j, T.e j ^ 2 * T.lam j ^ 2 = T.mu 1 := (T.mu_one_eq).symm
  have hinner : ∀ i, ∑ j, (T.e i * T.e j * (T.lam i + T.lam j - a)) ^ 2
      = T.e i ^ 2 * ((T.lam i - a) ^ 2 + 2 * a * (T.lam i - a) + T.mu 1) := by
    intro i
    have hstep : ∀ j, (T.e i * T.e j * (T.lam i + T.lam j - a)) ^ 2
        = T.e i ^ 2 * ((T.lam i - a) ^ 2 * T.e j ^ 2)
          + T.e i ^ 2 * (2 * (T.lam i - a) * (T.e j ^ 2 * T.lam j))
          + T.e i ^ 2 * (T.e j ^ 2 * T.lam j ^ 2) := by
      intro j; ring
    rw [Finset.sum_congr rfl fun j _ => hstep j]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum1, hsuma, hsum2]
    ring
  rw [Finset.sum_congr rfl fun i _ => hinner i]
  have hstep2 : ∀ i, T.e i ^ 2 * ((T.lam i - a) ^ 2 + 2 * a * (T.lam i - a) + T.mu 1)
      = (T.e i ^ 2 * T.lam i ^ 2) + (-2 * a) * (T.e i ^ 2 * T.lam i) + (a ^ 2 + T.mu 1) * T.e i ^ 2
        + (2 * a) * (T.e i ^ 2 * T.lam i) + (-2 * a ^ 2) * T.e i ^ 2 := by
    intro i; ring
  rw [Finset.sum_congr rfl fun i _ => hstep2 i]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum1, hsuma, hsum2]
  ring

/-- **`β₁ ≤ τ`.** -/
lemma beta_one_le_tau : T.beta 1 ≤ T.tau := by
  set a := T.nu 0 with ha
  have hdiag : ∑ i, (T.e i ^ 2 * (2 * T.lam i - a)) ^ 2
      ≤ ∑ i, ∑ j, (T.e i * T.e j * (T.lam i + T.lam j - a)) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hterm : (T.e i ^ 2 * (2 * T.lam i - a)) ^ 2
        = (T.e i * T.e i * (T.lam i + T.lam i - a)) ^ 2 := by ring
    rw [hterm]
    exact Finset.single_le_sum (f := fun j => (T.e i * T.e j * (T.lam i + T.lam j - a)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : (0 : ℝ) ≤ ∑ i, (T.lam i - T.e i ^ 2 * (2 * T.lam i - a)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hexpand : ∑ i, (T.lam i - T.e i ^ 2 * (2 * T.lam i - a)) ^ 2
      = T.tau - 2 * (2 * T.mu 1 - a ^ 2) + ∑ i, (T.e i ^ 2 * (2 * T.lam i - a)) ^ 2 := by
    have hstep : ∀ i, (T.lam i - T.e i ^ 2 * (2 * T.lam i - a)) ^ 2
        = T.lam i ^ 2 - 2 * (2 * (T.e i ^ 2 * T.lam i ^ 2) + (-a) * (T.e i ^ 2 * T.lam i))
          + (T.e i ^ 2 * (2 * T.lam i - a)) ^ 2 := by
      intro i; ring
    rw [Finset.sum_congr rfl fun i _ => hstep i]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [T.nu_zero_eq.symm, T.mu_one_eq.symm]
    simp only [tau]
    ring
  have hoff := T.offdiag_sum_sq
  rw [beta_one_eq]
  rw [← ha] at hoff ⊢
  linarith [hdiag, hsq, hexpand, hoff]

/-! ### The Cauchy-product form -/

lemma double_sum_conv (g : Fin n → ℕ → ℝ) (s : Finset (ℕ × ℕ)) :
    ∑ i, ∑ j, ∑ p ∈ s, g i p.1 * g j p.2
      = ∑ p ∈ s, (∑ i, g i p.1) * (∑ j, g j p.2) := by
  have h1 : ∀ i : Fin n, ∑ j, ∑ p ∈ s, g i p.1 * g j p.2
      = ∑ p ∈ s, ∑ j, g i p.1 * g j p.2 := fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => by rw [Finset.sum_mul_sum]

/-- `eq:def-beta` in Cauchy-product form: this is what matches `F = h² + z k²`. -/
lemma beta_succ_conv (r : ℕ) : T.beta (r + 1)
    = (∑ p ∈ Finset.antidiagonal (r + 1), T.mu p.1 * T.mu p.2)
      - ∑ p ∈ Finset.antidiagonal r, T.nu p.1 * T.nu p.2 := by
  have hexp : ∀ i j : Fin n, T.e i ^ 2 * T.e j ^ 2 * cn (r + 1) (T.lam i) (T.lam j)
      = (∑ p ∈ Finset.antidiagonal (r + 1),
          (T.e i ^ 2 * T.lam i ^ (2 * p.1)) * (T.e j ^ 2 * T.lam j ^ (2 * p.2)))
        - ∑ p ∈ Finset.antidiagonal r,
            (T.e i ^ 2 * T.lam i ^ (2 * p.1 + 1)) * (T.e j ^ 2 * T.lam j ^ (2 * p.2 + 1)) := by
    intro i j
    rw [cn_succ_eq_Sconv, Sconv, Sconv, mul_sub, Finset.mul_sum, ← mul_assoc, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun p _ => by ring
    · exact Finset.sum_congr rfl fun p _ => by ring
  rw [beta, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hexp i j]
  simp only [Finset.sum_sub_distrib]
  rw [double_sum_conv (fun i m => T.e i ^ 2 * T.lam i ^ (2 * m)),
    double_sum_conv (fun i m => T.e i ^ 2 * T.lam i ^ (2 * m + 1))]
  rfl

/-! ### The scalar resolvents `h`, `k`, `ℓ` -/

open PowerSeries in
/-- `h(z) = ⟨e, N(z) e⟩ = ∑ (-1)^r μ_r z^r`. -/
noncomputable def hSer : ℝ⟦X⟧ := PowerSeries.mk fun r => (-1) ^ r * T.mu r

open PowerSeries in
/-- `k(z) = ⟨u, N(z) e⟩ = ∑ (-1)^r ν_r z^r`. -/
noncomputable def kSer : ℝ⟦X⟧ := PowerSeries.mk fun r => (-1) ^ r * T.nu r

open PowerSeries in
/-- `ℓ(z) = ⟨u, N(z) u⟩ = ∑ (-1)^r μ_{r+1} z^r`. -/
noncomputable def lSer : ℝ⟦X⟧ := PowerSeries.mk fun r => (-1) ^ r * T.mu (r + 1)

open PowerSeries in
@[simp] lemma coeff_hSer (r : ℕ) : coeff r T.hSer = (-1) ^ r * T.mu r := by simp [hSer]

open PowerSeries in
@[simp] lemma coeff_kSer (r : ℕ) : coeff r T.kSer = (-1) ^ r * T.nu r := by simp [kSer]

open PowerSeries in
@[simp] lemma coeff_lSer (r : ℕ) : coeff r T.lSer = (-1) ^ r * T.mu (r + 1) := by simp [lSer]

open PowerSeries in
/-- **`eq:h-ell`**: `h(z) + z ℓ(z) = 1`, from `N + zX²N = I`. -/
lemma hSer_add_X_mul_lSer : T.hSer + X * T.lSer = 1 := by
  ext m
  cases m with
  | zero =>
      have hc : constantCoeff T.hSer = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_hSer]
        simp [T.mu_zero]
      simp [hc]
  | succ r =>
      rw [map_add, coeff_hSer, coeff_succ_X_mul, coeff_lSer, PowerSeries.coeff_one, if_neg]
      · rw [pow_succ]; ring
      · exact Nat.succ_ne_zero r

open PowerSeries in
/-- **`eq:F-double`/`eq:def-beta`**: the series `F = h² + z k²` has coefficients
`(-1)^n β_n`. -/
lemma hSer_sq_add : T.hSer ^ 2 + X * T.kSer ^ 2 = betaSeries T.beta := by
  ext m
  have hmu : ∀ q : ℕ, coeff q (T.hSer ^ 2) = (-1) ^ q * ∑ p ∈ Finset.antidiagonal q,
      T.mu p.1 * T.mu p.2 := by
    intro q
    rw [sq, coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hq : p.1 + p.2 = q := Finset.mem_antidiagonal.mp hp
    rw [coeff_hSer, coeff_hSer, ← hq, pow_add]
    ring
  have hnu : ∀ q : ℕ, coeff q (T.kSer ^ 2) = (-1) ^ q * ∑ p ∈ Finset.antidiagonal q,
      T.nu p.1 * T.nu p.2 := by
    intro q
    rw [sq, coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hq : p.1 + p.2 = q := Finset.mem_antidiagonal.mp hp
    rw [coeff_kSer, coeff_kSer, ← hq, pow_add]
    ring
  cases m with
  | zero =>
      rw [map_add, hmu 0, coeff_betaSeries]
      simp [T.beta_zero, T.mu_zero]
  | succ r =>
      rw [map_add, hmu (r + 1), coeff_succ_X_mul, hnu r, coeff_betaSeries, T.beta_succ_conv r,
        pow_succ]
      ring

/-- The full monotone chain `1 = β₀ ≥ β₁ ≥ … ≥ 0` of `eq:beta-monotone`. -/
lemma beta_antitone : ∀ r, T.beta (r + 1) ≤ T.beta r := by
  intro r
  cases r with
  | zero =>
      rw [beta_zero]
      exact le_trans T.beta_one_le_tau T.tau_le_one
  | succ r =>
      have h1 := T.beta_le_tau_mul r
      have h2 : T.tau * T.beta (r + 1) ≤ 1 * T.beta (r + 1) :=
        mul_le_mul_of_nonneg_right T.tau_le_one (T.beta_nonneg _)
      rw [one_mul] at h2
      linarith

end Spectrum

end AlternatingCycle
