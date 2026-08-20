import AlternatingCycle.Matrix.Scalar.LogDeriv

/-!
# The odd logarithmic coefficient lemma

This is `lem:odd-log` of `alternating_cycles_schur_proof.tex`, the lemma that isolates the role
of the parity of `m`.

Given a nonincreasing sequence `β` with `β 0 = 1`, set

```
  F(z) = ∑ (-1)^n β_n z^n,     G(z) = ∑ d_n z^n,     d_n = β_n - β_{n+1} ≥ 0.
```

The two-line computation `eq:F-G`–`eq:factor-log`,

```
  (1+z) F(z) = 1 + z G(-z),        (1+z)(1 - z F(z)) = 1 - z² G(-z),
```

splits the series into a part with an explicitly known logarithm and a part whose
coefficients all carry the sign `(-1)^{m-2r}`.  For **odd** `m` that sign is negative, giving

```
  coeff m (Λ (1 - z F(z))) ≤ 1,
```

which is `eq:odd-log-bound` (recall `coeff m (Λ A) = m · [z^m](-log A)`).

Note what is *not* needed: nonnegativity of `β`.  Only `β 0 = 1` and monotonicity enter, the latter
solely through `0 ≤ d_n` — and these are exactly the hypotheses of `lem:odd-log` in the note.
-/

namespace AlternatingCycle

open PowerSeries Finset

noncomputable section

variable (β : ℕ → ℝ)

/-- `F(z) = ∑_{n≥0} (-1)^n β_n z^n`, the series `eq:F-beta`. -/
def betaSeries : ℝ⟦X⟧ := PowerSeries.mk fun n => (-1) ^ n * β n

/-- `G(z) = ∑_{n≥0} d_n z^n` with `d_n = β_n - β_{n+1}`, the successive-difference series. -/
def diffSeries : ℝ⟦X⟧ := PowerSeries.mk fun n => β n - β (n + 1)

@[simp] lemma coeff_betaSeries (n : ℕ) : coeff n (betaSeries β) = (-1) ^ n * β n := by
  simp [betaSeries]

@[simp] lemma coeff_diffSeries (n : ℕ) : coeff n (diffSeries β) = β n - β (n + 1) := by
  simp [diffSeries]

variable {β}

lemma coeff_diffSeries_nonneg (hanti : ∀ n, β (n + 1) ≤ β n) (n : ℕ) :
    0 ≤ coeff n (diffSeries β) := by
  rw [coeff_diffSeries]; linarith [hanti n]

/-- A power series with nonnegative coefficients has powers with nonnegative coefficients. -/
lemma coeff_pow_nonneg {P : ℝ⟦X⟧} (hP : ∀ n, 0 ≤ coeff n P) (s : ℕ) :
    ∀ j, 0 ≤ coeff j (P ^ s) := by
  induction s with
  | zero =>
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · rw [pow_zero, coeff_one, if_neg hj.ne']
  | succ s ih =>
      intro j
      rw [pow_succ, coeff_mul]
      exact Finset.sum_nonneg fun p _ => mul_nonneg (ih p.1) (hP p.2)

/-! ### The factorization `eq:F-G` -/

/-- `eq:F-G`: `(1+z) F(z) = 1 + z G(-z)`. -/
lemma one_add_X_mul_betaSeries (hβ0 : β 0 = 1) :
    (1 + X) * betaSeries β = 1 + X * rescale (-1) (diffSeries β) := by
  ext n
  cases n with
  | zero =>
      have hc : constantCoeff (betaSeries β) = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_betaSeries]
        simp [hβ0]
      simp [hc]
  | succ k =>
      rw [add_mul, one_mul, map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul,
        coeff_betaSeries, coeff_betaSeries, coeff_rescale, coeff_diffSeries]
      simp [pow_succ]
      ring

/-- `eq:factor-log`: `(1+z)(1 - z F(z)) = 1 - z² G(-z)`. -/
lemma one_add_X_mul_one_sub (hβ0 : β 0 = 1) :
    (1 + X) * (1 - X * betaSeries β) = 1 - X ^ 2 * rescale (-1) (diffSeries β) := by
  have h := one_add_X_mul_betaSeries hβ0
  linear_combination (-X : ℝ⟦X⟧) * h

/-! ### The sign of the powers of `z² G(−z)` -/

/-- For odd `m` every power of `H = z² G(-z)` has nonpositive `m`-th coefficient.  This is the one
place where the parity `m ≡ 1 (mod 2)` is used. -/
lemma coeff_diffSeries_pow_nonpos (hanti : ∀ n, β (n + 1) ≤ β n) {m : ℕ} (hm : Odd m) (s : ℕ) :
    coeff m ((X ^ 2 * rescale (-1) (diffSeries β)) ^ s) ≤ 0 := by
  have hGpow : ∀ j, 0 ≤ coeff j (diffSeries β ^ s) :=
    coeff_pow_nonneg (coeff_diffSeries_nonneg hanti) s
  have hsplit : (X ^ 2 * rescale (-1) (diffSeries β)) ^ s
      = X ^ (2 * s) * rescale (-1) (diffSeries β ^ s) := by
    rw [mul_pow, ← pow_mul, map_pow]
  rw [hsplit, coeff_X_pow_mul']
  split_ifs with hle
  · rw [coeff_rescale]
    have hodd : Odd (m - 2 * s) := by
      obtain ⟨k, hk⟩ := hm
      exact ⟨k - s, by omega⟩
    have : (-1 : ℝ) ^ (m - 2 * s) = -1 := hodd.neg_one_pow
    rw [this]
    have := hGpow (m - 2 * s)
    linarith
  · exact le_refl 0

/-! ### The lemma -/

/-- **`lem:odd-log`, `eq:odd-log-bound`.**  For odd `m`,
`coeff m (Λ (1 - z F(z))) ≤ 1`, i.e. `m [z^m](-log(1 - zF(z))) ≤ 1`. -/
theorem coeff_logDeriv_betaSeries_le_one (hβ0 : β 0 = 1) (hanti : ∀ n, β (n + 1) ≤ β n)
    {m : ℕ} (hm : Odd m) :
    coeff m (logDeriv (1 - X * betaSeries β)) ≤ 1 := by
  set H : ℝ⟦X⟧ := X ^ 2 * rescale (-1) (diffSeries β) with hH
  have hcc : constantCoeff H = 0 := by
    rw [hH]
    simp
  have hA : constantCoeff (1 - X * betaSeries β : ℝ⟦X⟧) = 1 := by simp
  have hone : constantCoeff (1 + X : ℝ⟦X⟧) = 1 := by simp
  have hfac : (1 + X) * (1 - X * betaSeries β) = 1 - H := one_add_X_mul_one_sub hβ0
  have hsplit : logDeriv (1 - H) = logDeriv (1 + X) + logDeriv (1 - X * betaSeries β) := by
    rw [← hfac, logDeriv_mul hone hA]
  have h1 : coeff m (logDeriv (1 + X : ℝ⟦X⟧)) = -1 := coeff_logDeriv_one_add_X hm
  have h2 : coeff m (logDeriv (1 - H)) ≤ 0 :=
    coeff_logDeriv_one_sub_nonpos hcc m fun s _ =>
      coeff_diffSeries_pow_nonpos hanti hm s
  have h3 : coeff m (logDeriv (1 - H))
      = coeff m (logDeriv (1 + X : ℝ⟦X⟧)) + coeff m (logDeriv (1 - X * betaSeries β)) := by
    rw [hsplit, map_add]
  rw [h3, h1] at h2
  linarith

end

end AlternatingCycle
