import AlternatingCycle.Necklace.RankOne

/-!
# Fact A: the signed necklace identity

Take the normal form of `Necklace/RankOne.lean` and apply a cyclic linear functional `τ`.  Every monomial `k ^ a * j * k ^ b` collapses to the single number
`μ (a + b)`, because

```
  τ (k ^ a * j * k ^ b) = τ (j * k ^ (b + a)) = μ (a + b),
```

so that

```
  τ (word ε j k n) = alphaC ε n * τ (k ^ n) + ∑_{a,b} coeff ε μ n a b * μ (a + b).
```

The right-hand side involves no algebra element at all: it is a universal expression in the sign
pattern `ε` and the numbers `μ`.  Instantiating `(𝒜, τ, j, k, μ)` twice — at matrices with `μ j =
⟨e, Aʲ e⟩`, and at kernels with `μ j = ` the path density — therefore produces the *same* number on
the two sides, which is exactly Fact A.

The alternating specialization `alt` uses `ε i = (−1)^i`:

```
  τ (((j + k) * (j − k)) ^ m) + (−1)^(m+1) * τ (k ^ (2m)) = ∑_{a,b} coeff alt μ (2m) a b * μ (a + b),
```

and for odd `m` the sign `(−1)^(m+1)` is `+1`, so the left side is exactly the quantity bounded by
`matrix_main_general`.
-/

namespace AlternatingCycle.RankOne

open Finset

variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℝ 𝒜]

section Trace

variable (ε μ : ℕ → ℝ) (j k : 𝒜) (τ : 𝒜 →ₗ[ℝ] ℝ)

/-- A monomial of the normal form carries no more information than the total degree `a + b`. -/
lemma tau_term (hcyc : ∀ x y : 𝒜, τ (x * y) = τ (y * x))
    (hτj : ∀ g : ℕ, τ (j * k ^ g) = μ g) (a b : ℕ) :
    τ (k ^ a * j * k ^ b) = μ (a + b) := by
  rw [mul_assoc, hcyc (k ^ a) (j * k ^ b), mul_assoc, ← pow_add, hτj, Nat.add_comm]

/-- **Fact A, abstract form.**  The trace of a signed word is a universal expression in the sign
pattern and the moments. -/
theorem tau_word (hjk : ∀ b : ℕ, j * k ^ b * j = μ b • j)
    (hcyc : ∀ x y : 𝒜, τ (x * y) = τ (y * x)) (hτj : ∀ g : ℕ, τ (j * k ^ g) = μ g) (n : ℕ) :
    τ (word ε j k n)
      = alphaC ε n * τ (k ^ n)
        + ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), coeff ε μ n a b * μ (a + b) := by
  rw [word_eq ε μ j k hjk n, map_add, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun b _ => by
    rw [map_smul, tau_term μ j k τ hcyc hτj a b, smul_eq_mul]

end Trace

/-- The alternating sign pattern `+, −, +, −, …` of `(P + A)(P − A)`. -/
def alt (i : ℕ) : ℝ := (-1) ^ i

/-- A period-two coefficient pattern with values `a, -b, a, -b, ...`. -/
def colorPattern (a b : ℝ) (i : ℕ) : ℝ := if Even i then a else -b

@[simp] lemma colorPattern_two_mul (a b : ℝ) (m : ℕ) :
    colorPattern a b (2 * m) = a := by
  simp [colorPattern]

@[simp] lemma colorPattern_two_mul_succ (a b : ℝ) (m : ℕ) :
    colorPattern a b (2 * m + 1) = -b := by
  simp [colorPattern]

/-- An even period-two word is a power of its two consecutive factors. -/
lemma word_colorPattern (a b : ℝ) (j k : 𝒜) : ∀ m : ℕ,
    word (colorPattern a b) j k (2 * m) = ((j + a • k) * (j - b • k)) ^ m
  | 0 => by simp
  | m + 1 => by
      have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [h, word_succ, word_succ, word_colorPattern a b j k m,
        colorPattern_two_mul, colorPattern_two_mul_succ, pow_succ]
      simp only [neg_smul, sub_eq_add_neg, mul_assoc]

/-- The pure-power coefficient of an even period-two word is `(-a*b)^m`. -/
lemma alphaC_colorPattern (a b : ℝ) : ∀ m : ℕ,
    alphaC (colorPattern a b) (2 * m) = (-(a * b)) ^ m
  | 0 => rfl
  | m + 1 => by
      have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [h, alphaC_succ, alphaC_succ, alphaC_colorPattern a b m,
        colorPattern_two_mul, colorPattern_two_mul_succ, pow_succ]
      ring

/-- For `a*b=1` and odd length parameter, the period-two trace and the pure even moment add to
the universal rank-one moment expression. -/
theorem tau_colorPattern_add (a b : ℝ) (μ : ℕ → ℝ) (j k : 𝒜) (τ : 𝒜 →ₗ[ℝ] ℝ)
    (hjk : ∀ g : ℕ, j * k ^ g * j = μ g • j)
    (hcyc : ∀ x y : 𝒜, τ (x * y) = τ (y * x)) (hτj : ∀ g : ℕ, τ (j * k ^ g) = μ g)
    (hab : a * b = 1) {m : ℕ} (hm : Odd m) :
    τ (((j + a • k) * (j - b • k)) ^ m) + τ (k ^ (2 * m))
      = ∑ x ∈ range (2 * m + 1), ∑ y ∈ range (2 * m + 1),
          coeff (colorPattern a b) μ (2 * m) x y * μ (x + y) := by
  rw [← word_colorPattern a b j k m,
    tau_word (colorPattern a b) μ j k τ hjk hcyc hτj (2 * m),
    alphaC_colorPattern a b m, hab, hm.neg_one_pow]
  ring

@[simp] lemma alt_two_mul (m : ℕ) : alt (2 * m) = 1 := by
  rw [alt, pow_mul]; norm_num

@[simp] lemma alt_two_mul_succ (m : ℕ) : alt (2 * m + 1) = -1 := by
  rw [alt, pow_succ, pow_mul]; norm_num

/-- The alternating word of even length is the `m`-th power of `(j + k) * (j − k)`. -/
lemma word_alt (j k : 𝒜) : ∀ m : ℕ, word alt j k (2 * m) = ((j + k) * (j - k)) ^ m
  | 0 => by simp
  | m + 1 => by
      have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [h, word_succ, word_succ, word_alt j k m, alt_two_mul, alt_two_mul_succ, one_smul,
        neg_one_smul, ← sub_eq_add_neg, pow_succ, mul_assoc]

/-- The pure-power coefficient of the alternating word is `(−1)^m`. -/
lemma alphaC_alt : ∀ m : ℕ, alphaC alt (2 * m) = (-1) ^ m
  | 0 => rfl
  | m + 1 => by
      have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [h, alphaC_succ, alphaC_succ, alphaC_alt m, alt_two_mul, alt_two_mul_succ, pow_succ]
      ring

/-- **Fact A for the alternating pattern**: the identity
`4^m Alt_{2m}(W) + t(C_{2m}, K) = N_m(ε; μ)`, before either instantiation. -/
theorem tau_alt (μ : ℕ → ℝ) (j k : 𝒜) (τ : 𝒜 →ₗ[ℝ] ℝ)
    (hjk : ∀ b : ℕ, j * k ^ b * j = μ b • j)
    (hcyc : ∀ x y : 𝒜, τ (x * y) = τ (y * x)) (hτj : ∀ g : ℕ, τ (j * k ^ g) = μ g) (m : ℕ) :
    τ (((j + k) * (j - k)) ^ m)
      = (-1) ^ m * τ (k ^ (2 * m))
        + ∑ a ∈ range (2 * m + 1), ∑ b ∈ range (2 * m + 1),
            coeff alt μ (2 * m) a b * μ (a + b) := by
  rw [← word_alt j k m, tau_word alt μ j k τ hjk hcyc hτj (2 * m), alphaC_alt m]

/-- The form used at the end: for **odd** `m` the two trace terms appear with the same sign, so
their sum is the universal expression `N_m`. -/
theorem tau_alt_add (μ : ℕ → ℝ) (j k : 𝒜) (τ : 𝒜 →ₗ[ℝ] ℝ)
    (hjk : ∀ b : ℕ, j * k ^ b * j = μ b • j)
    (hcyc : ∀ x y : 𝒜, τ (x * y) = τ (y * x)) (hτj : ∀ g : ℕ, τ (j * k ^ g) = μ g)
    {m : ℕ} (hm : Odd m) :
    τ (((j + k) * (j - k)) ^ m) + τ (k ^ (2 * m))
      = ∑ a ∈ range (2 * m + 1), ∑ b ∈ range (2 * m + 1),
          coeff alt μ (2 * m) a b * μ (a + b) := by
  rw [tau_alt μ j k τ hjk hcyc hτj m, hm.neg_one_pow]
  ring

end AlternatingCycle.RankOne
