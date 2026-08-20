import AlternatingCycle.Compression.HSBound
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The Krylov compression and the finite matrix model

For a symmetric `T` on an inner product space, a vector
`g` and a cutoff `d`, compress `T` orthogonally to `V = span{g, Tg, …, T^d g}`.  Two things survive
the compression:

* the vector moments, `⟨g, C^j g⟩ = ⟨g, T^j g⟩` for `j ≤ d` — because `C^j g = T^j g` there;
* the Hilbert–Schmidt bound, since `C = Π ∘ T` on `V` and `Π` does not increase norms.

Diagonalising `C` (it is symmetric on a finite-dimensional space) turns this into the *matrix* data
that `matrix_main_general` wants, and the packaging is deliberately trivial: with `λ` the
eigenvalues, `b` the eigenbasis and `eᵢ = ⟨g, bᵢ⟩`,

```
  A := Matrix.diagonal λ,     Aᵀ = A,     e ⬝ᵥ e = ‖g‖²,
  ⟨e, Aʲ e⟩ = ⟨g, Cʲ g⟩,      Tr(A²) = ∑ λᵢ² = ∑ ‖C bᵢ‖² ≤ ∑ ‖T bᵢ‖².
```

Taking the cutoff `d := 2m` (rather than `m`) makes the moment matching hold for every `j ≤ 2m`
with no polarisation step; the larger subspace costs nothing.

-/

open MeasureTheory OddCycleBound OddCycleBound.Spectral.L2Kernel Finset Matrix
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace AlternatingCycle

/-! ### The compression of a symmetric operator to a Krylov space -/

section Krylov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `span {g, Tg, …, T^d g}`. -/
def krylov (T : E →L[ℝ] E) (g : E) (d : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun j : Fin (d + 1) => (T ^ (j : ℕ)) g)

instance krylov_finiteDimensional (T : E →L[ℝ] E) (g : E) (d : ℕ) :
    FiniteDimensional ℝ (krylov T g d) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- Every iterate up to the cutoff lies in the Krylov space. -/
lemma pow_mem_krylov (T : E →L[ℝ] E) (g : E) {d j : ℕ} (hj : j ≤ d) :
    (T ^ j) g ∈ krylov T g d :=
  Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩

/-- The starting vector, inside its Krylov space. -/
def krylovVec (T : E →L[ℝ] E) (g : E) (d : ℕ) : krylov T g d :=
  ⟨g, by simpa using pow_mem_krylov T g (Nat.zero_le d)⟩

@[simp] lemma krylovVec_coe (T : E →L[ℝ] E) (g : E) (d : ℕ) :
    (krylovVec T g d : E) = g := rfl

/-- The orthogonal compression `C = Π T` of `T` to its Krylov space. -/
def krylovComp (T : E →L[ℝ] E) (g : E) (d : ℕ) : krylov T g d →L[ℝ] krylov T g d :=
  (krylov T g d).orthogonalProjectionOnto.comp (T.comp (krylov T g d).subtypeL)

lemma krylovComp_apply (T : E →L[ℝ] E) (g : E) (d : ℕ) (v : krylov T g d) :
    krylovComp T g d v = (krylov T g d).orthogonalProjectionOnto (T (v : E)) := rfl

/-- Compression preserves symmetry. -/
theorem krylovComp_isSymmetric (T : E →L[ℝ] E) (g : E) (d : ℕ)
    (hT : (T : E →ₗ[ℝ] E).IsSymmetric) :
    ((krylovComp T g d : krylov T g d →L[ℝ] krylov T g d) :
      krylov T g d →ₗ[ℝ] krylov T g d).IsSymmetric := by
  intro x y
  show inner ℝ ((krylov T g d).orthogonalProjectionOnto (T (x : E))) y
      = inner ℝ x ((krylov T g d).orthogonalProjectionOnto (T (y : E)))
  rw [(krylov T g d).inner_orthogonalProjectionOnto_eq_of_mem_right,
    (krylov T g d).inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact hT x y

/-- Up to the cutoff, the compression reproduces the original iterates. -/
theorem pow_krylovComp (T : E →L[ℝ] E) (g : E) {d : ℕ} : ∀ {j : ℕ}, j ≤ d →
    ((krylovComp T g d ^ j) (krylovVec T g d) : E) = (T ^ j) g
  | 0, _ => by simp
  | j + 1, hj => by
      have hjd : j ≤ d := by omega
      have hstep : (krylovComp T g d ^ (j + 1)) (krylovVec T g d)
          = krylovComp T g d ((krylovComp T g d ^ j) (krylovVec T g d)) := by
        rw [pow_succ' (krylovComp T g d) j]; rfl
      have hmem : (T ^ (j + 1)) g ∈ krylov T g d := pow_mem_krylov T g hj
      rw [hstep, krylovComp_apply, pow_krylovComp T g hjd]
      have : T ((T ^ j) g) = (T ^ (j + 1)) g := by
        rw [pow_succ' T j]; rfl
      rw [this]
      exact congrArg _ ((krylov T g d).orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, hmem⟩)

/-- **Moment matching.**  The compression has the same vector moments at `g` up to the cutoff. -/
theorem inner_pow_krylovComp (T : E →L[ℝ] E) (g : E) {d j : ℕ} (hj : j ≤ d) :
    inner ℝ (krylovVec T g d) ((krylovComp T g d ^ j) (krylovVec T g d))
      = inner ℝ g ((T ^ j) g) := by
  show inner ℝ ((krylovVec T g d : E)) (((krylovComp T g d ^ j) (krylovVec T g d) : E))
      = inner ℝ g ((T ^ j) g)
  rw [krylovVec_coe, pow_krylovComp T g hj]

end Krylov

/-! ### Diagonalising a symmetric operator on a finite-dimensional space -/

section Diagonal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The eigenvalues of a symmetric operator, as a vector. -/
def atomEigen {C : F →ₗ[ℝ] F} (hC : C.IsSymmetric) : Fin (Module.finrank ℝ F) → ℝ :=
  hC.eigenvalues rfl

/-- The coordinates of `g` in the eigenbasis. -/
def atomCoord {C : F →ₗ[ℝ] F} (hC : C.IsSymmetric) (g : F) : Fin (Module.finrank ℝ F) → ℝ :=
  fun i => inner ℝ g (hC.eigenvectorBasis rfl i)

lemma inner_eigenvector_pow {C : F →ₗ[ℝ] F} (hC : C.IsSymmetric) (g : F) (i) : ∀ j : ℕ,
    inner ℝ (hC.eigenvectorBasis rfl i) ((C ^ j) g)
      = atomEigen hC i ^ j * inner ℝ (hC.eigenvectorBasis rfl i) g
  | 0 => by simp
  | j + 1 => by
      have heigen : C (hC.eigenvectorBasis rfl i) = atomEigen hC i • hC.eigenvectorBasis rfl i := by
        simp [atomEigen, hC.apply_eigenvectorBasis rfl i]
      have hstep : (C ^ (j + 1)) g = C ((C ^ j) g) := by rw [pow_succ' C j]; rfl
      rw [hstep, ← hC (hC.eigenvectorBasis rfl i) ((C ^ j) g), heigen, real_inner_smul_left,
        inner_eigenvector_pow hC g i j]
      ring

/-- The moments of a symmetric operator are the atomic moments of its eigenvalues. -/
theorem inner_pow_eq_sum {C : F →ₗ[ℝ] F} (hC : C.IsSymmetric) (g : F) (j : ℕ) :
    inner ℝ g ((C ^ j) g) = ∑ i, atomCoord hC g i ^ 2 * atomEigen hC i ^ j := by
  have hb := (hC.eigenvectorBasis (n := Module.finrank ℝ F) rfl).sum_inner_mul_inner g ((C ^ j) g)
  rw [← hb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvector_pow hC g i j, atomCoord, real_inner_comm (hC.eigenvectorBasis rfl i) g]
  ring

/-- The eigenbasis, viewed in the ambient space, is orthonormal. -/
lemma orthonormal_eigenvectorBasis {C : F →ₗ[ℝ] F} (hC : C.IsSymmetric) :
    Orthonormal ℝ (fun i => hC.eigenvectorBasis (n := Module.finrank ℝ F) rfl i) :=
  (hC.eigenvectorBasis rfl).orthonormal

end Diagonal

/-! ### The matrix model of a graphon -/

section Model

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ}

/-- The Krylov space of the signed operator at the constant function, with cutoff `2m`. -/
def kryV (hW : IsGraphon W μ) (m : ℕ) : Submodule ℝ (Lp ℝ 2 μ) :=
  krylov (opX hW) (oneL2 μ) (2 * m)

/-- The compression of `X` to it. -/
def kryC (hW : IsGraphon W μ) (m : ℕ) : kryV hW m →L[ℝ] kryV hW m :=
  krylovComp (opX hW) (oneL2 μ) (2 * m)

lemma kryC_isSymmetric (hW : IsGraphon W μ) (m : ℕ) :
    ((kryC hW m : kryV hW m →L[ℝ] kryV hW m) : kryV hW m →ₗ[ℝ] kryV hW m).IsSymmetric :=
  krylovComp_isSymmetric _ _ _ (opX_isSymmetric hW)

instance kryV_finiteDimensional (hW : IsGraphon W μ) (m : ℕ) :
    FiniteDimensional ℝ (kryV hW m) := by
  unfold kryV; infer_instance

/-- `‖1‖ = 1` in `L²` of a probability measure. -/
lemma norm_oneL2_sq_eq_one : ‖oneL2 (Omega := Ω) μ‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_oneL2_eq_integral,
    integral_congr_ae (oneL2_ae_eq_one (mu := μ))]
  simp

/-- Powers of a continuous linear map agree with powers of the underlying linear map. -/
lemma coeLinear_pow {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : F →L[ℝ] F) (v : F) : ∀ j : ℕ, ((T : F →ₗ[ℝ] F) ^ j) v = (T ^ j) v
  | 0 => rfl
  | j + 1 => by
      have h1 : ((T : F →ₗ[ℝ] F) ^ (j + 1)) v = (T : F →ₗ[ℝ] F) (((T : F →ₗ[ℝ] F) ^ j) v) := by
        rw [pow_succ' (T : F →ₗ[ℝ] F) j]; rfl
      have h2 : (T ^ (j + 1)) v = T ((T ^ j) v) := by rw [pow_succ' T j]; rfl
      rw [h1, h2, coeLinear_pow T v j]
      rfl

/-- **The matrix model.**  A symmetric matrix and a unit vector whose moments are the graphon
moments and whose Hilbert–Schmidt norm respects the bound. -/
theorem exists_matrix_model (hW : IsGraphon W μ) (m : ℕ) :
    ∃ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (e : Fin N → ℝ),
      Aᵀ = A ∧ e ⬝ᵥ e = 1 ∧ Matrix.trace (A * A) ≤ 1 ∧
        ∀ j ≤ 2 * m, e ⬝ᵥ (A ^ j *ᵥ e) = kMoment hW j := by
  classical
  have hCsymm := kryC_isSymmetric hW m
  set N := Module.finrank ℝ (kryV hW m) with hN
  set b := hCsymm.eigenvectorBasis (n := N) rfl with hb
  set lam : Fin N → ℝ := atomEigen hCsymm with hlam
  set g : kryV hW m := krylovVec (opX hW) (oneL2 μ) (2 * m) with hg
  set e : Fin N → ℝ := atomCoord hCsymm g with he
  -- the moments of the diagonal matrix are the moments of the compression
  have hmom : ∀ j : ℕ, e ⬝ᵥ (Matrix.diagonal lam ^ j *ᵥ e)
      = inner ℝ g (((kryC hW m : kryV hW m →ₗ[ℝ] kryV hW m) ^ j) g) := by
    intro j
    rw [inner_pow_eq_sum hCsymm g j, Matrix.diagonal_pow, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_diagonal]
    show e i * ((lam ^ j) i * e i) = e i ^ 2 * lam i ^ j
    simp only [Pi.pow_apply]
    ring
  refine ⟨N, Matrix.diagonal lam, e, Matrix.diagonal_transpose lam, ?_, ?_, ?_⟩
  · -- `∑ eᵢ² = ‖1‖² = 1`
    have h0 := hmom 0
    rw [pow_zero, Matrix.one_mulVec] at h0
    have hgg : inner ℝ g (((kryC hW m : kryV hW m →ₗ[ℝ] kryV hW m) ^ 0) g) = 1 := by
      show inner ℝ g g = 1
      rw [real_inner_self_eq_norm_sq]
      show ‖oneL2 (Omega := Ω) μ‖ ^ 2 = 1
      exact norm_oneL2_sq_eq_one
    rw [hgg] at h0
    exact h0
  · -- `Tr(A²) = ∑ λᵢ² ≤ 1`
    have hcoe : Orthonormal ℝ (fun i => ((b i : kryV hW m) : Lp ℝ 2 μ)) := by
      constructor
      · intro i; exact b.orthonormal.1 i
      · intro i j hij; exact b.orthonormal.2 hij
    have hstep : ∀ i, lam i ^ 2 ≤ ‖opX hW ((b i : kryV hW m) : Lp ℝ 2 μ)‖ ^ 2 := by
      intro i
      have heig : (kryC hW m) (b i) = lam i • b i := hCsymm.apply_eigenvectorBasis rfl i
      have hnorm : ‖(kryC hW m) (b i)‖ = |lam i| := by
        rw [heig, norm_smul, Real.norm_eq_abs, b.orthonormal.1 i, mul_one]
      have hle : ‖(kryC hW m) (b i)‖ ≤ ‖opX hW ((b i : kryV hW m) : Lp ℝ 2 μ)‖ :=
        (kryV hW m).norm_orthogonalProjectionOnto_apply_le
          (opX hW ((b i : kryV hW m) : Lp ℝ 2 μ))
      rw [hnorm] at hle
      nlinarith [abs_nonneg (lam i), hle, sq_abs (lam i)]
    have htr : Matrix.trace (Matrix.diagonal lam * Matrix.diagonal lam) = ∑ i, lam i ^ 2 := by
      simp [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, sq]
    rw [htr]
    calc ∑ i, lam i ^ 2 ≤ ∑ i, ‖opX hW ((b i : kryV hW m) : Lp ℝ 2 μ)‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hstep i
      _ ≤ 1 := sum_norm_opX_sq_le hW hcoe
  · -- the moments agree with `kMoment` up to the cutoff
    intro j hj
    rw [hmom j, coeLinear_pow (kryC hW m) g j]
    show inner ℝ (krylovVec (opX hW) (oneL2 μ) (2 * m))
        ((krylovComp (opX hW) (oneL2 μ) (2 * m) ^ j) (krylovVec (opX hW) (oneL2 μ) (2 * m)))
      = kMoment hW j
    rw [inner_pow_krylovComp (opX hW) (oneL2 μ) hj, inner_oneL2_opX_pow_oneL2 hW j]

end Model

end AlternatingCycle
