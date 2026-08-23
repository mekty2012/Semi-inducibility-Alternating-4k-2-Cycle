import AlternatingCycle

open AlternatingCycle

/-!
Axiom audit.  Every theorem below must depend only on `propext`, `Classical.choice`, `Quot.sound`.
Run with `lake env lean CheckAxioms.lean`.
-/

-- ## The theorem
#print axioms AlternatingCycle.alt_add_cycle_le_one
#print axioms AlternatingCycle.altDensity_le
#print axioms AlternatingCycle.alt_add_cycle_le_one_integral
#print axioms AlternatingCycle.half_sharp
#print axioms AlternatingCycle.half_alt
#print axioms AlternatingCycle.signedCycleDensity_nonneg

-- ## Fact A: the rank-one normal form, and its two instantiations
#print axioms AlternatingCycle.RankOne.word_eq
#print axioms AlternatingCycle.RankOne.tau_word
#print axioms AlternatingCycle.RankOne.tau_alt_add
#print axioms AlternatingCycle.trace_alt_matrix
#print axioms AlternatingCycle.necklace_le_one
#print axioms AlternatingCycle.KAlg.j_mul_mul_j
#print axioms AlternatingCycle.KAlg.tau_j_mul
#print axioms AlternatingCycle.KAlg.tau_mul_comm
#print axioms AlternatingCycle.alt_add_cycle_eq_necklace
#print axioms AlternatingCycle.centralDensity_iff_interval
#print axioms AlternatingCycle.RankOne.word_colorPattern
#print axioms AlternatingCycle.RankOne.tau_colorPattern_add
#print axioms AlternatingCycle.normalized_alt_add_centeredCycle_eq_necklace

-- ## Fact B: the L² operator, the Hilbert–Schmidt bound, the matrix model
#print axioms AlternatingCycle.opX_isSymmetric
#print axioms AlternatingCycle.centeredOp_isSymmetric
#print axioms AlternatingCycle.coeFn_centeredOp
#print axioms AlternatingCycle.inner_oneL2_centeredOp_oneL2
#print axioms AlternatingCycle.kernelSqNorm_centered_le
#print axioms AlternatingCycle.kernelSqNorm_normalizedCentered_le_one
#print axioms AlternatingCycle.sum_norm_centeredOp_sq_le
#print axioms AlternatingCycle.inner_oneL2_centeredOp_pow_oneL2
#print axioms AlternatingCycle.exists_fixedDensity_spectrum_mean_zero
#print axioms AlternatingCycle.density_cubic_head_le_one
#print axioms AlternatingCycle.exists_fixedDensity_spectrum_cubic
#print axioms AlternatingCycle.coeFn_opX
#print axioms AlternatingCycle.inner_oneL2_opX_pow_oneL2
#print axioms AlternatingCycle.sum_norm_opX_sq_le
#print axioms AlternatingCycle.exists_matrix_model

-- ## The finite-dimensional engine
#print axioms AlternatingCycle.cn_nonneg
#print axioms AlternatingCycle.cn_recurrence
#print axioms AlternatingCycle.coeff_logDeriv_betaSeries_le_one
#print axioms AlternatingCycle.trace_resolvent
#print axioms AlternatingCycle.resolvent_sq
#print axioms AlternatingCycle.det_mul_trace_sub
#print axioms AlternatingCycle.trace_adjugate_mul_matDeriv
#print axioms AlternatingCycle.trace_sub_eq_logDeriv
#print axioms AlternatingCycle.Model.traceSeries_sub
#print axioms AlternatingCycle.Model.density_traceSeries_sub
#print axioms AlternatingCycle.Spectrum.beta_one_le_tau
#print axioms AlternatingCycle.Spectrum.beta_antitone
#print axioms AlternatingCycle.det_M2
#print axioms AlternatingCycle.Spectrum.det_densityM2
#print axioms AlternatingCycle.Spectrum.densityBeta_series
#print axioms AlternatingCycle.Spectrum.densityBeta_nonneg
#print axioms AlternatingCycle.Spectrum.densityBeta_antitone
#print axioms AlternatingCycle.Spectrum.matrix_fixedDensity_diagonal
#print axioms AlternatingCycle.matrix_main
#print axioms AlternatingCycle.matrix_main_general

-- ## Fixed-density theorem
#print axioms AlternatingCycle.fixedDensity_normalized_le_one
#print axioms AlternatingCycle.fixedDensity_alt_add_centeredCycle_le
#print axioms AlternatingCycle.fixedDensity_alt_le
#print axioms AlternatingCycle.fixedDensity_alt_add_centeredCycle_le_integral
#print axioms AlternatingCycle.fixedDensity_alt_le_integral
#print axioms AlternatingCycle.constant_fixedDensity_sharp

-- ## Traces as integrals
#print axioms AlternatingCycle.trace_compList_eq_cycleIntegral
#print axioms AlternatingCycle.signedCycleDensity_eq_integral
#print axioms AlternatingCycle.altDensity_eq_integral
