import Grain.Main
import Grain.ParityMatching
import Grain.ScalarCertificate
import Grain.PhononGround
import Grain.PairingExample
import Grain.PairingMaterialExample
import Grain.PairingFullExample
import Grain.PairingParent
import Grain.PairingBandMesh
import Grain.PairingProjection
import Grain.MgB2
import Grain.CrystalBCSExample
import Grain.CooperFluctuation
import Grain.CooperBenchmark
import Grain.EFTBounds
import Grain.HarmonicBandExample
import Grain.DFPTFive
import Grain.DFPTSevenContrast
import Grain.HubbardBenchmark
import Grain.HubbardOperators

#print axioms Grain.RankOne.shifted_form
#print axioms Grain.RankOne.enclosure
#print axioms Grain.effective_bounds
#print axioms Grain.secondOrder_error
#print axioms Grain.prediction_window
#print axioms Grain.prediction_decimal_enclosure
#print axioms Grain.reference_control
#print axioms Grain.ParityCancellation.secondOrder_parity
#print axioms Grain.ParityCancellation.contrast_center_from_hops
#print axioms Grain.ParityMatching.symmetric_hop_parity
#print axioms Grain.ParityMatching.matches_parity_iff
#print axioms Grain.ParityMatching.two_shell_shift
#print axioms Grain.ParityMatching.reciprocalCoupling_eq
#print axioms Grain.ParityMatching.reciprocal_remainder
#print axioms Grain.ParityMatching.benchmark_mixed_zero
#print axioms Grain.ParityMatching.benchmark_legal_endpoints
#print axioms Grain.ParityMatching.benchmark_loop_parity
#print axioms Grain.ParityMatching.benchmark_cubic_mixed
#print axioms Grain.ParityMatching.cubic_coefficient_match_iff
#print axioms Grain.ParityMatching.cubic_match_remainder
#print axioms Grain.ResolventRemainder.normalize_eigenvector
#print axioms Grain.ResolventRemainder.sector_remainder
#print axioms Grain.ResolventRemainder.eigenvalue_remainder
#print axioms Grain.ResolventRemainder.parity_error
#print axioms Grain.ResolventRemainder.cubic_loop_expansion
#print axioms Grain.ParityMatching.benchmark_analytic_error
#print axioms Grain.ParityMatching.benchmark_reduced_error
#print axioms Grain.ParityMatching.benchmark_sharp_error
#print axioms Grain.ParityMatching.benchmark_scalar_error
#print axioms Grain.full_model_window
#print axioms Grain.verified_five_orbital_eft
#print axioms Grain.verified_shell_dependent_pairing

#print axioms Grain.schur_compose
#print axioms Grain.TwoShell.exact_shell_composition
#print axioms Grain.TwoShell.exact_shell_eigenvalue
#print axioms Grain.TwoShell.parity_ground_in_window

#print axioms Grain.TwoShell.Prediction.sector_error
#print axioms Grain.TwoShell.Prediction.verified_two_shell_approximation

#print axioms Grain.TwoShell.FullSolve.sector_bounds
#print axioms Grain.TwoShell.FullSolve.full_solve_matches_frozen_prediction

#print axioms Grain.Phonon.generated_pair_transfer
#print axioms Grain.Phonon.one_quantum_response
#print axioms Grain.Phonon.frozen_harmonic_bounds
#print axioms Grain.Phonon.microscopic_contrast_positive
#print axioms Grain.Phonon.microscopic_sector_comparison
#print axioms Grain.Phonon.verified_phonon_comparison

#print axioms Grain.Pairing.gap_equation
#print axioms Grain.Pairing.eigenvalue_bounds
#print axioms Grain.Pairing.Certificate.crossing_endpoints

#print axioms Grain.Pairing.Material.weight_enclosure
#print axioms Grain.Pairing.Material.kernel_enclosure
#print axioms Grain.Pairing.Material.metric_enclosure
#print axioms Grain.Pairing.Material.material_spectrum_enclosure
#print axioms Grain.Pairing.Material.spectrum_eigenvector
#print axioms Grain.Pairing.Material.Certificate.has_realization
#print axioms Grain.Pairing.Material.Certificate.pairing_instability
#print axioms Grain.Pairing.Material.harmonic_fourier_integral
#print axioms Grain.Pairing.Material.parent_phonon
#print axioms Grain.Pairing.Material.normal_band_error
#print axioms Grain.Pairing.Material.band_mesh_partition
#print axioms Grain.Pairing.Material.band_mesh_realization
#print axioms Grain.Pairing.Material.fullMetric_error
#print axioms Grain.Pairing.Material.all_frequency_enclosure
#print axioms Grain.Pairing.Material.all_frequency_continuous
#print axioms Grain.Pairing.Material.AllFrequencyCertificate.crossing
#print axioms Grain.Pairing.Material.AllFrequencyCertificate.midpoint_crossing
#print axioms Grain.Pairing.Material.crossing_of_threshold_budget
#print axioms Grain.Pairing.Attribution.phonon_zero
#print axioms Grain.Pairing.Attribution.static_mode_from_derivative
#print axioms Grain.Pairing.Attribution.MgB2.sensitivity_box
#print axioms Grain.Pairing.Attribution.MgB2.sigma_dominates_two_band
#print axioms Grain.Pairing.Attribution.MgB2.sigma_dominates_four_sheet
#print axioms Grain.Pairing.Attribution.MgB2.grouping_full_error
#print axioms Grain.Pairing.Attribution.MgB2.a_point_e2g_dominates
#print axioms Grain.Pairing.Attribution.MgB2.a_point_xray_compatible

#print axioms Grain.CrystalBCS.static_coefficients
#print axioms Grain.CrystalBCS.complete_band_basis
#print axioms Grain.CrystalBCS.projected_cooper
#print axioms Grain.BCS.thermal_bdg_entry
#print axioms Grain.BCS.subcritical
#print axioms Grain.BCS.thermal_ratio_decreases
#print axioms Grain.CrystalBCS.Certificate.band_basis
#print axioms Grain.CrystalBCS.Certificate.critical_eigenvalue
#print axioms Grain.CrystalBCS.Certificate.thermal_gap_threshold
#print axioms Grain.CrystalBCS.Certificate.zero_temperature_gap
#print axioms Grain.CrystalBCS.Certificate.at0_gap
#print axioms Grain.CrystalBCS.Certificate.at1_no_gap

#print axioms Grain.BCS.mean_field_derivative
#print axioms Grain.BCS.thermal_minimum_iff
#print axioms Grain.BCS.ground_minimum_iff
#print axioms Grain.CrystalBCS.thermal_gap_of_minimum
#print axioms Grain.Cooper.restore_square
#print axioms Grain.Cooper.zero_source_pairing
#print axioms Grain.Cooper.free_energy_analytic
#print axioms Grain.Cooper.fluctuation_cost
#print axioms Grain.Cooper.fluctuation_response_of_forms
#print axioms Grain.CrystalBCS.Certificate.mean_field_transition
#print axioms Grain.CrystalBCS.Certificate.mean_field_ground_minimum
#print axioms Grain.CrystalBCS.Certificate.cooper_free_energy_analytic
#print axioms Grain.CrystalBCS.Certificate.cooper_inputs
#print axioms Grain.CrystalBCS.Certificate.cooper_response_eq
#print axioms Grain.CrystalBCS.Certificate.cooper_pair_response
#print axioms Grain.CrystalBCS.Certificate.mean_field_response_excess
#print axioms Grain.CrystalBCS.Certificate.fluctuation_cost_change

#print axioms Grain.EFT.lifted_enclosure
#print axioms Grain.EFT.frobenius_residual
#print axioms Grain.EFT.pairing_square
#print axioms Grain.EFT.pairing_response_error
#print axioms Grain.EFT.channel_response_enclosure
#print axioms Grain.EFT.channel_response_of_energy_shifts
#print axioms Grain.EFT.channel_response_relative_budget
#print axioms Grain.HubbardChannels.cooper_only_excess
#print axioms Grain.EFT.discarded_partition_ratio
#print axioms Grain.EFT.discarded_partition_ratio_enclosure
#print axioms Grain.EFT.dfpt_induced_coefficient
#print axioms Grain.EFT.mode_lower
#print axioms Grain.EFT.mode_dressed_upper
#print axioms Grain.EFT.contrast_enclosure
#print axioms Grain.EFT.free_energy_enclosure
#print axioms Grain.EFT.four_site_response_enclosure

#print axioms Grain.HarmonicBand.electronic_symmetric
#print axioms Grain.HarmonicBand.electronPhonon_symmetric
#print axioms Grain.HarmonicBand.instantaneous_from_square
#print axioms Grain.HarmonicBand.instantaneous_form
#print axioms Grain.HarmonicBand.occupation_box_covers
#print axioms Grain.HarmonicBand.Export.input_valid
#print axioms Grain.HarmonicBand.Export.certified_harmonic_lower
#print axioms Grain.HarmonicBand.sector_certificate
#print axioms Grain.HarmonicBand.DFPTFive.electronic_prediction
#print axioms Grain.HarmonicBand.DFPTFive.electronic_validation
#print axioms Grain.HarmonicBand.DFPTFive.harmonic_prediction
#print axioms Grain.HarmonicBand.DFPTSeven.electronic_validation
#print axioms Grain.HarmonicBand.DFPTSeven.harmonic_prediction

#print axioms Grain.HubbardChannels.site_vertex_fourier
#print axioms Grain.HubbardChannels.scattering_blocked
#print axioms Grain.HubbardChannels.scatter_preserves_sector
#print axioms Grain.HubbardChannels.source_preserves_sector
#print axioms Grain.HubbardChannels.retained_sector_size
#print axioms Grain.HubbardChannels.scatter_survives_elimination
#print axioms Grain.HubbardChannels.benchmark_bounds
#print axioms Grain.HubbardChannels.applicable_iff
#print axioms Grain.HubbardChannels.inapplicable_iff
#print axioms Grain.HubbardChannels.density_dominance
#print axioms Grain.HubbardChannels.filled_probability_comparison
#print axioms Grain.HubbardChannels.pair_removal_resolvent
