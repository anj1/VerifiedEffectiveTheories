import Grain.Main
import Grain.PhononGround
import Grain.PairingExample
import Grain.PairingMaterialExample
import Grain.CrystalBCSExample
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

#print axioms Grain.EFT.lifted_enclosure
#print axioms Grain.EFT.frobenius_residual
#print axioms Grain.EFT.pairing_square
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
#print axioms Grain.HarmonicBand.DFPTFive.electronic_validation
#print axioms Grain.HarmonicBand.DFPTFive.harmonic_prediction
#print axioms Grain.HarmonicBand.DFPTSeven.electronic_validation
#print axioms Grain.HarmonicBand.DFPTSeven.harmonic_prediction

#print axioms Grain.HubbardChannels.site_vertex_fourier
#print axioms Grain.HubbardChannels.scattering_blocked
#print axioms Grain.HubbardChannels.benchmark_bounds
#print axioms Grain.HubbardChannels.applicable_iff
#print axioms Grain.HubbardChannels.inapplicable_iff
#print axioms Grain.HubbardChannels.density_dominance
#print axioms Grain.HubbardChannels.filled_probability_comparison
#print axioms Grain.HubbardChannels.pair_removal_resolvent
