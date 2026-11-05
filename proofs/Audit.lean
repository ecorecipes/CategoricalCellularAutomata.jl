import CategoricalCellularAutomataProofs

/-! Axiom audit for the default target. Every line should report at most `propext`,
`Classical.choice`, `Quot.sound`. -/

open CategoricalCellularAutomataProofs

-- Configurations.lean
#print axioms shift_one
#print axioms shift_shift
#print axioms pullback_id
#print axioms pullback_comp
#print axioms pullback_shift
-- CellularAutomata.lean
#print axioms ca_shift
#print axioms apply_eq_apply_one_shift
#print axioms eq_of_apply_one
#print axioms ca_eq_iff
#print axioms ca_id
#print axioms ca_comp
#print axioms ca_comp_shift
#print axioms ca_pair
-- Category.lean
#print axioms isCA_id
#print axioms isCA_comp
#print axioms IsCA.shift_comm
#print axioms prodIsLimit
#print axioms unitIsTerminal
#print axioms instCartesianMonoidalCategoryCAObj
-- CurtisHedlundLyndon.lean
#print axioms IsCA.exists_localAt
#print axioms isCA_iff_shift_comm_and_local
#print axioms isCA_iff_shift_comm
-- Linear.lean
#print axioms linCA_conv
#print axioms monoidAlgebra_mul_eq_conv
#print axioms linCA_mul
#print axioms linCA_one
#print axioms linCA_pow
#print axioms isCA_linCA
-- Generalized.lean
#print axioms gca_eq_pullback_ca
#print axioms gca_id
#print axioms pullback_ca
#print axioms gca_map_eq_ca_pullback
#print axioms gca_shift
#print axioms gca_comp
-- Gluing.lean
#print axioms gluedConfigEquiv
#print axioms gluedConfigEquiv_app
#print axioms exists_unique_glued_config
#print axioms glued_config_ext
#print axioms step_restrict
#print axioms step_local
#print axioms step_eq_of_cover
-- Spaces.lean
#print axioms SpaceMap.step_pullback
#print axioms SpaceMap.run_pullback
-- Models.lean
#print axioms ModelMap.step_map
#print axioms ModelMap.run_map
#print axioms instCategoryCAModel
#print axioms SpaceMap.pullFunctor
