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
