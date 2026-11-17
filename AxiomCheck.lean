module

import Main
import ApproximationByGMM

/--
info: 'main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms main_theorem

/--
info: 'cme_uniform_balls_R' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cme_uniform_balls_R

/--
info: 'cme_convergence_of_gmm_prior' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cme_convergence_of_gmm_prior

/--
info: 'isPdf_gaussSmoothed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isPdf_gaussSmoothed

/--
info: 'weighted_modulus_tendsto_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms weighted_modulus_tendsto_seq

/--
info: 'weighted_smoothing_tendsto_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms weighted_smoothing_tendsto_seq
