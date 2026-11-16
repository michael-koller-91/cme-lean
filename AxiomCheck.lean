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
