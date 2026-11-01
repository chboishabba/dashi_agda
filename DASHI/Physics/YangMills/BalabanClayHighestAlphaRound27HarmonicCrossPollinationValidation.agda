module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound27HarmonicCrossPollinationValidation where

------------------------------------------------------------------------
-- Cumulative validation root.
--
-- Imports Round Twenty Six and checks the common ring-scale, filtered-estimate,
-- separating-probe, local-permutation and finite three-cycle-torus modules plus
-- their Yang--Mills adapters, including a literal four-diagonal/twelve-ordered
-- Wilson placement audit.  No selected-background radius, signed W-local
-- bound, terminal physical coercivity, literal Combes--Thomas estimate,
-- uniform RG inverse/coupling, thermodynamic gap, OS reconstruction or Clay
-- completion is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound26Validation
import DASHI.Physics.Common.FiniteRingScaleDualityExact
import DASHI.Physics.Common.ScaledFilteredEstimateExact
import DASHI.Physics.Common.SeparatingProbeFamilyExact
import DASHI.Physics.Common.FiniteWreathRefinementExact
import DASHI.Physics.Common.FiniteThreeCycleTorusExact
import DASHI.Physics.YangMills.BalabanP33WilsonSixteenPlacementSeparatingProbeExact
import DASHI.Physics.YangMills.BalabanP33ScaledFilteredCrossPollinationExact
import DASHI.Physics.YangMills.BalabanP33WreathBlockSpinCrossPollinationExact
import DASHI.Physics.YangMills.BalabanP33ThreeCycleBlockTorusCrossPollinationExact

round27HarmonicCrossPollinationRoot : Set
round27HarmonicCrossPollinationRoot = ⊤

round27HarmonicCrossPollinationRootInhabited :
  round27HarmonicCrossPollinationRoot
round27HarmonicCrossPollinationRootInhabited = tt

round27HarmonicCrossPollinationRootStable :
  round27HarmonicCrossPollinationRoot ≡ ⊤
round27HarmonicCrossPollinationRootStable = refl
