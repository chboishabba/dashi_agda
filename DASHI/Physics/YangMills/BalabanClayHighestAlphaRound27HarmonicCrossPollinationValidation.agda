module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound27HarmonicCrossPollinationValidation where

------------------------------------------------------------------------
-- Cumulative validation root.
--
-- Imports Round Twenty Six and checks the common ring-scale, filtered-estimate,
-- separating-probe and local-permutation modules plus their Yang--Mills
-- adapters.  No selected-background radius, W-local bound, terminal physical
-- coercivity, literal Combes--Thomas estimate, uniform RG inverse/coupling,
-- thermodynamic gap, OS reconstruction or Clay completion is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound26Validation
import DASHI.Physics.Common.FiniteRingScaleDualityExact
import DASHI.Physics.Common.ScaledFilteredEstimateExact
import DASHI.Physics.Common.SeparatingProbeFamilyExact
import DASHI.Physics.Common.FiniteWreathRefinementExact
import DASHI.Physics.YangMills.BalabanP33ScaledFilteredCrossPollinationExact
import DASHI.Physics.YangMills.BalabanP33WreathBlockSpinCrossPollinationExact

round27HarmonicCrossPollinationRoot : Set
round27HarmonicCrossPollinationRoot = ⊤

round27HarmonicCrossPollinationRootInhabited :
  round27HarmonicCrossPollinationRoot
round27HarmonicCrossPollinationRootInhabited = tt

round27HarmonicCrossPollinationRootStable :
  round27HarmonicCrossPollinationRoot ≡ ⊤
round27HarmonicCrossPollinationRootStable = refl
