module DASHI.Physics.YangMills.YMClayUrsellTransferMixingBoundaryValidation where

open import Agda.Builtin.Equality using (_≡_)

-- RED-first guard: observable-pair Ursell decay must not be promoted to a
-- state-uniform transfer/mixing theorem without an explicit upgrade theorem.
import DASHI.Physics.YangMills.YMClayUrsellTransferMixingBoundaryExact as Boundary

open Boundary

pairwiseUrsellIsNotUniformMixing :
  pairwiseObservableUrsellDecayPaysUniformL2Mixing ≡ false
pairwiseUrsellIsNotUniformMixing =
  pairwiseObservableUrsellDecayPaysUniformL2MixingIsFalse

physicalTreeGraphMajorantStillRequired :
  physicalUrsellTreeGraphMajorantStillConditional ≡ true
physicalTreeGraphMajorantStillRequired =
  physicalUrsellTreeGraphMajorantStillConditionalIsTrue

explicitUpgradeTheoremRequired :
  observableToUniformMixingUpgradeStillRequired ≡ true
explicitUpgradeTheoremRequired =
  observableToUniformMixingUpgradeStillRequiredIsTrue
