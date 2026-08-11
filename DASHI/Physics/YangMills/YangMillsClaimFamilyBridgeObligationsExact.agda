module DASHI.Physics.YangMills.YangMillsClaimFamilyBridgeObligationsExact where

------------------------------------------------------------------------
-- Each adversarial source receives a complete typed bridge list.  The list is
-- an audit target, not evidence that any bridge has been proved.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)

import DASHI.Physics.YangMills.YangMillsPaperClaimAuditCarrierExact as Audit
import DASHI.Physics.YangMills.YangMillsAdversarialClaimAtlasExact as Atlas

sourceBridges : Atlas.ClaimSource → List Audit.BridgeObligation
sourceBridges Atlas.nielsenSemitaTopological =
  Audit.sameTheoryEquivalence
  ∷ Audit.sameOperatorIntertwining
  ∷ Audit.measureConstructionAndPositivity
  ∷ Audit.reflectionPositivity
  ∷ Audit.continuumCutoffRemoval
  ∷ Audit.physicalGapScaleCompatibility
  ∷ Audit.allCompactSimpleGroupCoverage
  ∷ []
sourceBridges Atlas.toupinCelestialHaar =
  Audit.sameTheoryEquivalence
  ∷ Audit.sameOperatorIntertwining
  ∷ Audit.measureConstructionAndPositivity
  ∷ Audit.reflectionPositivity
  ∷ Audit.continuumCutoffRemoval
  ∷ Audit.physicalGapScaleCompatibility
  ∷ Audit.localOperatorAndOPEConstruction
  ∷ Audit.allCompactSimpleGroupCoverage
  ∷ []
sourceBridges Atlas.rietzUIDTScalar =
  Audit.sameTheoryEquivalence
  ∷ Audit.noCircularGapInput
  ∷ Audit.reflectionPositivity
  ∷ Audit.continuumCutoffRemoval
  ∷ Audit.physicalGapScaleCompatibility
  ∷ Audit.allCompactSimpleGroupCoverage
  ∷ []
sourceBridges Atlas.jacobsenFiveDimensionalOrbifold =
  Audit.sameTheoryEquivalence
  ∷ Audit.reflectionPositivity
  ∷ Audit.continuumCutoffRemoval
  ∷ Audit.sameOperatorIntertwining
  ∷ Audit.physicalGapScaleCompatibility
  ∷ Audit.gaugeSliceOrQuotientControl
  ∷ Audit.localOperatorAndOPEConstruction
  ∷ Audit.allCompactSimpleGroupCoverage
  ∷ []
sourceBridges Atlas.agawaNonlocalHolonomy =
  Audit.sameTheoryEquivalence
  ∷ Audit.measureConstructionAndPositivity
  ∷ Audit.gaugeSliceOrQuotientControl
  ∷ Audit.reflectionPositivity
  ∷ Audit.continuumCutoffRemoval
  ∷ Audit.physicalGapScaleCompatibility
  ∷ Audit.allCompactSimpleGroupCoverage
  ∷ []
sourceBridges Atlas.agawaRetractedAddendum =
  Audit.sameTheoryEquivalence
  ∷ Audit.gaugeSliceOrQuotientControl
  ∷ Audit.continuumCutoffRemoval
  ∷ Audit.physicalGapScaleCompatibility
  ∷ Audit.allCompactSimpleGroupCoverage
  ∷ []
sourceBridges Atlas.katayamaContinuumLSI =
  Audit.measureConstructionAndPositivity
  ∷ Audit.reflectionPositivity
  ∷ Audit.sameOperatorIntertwining
  ∷ Audit.noCircularGapInput
  ∷ Audit.continuumCutoffRemoval
  ∷ Audit.physicalGapScaleCompatibility
  ∷ Audit.allCompactSimpleGroupCoverage
  ∷ []
sourceBridges Atlas.randolphCascadeTransfer =
  Audit.sameTheoryEquivalence
  ∷ Audit.sameOperatorIntertwining
  ∷ Audit.noCircularGapInput
  ∷ Audit.continuumCutoffRemoval
  ∷ Audit.physicalGapScaleCompatibility
  ∷ Audit.allCompactSimpleGroupCoverage
  ∷ []
sourceBridges Atlas.wattAllBetaSketch =
  Audit.sameTheoryEquivalence
  ∷ Audit.measureConstructionAndPositivity
  ∷ Audit.noCircularGapInput
  ∷ Audit.reflectionPositivity
  ∷ Audit.continuumCutoffRemoval
  ∷ Audit.physicalGapScaleCompatibility
  ∷ Audit.allCompactSimpleGroupCoverage
  ∷ []

nielsenBridgeCountExact :
  length (sourceBridges Atlas.nielsenSemitaTopological) ≡ 7
nielsenBridgeCountExact = refl

toupinBridgeCountExact :
  length (sourceBridges Atlas.toupinCelestialHaar) ≡ 8
toupinBridgeCountExact = refl

rietzBridgeCountExact :
  length (sourceBridges Atlas.rietzUIDTScalar) ≡ 6
rietzBridgeCountExact = refl

jacobsenBridgeCountExact :
  length (sourceBridges Atlas.jacobsenFiveDimensionalOrbifold) ≡ 8
jacobsenBridgeCountExact = refl

agawaBridgeCountExact :
  length (sourceBridges Atlas.agawaNonlocalHolonomy) ≡ 7
agawaBridgeCountExact = refl

katayamaBridgeCountExact :
  length (sourceBridges Atlas.katayamaContinuumLSI) ≡ 7
katayamaBridgeCountExact = refl

randolphBridgeCountExact :
  length (sourceBridges Atlas.randolphCascadeTransfer) ≡ 6
randolphBridgeCountExact = refl

wattBridgeCountExact :
  length (sourceBridges Atlas.wattAllBetaSketch) ≡ 7
wattBridgeCountExact = refl
