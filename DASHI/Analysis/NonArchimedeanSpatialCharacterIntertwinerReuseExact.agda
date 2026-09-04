module DASHI.Analysis.NonArchimedeanSpatialCharacterIntertwinerReuseExact where

------------------------------------------------------------------------
-- EXISTING-MACHINERY REUSE FOR THE SPATIAL / CHARACTER WELD
--
-- This lane does not define another Fourier/intertwiner abstraction.
-- DASHI.Core.ReopenableConsumerInterventionKernelExact already owns the exact
-- commuting-square contract
--
--   projectOut (fineMap x) = coarseMap (projectIn x).
--
-- Here the fine carrier is the concrete spatial representation and the coarse
-- carrier is the character/monomial representation.  An exact analyze/synthesize
-- round trip plus the existing Intertwiner is sufficient to transport one-step
-- dynamics back to the same spatial object.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core

record SpatialCharacterRechart : Set₁ where
  field
    Spatial : Set
    Character : Set

    analyze : Spatial → Character
    synthesize : Character → Spatial

    spatialStep : Spatial → Spatial
    characterStep : Character → Character

    synthesizeAnalyze :
      (state : Spatial) →
      synthesize (analyze state) ≡ state

    analyzeSynthesize :
      (state : Character) →
      analyze (synthesize state) ≡ state

    exactIntertwiner :
      Core.Intertwiner analyze analyze spatialStep characterStep

open SpatialCharacterRechart public

spatialCharacterCommutes :
  (R : SpatialCharacterRechart) →
  (state : Spatial R) →
  analyze R (spatialStep R state)
  ≡ characterStep R (analyze R state)
spatialCharacterCommutes R =
  Core.commutes (exactIntertwiner R)

------------------------------------------------------------------------
-- The commuting square plus reconstruction recovers the literal spatial step.
-- No carrier equality between Spatial and Character is required.
------------------------------------------------------------------------

spatialStepRecoveredFromCharacterStep :
  (R : SpatialCharacterRechart) →
  (state : Spatial R) →
  synthesize R (characterStep R (analyze R state))
  ≡ spatialStep R state
spatialStepRecoveredFromCharacterStep R state =
  trans
    (cong (synthesize R) (sym (spatialCharacterCommutes R state)))
    (synthesizeAnalyze R (spatialStep R state))

------------------------------------------------------------------------
-- BIDI cutset.  The generic monomial power theorem is downstream of this
-- same-object rechart; period and orbit-weight receipts stay independent.
------------------------------------------------------------------------

record SpatialCharacterPowerCutset : Set₁ where
  field
    rechart : SpatialCharacterRechart
    fullPeriodReceipt : Set
    fullOrbitWeightReceipt : Set
    genericMonomialPowerReceipt : Set

open SpatialCharacterPowerCutset public

record ExistingMachineryReuseBoundary : Set where
  constructor existingMachineryReuseBoundary
  field
    newIntertwinerDatatypeRequired : Bool
    existingCoreIntertwinerReused : Bool
    exactAnalyzeSynthesizeRequired : Bool
    spatialCarrierEqualsCharacterCarrierRequired : Bool
    periodMayBeCollapsedIntoIntertwiner : Bool
    weightMayBeCollapsedIntoIntertwiner : Bool

canonicalExistingMachineryReuseBoundary : ExistingMachineryReuseBoundary
canonicalExistingMachineryReuseBoundary =
  existingMachineryReuseBoundary
    false
    true
    true
    false
    false
    false
