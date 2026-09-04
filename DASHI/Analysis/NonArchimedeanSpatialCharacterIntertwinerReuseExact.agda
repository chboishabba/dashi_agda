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
-- round trip plus the existing Intertwiner is sufficient to transport dynamics
-- back to the same spatial object.
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
-- Exact intertwiners lift to every iterate.  This is the generic power bridge
-- required by the source repo's monomial reduction:
--
--   analyze (S^m x) = C^m (analyze x)
--
-- and, by reconstruction,
--
--   synthesize (C^m (analyze x)) = S^m x.
------------------------------------------------------------------------

iterate :
  {A : Set} →
  Nat →
  (A → A) →
  A → A
iterate zero step state = state
iterate (suc n) step state = step (iterate n step state)

iterateIntertwines :
  (R : SpatialCharacterRechart) →
  (n : Nat) →
  (state : Spatial R) →
  analyze R (iterate n (spatialStep R) state)
  ≡ iterate n (characterStep R) (analyze R state)
iterateIntertwines R zero state = refl
iterateIntertwines R (suc n) state =
  trans
    (spatialCharacterCommutes R (iterate n (spatialStep R) state))
    (cong (characterStep R) (iterateIntertwines R n state))

spatialIterateRecoveredFromCharacterIterate :
  (R : SpatialCharacterRechart) →
  (n : Nat) →
  (state : Spatial R) →
  synthesize R (iterate n (characterStep R) (analyze R state))
  ≡ iterate n (spatialStep R) state
spatialIterateRecoveredFromCharacterIterate R n state =
  trans
    (cong (synthesize R) (sym (iterateIntertwines R n state)))
    (synthesizeAnalyze R (iterate n (spatialStep R) state))

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
    exactIntertwinerLiftsToAllIterates : Bool

canonicalExistingMachineryReuseBoundary : ExistingMachineryReuseBoundary
canonicalExistingMachineryReuseBoundary =
  existingMachineryReuseBoundary
    false
    true
    true
    false
    false
    false
    true
