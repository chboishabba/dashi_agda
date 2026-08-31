module DASHI.Chemistry.RegulatoryAnalytePanelRefinementExact where

------------------------------------------------------------------------
-- DECLARED ASSAY-PANEL REFINEMENT CROSS-POLLINATION
--
-- Reuses the repository's canonical non-factorability pattern: if a coarse
-- observation identifies two fine states that differ on a consumer-relevant
-- coordinate, the missing coordinate cannot be reconstructed by interpreting
-- or relabelling the coarse result.  A genuinely richer observation can,
-- however, separate the pair.
--
-- This is a finite DASHI observation model.  `requiredPanel` means the coarse
-- panel required by THIS FINITE FIXTURE; it is not asserted to equal the whole
-- legal TGO 93 / Ph Eur pesticide-limit architecture or any laboratory's assay
-- scope.  Real named regulatory membership lives in
-- TGO93PhEurPesticideMembershipExact; method observability/LOD/LOQ lives in
-- AssayDetectionEnvelopeExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Chemistry.RegulatoryAnalyteCoverageBidiExact as Coverage

------------------------------------------------------------------------
-- Coarse declared fixture panel versus a declared expanded observation.
------------------------------------------------------------------------

data PanelStage : Set where
  requiredPanel expandedPanel : PanelStage

data PanelObservation : Set where
  requiredPass expandedPass expandedOffPanelHit : PanelObservation

observeAt : PanelStage → Coverage.FineBatch → PanelObservation
observeAt requiredPanel Coverage.cleanPassingBatch = requiredPass
observeAt requiredPanel Coverage.offPanelPresentPassingBatch = requiredPass
observeAt expandedPanel Coverage.cleanPassingBatch = expandedPass
observeAt expandedPanel Coverage.offPanelPresentPassingBatch = expandedOffPanelHit

requiredProjection : Coverage.FineBatch → PanelObservation
requiredProjection = observeAt requiredPanel

expandedProjection : Coverage.FineBatch → PanelObservation
expandedProjection = observeAt expandedPanel

requiredPanelCollision :
  NonFactor.NonFactorabilityWitness
    requiredProjection Coverage.offPanelPresence
requiredPanelCollision =
  NonFactor.nonFactorabilityWitness
    Coverage.cleanPassingBatch
    Coverage.offPanelPresentPassingBatch
    refl
    (λ ())

requiredPanelCannotRecoverOffPanelPresence :
  NonFactor.FactorsThrough requiredProjection Coverage.offPanelPresence → ⊥
requiredPanelCannotRecoverOffPanelPresence =
  NonFactor.witnessRulesOutEveryFlatFactorisation requiredPanelCollision

------------------------------------------------------------------------
-- The expanded observation is richer for this declared finite coordinate.
------------------------------------------------------------------------

decodeExpandedPresence : PanelObservation → Coverage.Presence
decodeExpandedPresence requiredPass = Coverage.absent
decodeExpandedPresence expandedPass = Coverage.absent
decodeExpandedPresence expandedOffPanelHit = Coverage.present

expandedProjectionRecoversDeclaredOffPanelCoordinate :
  NonFactor.FactorsThrough expandedProjection Coverage.offPanelPresence
expandedProjectionRecoversDeclaredOffPanelCoordinate =
  NonFactor.factorsThrough decodeExpandedPresence proof
  where
    proof :
      (batch : Coverage.FineBatch) →
      Coverage.offPanelPresence batch ≡
      decodeExpandedPresence (expandedProjection batch)
    proof Coverage.cleanPassingBatch = refl
    proof Coverage.offPanelPresentPassingBatch = refl

------------------------------------------------------------------------
-- Observation refinement is not universal chemical completeness.
------------------------------------------------------------------------

data ExpandedPanelImpliesUniversalChemicalCompletenessPermission : Set where

expandedPanelCannotAutoPromoteToUniversalChemicalCompleteness :
  ExpandedPanelImpliesUniversalChemicalCompletenessPermission → ⊥
expandedPanelCannotAutoPromoteToUniversalChemicalCompleteness ()

record PanelRefinementBoundary : Set where
  constructor panelRefinementBoundary
  field
    declaredCoarsePanelCanCollapseDistinctChemicalStates : Bool
    richerDeclaredPanelCanSeparateWitnessPair : Bool
    richerDeclaredPanelMeansAllPossibleChemistryObserved : Bool
    reinterpretationOfOldPassEqualsNewMeasurement : Bool
    fixturePanelEqualsWholeTGO93RegulatoryArchitecture : Bool

canonicalPanelRefinementBoundary : PanelRefinementBoundary
canonicalPanelRefinementBoundary =
  panelRefinementBoundary true true false false false
