module DASHI.Governance.PacificWomenNegotiationContributionNonDescentExact where

open import DASHI.Core.Prelude
import DASHI.Core.MeasurementBoundaryNonfactorabilityExact as Measurement
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Governance.FeministClimateJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- CARTER & HOWARD 2020: VISIBLE ROLE != SUBSTANTIVE CONTRIBUTION
--
-- George Carter & Elise Howard, "Pacific women in climate change negotiations",
-- Small States & Territories 3(2), 303-318 (2020).
-- Stable handle: http://hdl.handle.net/1885/262370.  No DOI asserted.
--
-- Source result used here: contribution can be underacknowledged when women are
-- less visible as heads of delegation while exercising proactive leadership as
-- technical negotiators or coalition coordinators.  The finite two-person
-- witness is DASHI-owned and is not a census of Pacific negotiators.
------------------------------------------------------------------------

data Negotiator : Set where technicalNegotiator coalitionCoordinator : Negotiator
data VisibleDelegationRole : Set where behindScenesRole : VisibleDelegationRole
data SubstantiveContribution : Set where technicalLeadership coalitionLeadership : SubstantiveContribution

visibleRole : Negotiator → VisibleDelegationRole
visibleRole _ = behindScenesRole

contribution : Negotiator → SubstantiveContribution
contribution technicalNegotiator = technicalLeadership
contribution coalitionCoordinator = coalitionLeadership

negotiationMeasurementBoundary :
  Measurement.MeasurementBoundary Negotiator VisibleDelegationRole SubstantiveContribution
negotiationMeasurementBoundary = Measurement.measurementBoundary visibleRole contribution

visibleRoleLoss : Measurement.BoundaryLossWitness negotiationMeasurementBoundary
visibleRoleLoss =
  Measurement.boundaryLossWitness technicalNegotiator coalitionCoordinator refl (λ ())

contributionDoesNotDescendThroughVisibleRole :
  Consumer.FactorsThrough visibleRole contribution → ⊥
contributionDoesNotDescendThroughVisibleRole =
  Measurement.boundaryLossBlocksFactorization visibleRoleLoss

joinedObserverStrictlyRefinesVisibleRole :
  Observer.StrictRefinement visibleRole (Observer.pairObserver visibleRole contribution)
joinedObserverStrictlyRefinesVisibleRole =
  Observer.strictPairRefinement
    visibleRole contribution
    technicalNegotiator coalitionCoordinator
    refl (λ ())

source : Sources.SourceReference
source = Sources.carterHoward2020

record PacificNegotiationContributionBoundary : Set where
  constructor pacificNegotiationContributionBoundary
  field
    formalVisibilityDeterminesSubstantiveContribution : Bool
    formalVisibilityDeterminesSubstantiveContributionIsFalse :
      formalVisibilityDeterminesSubstantiveContribution ≡ false
    addingContributionObserverCanStrictlyRefineVisibility : Bool
    addingContributionObserverCanStrictlyRefineVisibilityIsTrue :
      addingContributionObserverCanStrictlyRefineVisibility ≡ true
    underacknowledgedContributionMeansNoLeadership : Bool
    underacknowledgedContributionMeansNoLeadershipIsFalse :
      underacknowledgedContributionMeansNoLeadership ≡ false

canonicalPacificNegotiationContributionBoundary : PacificNegotiationContributionBoundary
canonicalPacificNegotiationContributionBoundary =
  pacificNegotiationContributionBoundary false refl true refl false refl
