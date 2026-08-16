module DASHI.Governance.EpistemicAttractorDynamicsExact where

open import DASHI.Core.Prelude

import DASHI.Governance.EpistemicAttractorCore as Epistemic
import DASHI.Governance.GenericSocialAttractor as Attractor

------------------------------------------------------------------------
-- Dynamical completion of EpistemicAttractorCore.
--
-- The structural core separates trust update, evidence reframing and
-- disconfirmation inversion.  Here we expose the exact dynamical obligations
-- needed before the word "attractor" is mathematically justified.
------------------------------------------------------------------------

record EpistemicDynamics
  (S : Epistemic.TrustUpdateSystem)
  (R : Epistemic.EvidenceReframingSystem S) : Set₁ where
  field
    informant : Epistemic.Informant S
    domain : Epistemic.Domain S
    evidence : Epistemic.Evidence S

    TrustState : Set
    encodeTrust : Epistemic.Trust S → TrustState
    decodeTrust : TrustState → Epistemic.Trust S

    updateState : TrustState → TrustState

    updateStateMatchesReframedEvidence :
      (t : TrustState) →
      decodeTrust (updateState t)
      ≡ Epistemic.update S informant domain (decodeTrust t)
          (Epistemic.EvidenceReframingSystem.reframe R evidence)

open EpistemicDynamics public

asDiscreteSystem :
  ∀ {S R} →
  EpistemicDynamics S R →
  Attractor.DiscreteSystem
asDiscreteSystem dynamics =
  record
    { State = EpistemicDynamics.TrustState dynamics
    ; step = EpistemicDynamics.updateState dynamics
    }

------------------------------------------------------------------------
-- Self-sealing is not enough for stability.  Idempotence (or another genuine
-- convergence hypothesis) is required.  Under explicit idempotence, however,
-- every updated trust state is an exact fixed point.
------------------------------------------------------------------------

record StableEpistemicClosure
  {S : Epistemic.TrustUpdateSystem}
  {R : Epistemic.EvidenceReframingSystem S}
  (D : EpistemicDynamics S R) : Set where
  field
    updateIdempotent :
      (t : EpistemicDynamics.TrustState D) →
      EpistemicDynamics.updateState D
        (EpistemicDynamics.updateState D t)
      ≡ EpistemicDynamics.updateState D t

open StableEpistemicClosure public

stableClosureGivesFixedPoint :
  ∀ {S R}
  (D : EpistemicDynamics S R) →
  StableEpistemicClosure D →
  EpistemicDynamics.TrustState D →
  Attractor.FixedPoint (asDiscreteSystem D)
stableClosureGivesFixedPoint D stable t =
  Attractor.fixedPointFromImage
    (asDiscreteSystem D)
    (record { stepIdempotent = StableEpistemicClosure.updateIdempotent stable })
    t

------------------------------------------------------------------------
-- A closed neighbourhood is the second explicit ingredient.  It must be
-- supplied as a predicate on trust states; no social-media or ideological
-- community is silently assumed to be closed.
------------------------------------------------------------------------

record ClosedTrustNeighbourhood
  {S : Epistemic.TrustUpdateSystem}
  {R : Epistemic.EvidenceReframingSystem S}
  (D : EpistemicDynamics S R) : Set₁ where
  field
    InNeighbourhood : EpistemicDynamics.TrustState D → Set
    updateStaysInside :
      (t : EpistemicDynamics.TrustState D) →
      InNeighbourhood t →
      InNeighbourhood (EpistemicDynamics.updateState D t)

open ClosedTrustNeighbourhood public

closedNeighbourhoodAsInvariant :
  ∀ {S R}
  (D : EpistemicDynamics S R) →
  ClosedTrustNeighbourhood D →
  Attractor.InvariantRegion (asDiscreteSystem D)
closedNeighbourhoodAsInvariant D closed =
  record
    { Region = ClosedTrustNeighbourhood.InNeighbourhood closed
    ; closedUnderStep = ClosedTrustNeighbourhood.updateStaysInside closed
    }

closedNeighbourhoodPersistsTwoSteps :
  ∀ {S R}
  (D : EpistemicDynamics S R) →
  (closed : ClosedTrustNeighbourhood D) →
  (t : EpistemicDynamics.TrustState D) →
  ClosedTrustNeighbourhood.InNeighbourhood closed t →
  ClosedTrustNeighbourhood.InNeighbourhood closed
    (EpistemicDynamics.updateState D
      (EpistemicDynamics.updateState D t))
closedNeighbourhoodPersistsTwoSteps D closed t inside =
  Attractor.closedUnderTwoSteps
    (asDiscreteSystem D)
    (closedNeighbourhoodAsInvariant D closed)
    t inside

------------------------------------------------------------------------
-- Promotion boundary: disconfirmation inversion + a closed neighbourhood do
-- not by themselves establish an attractor.  Stable closure additionally
-- requires an explicit dynamical stability witness.
------------------------------------------------------------------------

record EpistemicDynamicsBoundary : Set where
  constructor epistemicDynamicsBoundary
  field
    inversionAloneImpliesFixedPoint : Bool
    closedGraphAloneImpliesFixedPoint : Bool
    stabilityRequiresDynamicsWitness : Bool
    namedPipelineRequiresCaseEvidence : Bool

canonicalEpistemicDynamicsBoundary : EpistemicDynamicsBoundary
canonicalEpistemicDynamicsBoundary =
  epistemicDynamicsBoundary false false true true
