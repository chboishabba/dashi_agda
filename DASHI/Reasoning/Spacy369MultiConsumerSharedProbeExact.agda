module DASHI.Reasoning.Spacy369MultiConsumerSharedProbeExact where

open import DASHI.Core.Prelude

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyPNF369DialecticBridgeExact as Bridge369
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace

------------------------------------------------------------------------
-- MULTI-CONSUMER SHARED PROBE ON THE MATERIALISED SPACY / PNF / 369 FIXTURE
--
-- One richer provenance/context observation may close more than one declared
-- downstream consumer without identifying the whole hidden audit state.  The
-- finite fixture keeps a separate closure-residual coordinate invisible to the
-- shared probe, so shared usefulness cannot be promoted into universal closure.
------------------------------------------------------------------------

data GovernedStanding : Set where
  representedStanding selfSituatedStanding : GovernedStanding

data ClosureResidual : Set where
  closureResidualOpen closureResidualClosed : ClosureResidual

data SharedAuditWorld : Set where
  representedOpen
  representedClosed
  originatingOpen
  originatingClosed
  : SharedAuditWorld

subjectPosition : SharedAuditWorld → Subject.SubjectPosition
subjectPosition representedOpen = Subject.representedPosition
subjectPosition representedClosed = Subject.representedPosition
subjectPosition originatingOpen = Subject.originatingPosition
subjectPosition originatingClosed = Subject.originatingPosition

governedStanding : SharedAuditWorld → GovernedStanding
governedStanding representedOpen = representedStanding
governedStanding representedClosed = representedStanding
governedStanding originatingOpen = selfSituatedStanding
governedStanding originatingClosed = selfSituatedStanding

closureResidual : SharedAuditWorld → ClosureResidual
closureResidual representedOpen = closureResidualOpen
closureResidual representedClosed = closureResidualClosed
closureResidual originatingOpen = closureResidualOpen
closureResidual originatingClosed = closureResidualClosed

------------------------------------------------------------------------
-- Every finite world remains anchored to the SAME materialised parser reading
-- and 369 review atom.  The added coordinates are audit/provenance coordinates,
-- not parser observations manufactured after the fact.
------------------------------------------------------------------------

materialisedParserSurface : SharedAuditWorld → Candidate.CandidateSemanticFragment
materialisedParserSurface representedOpen = Trace.negNarrowCandidate
materialisedParserSurface representedClosed = Trace.negNarrowCandidate
materialisedParserSurface originatingOpen = Trace.negNarrowCandidate
materialisedParserSurface originatingClosed = Trace.negNarrowCandidate

materialised369Surface : SharedAuditWorld → Bridge369.SpacyCandidateDialectic369Atom
materialised369Surface representedOpen = Trace.revised369
materialised369Surface representedClosed = Trace.revised369
materialised369Surface originatingOpen = Trace.revised369
materialised369Surface originatingClosed = Trace.revised369

parserSurfaceCannotRecoverClosureResidual :
  INF.FactorsThrough materialisedParserSurface closureResidual → ⊥
parserSurfaceCannotRecoverClosureResidual =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      representedOpen
      representedClosed
      refl
      (λ ()))

chart369CannotRecoverClosureResidual :
  INF.FactorsThrough materialised369Surface closureResidual → ⊥
chart369CannotRecoverClosureResidual =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      representedOpen
      representedClosed
      refl
      (λ ()))

------------------------------------------------------------------------
-- One shared probe exposes subject position + governed standing together.
------------------------------------------------------------------------

sharedContextObservation :
  SharedAuditWorld → Subject.SubjectPosition × GovernedStanding
sharedContextObservation world =
  subjectPosition world , governedStanding world

data SharedEvidence : Set where
  initialSharedEvidence : SharedEvidence

sharedCompatible : Envelope.Compatible SharedEvidence SharedAuditWorld
sharedCompatible initialSharedEvidence world = ⊤

sharedContextBundle : Discriminator.ExperimentBundle SharedAuditWorld
sharedContextBundle =
  Discriminator.experimentBundle
    (Subject.SubjectPosition × GovernedStanding)
    sharedContextObservation
    2
    "materialised-spacy: shared subject-position + governed-standing probe"
    "independent provenance/context evidence; does not alter spaCy dependency evidence or 369 chart"

------------------------------------------------------------------------
-- The SAME probe closes the subject-position consumer.
------------------------------------------------------------------------

sharedProbeClosesSubjectConsumer :
  Discriminator.ProspectivelyClosesConsumer
    sharedCompatible subjectPosition sharedContextBundle
sharedProbeClosesSubjectConsumer evidence witness witnessCompatible
    left right leftCompatible rightCompatible =
  cong proj₁
    (trans (proj₂ leftCompatible) (sym (proj₂ rightCompatible)))

subjectSharedProbePlan :
  Sequential.SequentialConsumerPlan
    subjectPosition
    (sharedCompatible initialSharedEvidence)
subjectSharedProbePlan =
  Sequential.oneShotConsumerClosingPlan
    sharedCompatible
    subjectPosition
    initialSharedEvidence
    sharedContextBundle
    sharedProbeClosesSubjectConsumer

------------------------------------------------------------------------
-- The SAME probe also closes the governed-standing consumer.
------------------------------------------------------------------------

sharedProbeClosesStandingConsumer :
  Discriminator.ProspectivelyClosesConsumer
    sharedCompatible governedStanding sharedContextBundle
sharedProbeClosesStandingConsumer evidence witness witnessCompatible
    left right leftCompatible rightCompatible =
  cong proj₂
    (trans (proj₂ leftCompatible) (sym (proj₂ rightCompatible)))

standingSharedProbePlan :
  Sequential.SequentialConsumerPlan
    governedStanding
    (sharedCompatible initialSharedEvidence)
standingSharedProbePlan =
  Sequential.oneShotConsumerClosingPlan
    sharedCompatible
    governedStanding
    initialSharedEvidence
    sharedContextBundle
    sharedProbeClosesStandingConsumer

------------------------------------------------------------------------
-- But closure-residual remains open: representedOpen and representedClosed
-- have exactly the same shared observation while differing on closure status.
------------------------------------------------------------------------

representedSharedObservationCollision :
  sharedContextObservation representedOpen
  ≡ sharedContextObservation representedClosed
representedSharedObservationCollision = refl

representedClosureResidualDiffers :
  closureResidual representedOpen ≡ closureResidual representedClosed → ⊥
representedClosureResidualDiffers ()

sharedContextCannotRecoverClosureResidual :
  INF.FactorsThrough sharedContextObservation closureResidual → ⊥
sharedContextCannotRecoverClosureResidual =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      representedOpen
      representedClosed
      representedSharedObservationCollision
      representedClosureResidualDiffers)

sharedProbeDoesNotCloseClosureConsumer :
  Discriminator.ProspectivelyClosesConsumer
    sharedCompatible closureResidual sharedContextBundle → ⊥
sharedProbeDoesNotCloseClosureConsumer closes =
  representedClosureResidualDiffers
    (closes
      initialSharedEvidence
      representedOpen
      tt
      representedOpen
      representedClosed
      (tt , refl)
      (tt , refl))

------------------------------------------------------------------------
-- Shared probe separation on one subject/standing collision.
------------------------------------------------------------------------

sharedProbeSeparatesRepresentedOriginating :
  Discriminator.BundleSeparates
    sharedContextBundle representedOpen originatingOpen
sharedProbeSeparatesRepresentedOriginating =
  Discriminator.bundleSeparates λ same →
    Subject.subjectPositionDiffers (cong proj₁ same)

------------------------------------------------------------------------
-- Multi-consumer receipt: one observation can serve several declared consumers
-- while leaving another consumer unresolved.
------------------------------------------------------------------------

record SharedProbeCoverageReceipt : Set₁ where
  constructor sharedProbeCoverageReceipt
  field
    bundle : Discriminator.ExperimentBundle SharedAuditWorld
    closesSubject :
      Discriminator.ProspectivelyClosesConsumer
        sharedCompatible subjectPosition bundle
    closesStanding :
      Discriminator.ProspectivelyClosesConsumer
        sharedCompatible governedStanding bundle
    doesNotCloseClosureResidual :
      Discriminator.ProspectivelyClosesConsumer
        sharedCompatible closureResidual bundle → ⊥

canonicalSharedProbeCoverageReceipt : SharedProbeCoverageReceipt
canonicalSharedProbeCoverageReceipt =
  sharedProbeCoverageReceipt
    sharedContextBundle
    sharedProbeClosesSubjectConsumer
    sharedProbeClosesStandingConsumer
    sharedProbeDoesNotCloseClosureConsumer

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record Spacy369MultiConsumerSharedProbeBoundary : Set where
  constructor spacy369MultiConsumerSharedProbeBoundary
  field
    oneProbeMayCloseSeveralConsumers : Bool
    oneProbeMayCloseSeveralConsumersIsTrue :
      oneProbeMayCloseSeveralConsumers ≡ true
    oneProbeClosingSeveralConsumersClosesEveryConsumer : Bool
    oneProbeClosingSeveralConsumersClosesEveryConsumerIsFalse :
      oneProbeClosingSeveralConsumersClosesEveryConsumer ≡ false
    sharedProbeRecoversClosureResidual : Bool
    sharedProbeRecoversClosureResidualIsFalse :
      sharedProbeRecoversClosureResidual ≡ false
    parserOr369SurfaceRecoversAllAuditCoordinates : Bool
    parserOr369SurfaceRecoversAllAuditCoordinatesIsFalse :
      parserOr369SurfaceRecoversAllAuditCoordinates ≡ false
    richerContextObservationRewritesParserEvidence : Bool
    richerContextObservationRewritesParserEvidenceIsFalse :
      richerContextObservationRewritesParserEvidence ≡ false
    sharedInformationUtilityMeansSharedSemanticAuthority : Bool
    sharedInformationUtilityMeansSharedSemanticAuthorityIsFalse :
      sharedInformationUtilityMeansSharedSemanticAuthority ≡ false

canonicalSpacy369MultiConsumerSharedProbeBoundary :
  Spacy369MultiConsumerSharedProbeBoundary
canonicalSpacy369MultiConsumerSharedProbeBoundary =
  spacy369MultiConsumerSharedProbeBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
