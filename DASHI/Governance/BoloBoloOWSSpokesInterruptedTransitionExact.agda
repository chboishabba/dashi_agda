module DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyOWSDevelopmentInterfaceProcessPanelExact as Interface
import DASHI.Governance.OccupyOWSDevelopmentDurationPanelExact as Duration

------------------------------------------------------------------------
-- OWS SPOKES COUNCIL AS AN INTERRUPTED SAME-CONTEXT STRUCTURAL TRANSITION.
--
-- Source history: the Structure proposal was intended to route operational /
-- logistical work through working groups/caucuses and rotating spokes rather
-- than requiring the mass GA to carry all such discussion. The first Spokes
-- Council met 7 November 2011. This is unusually close to the flat-vs-nested
-- counterfactual, but it is not a randomized or matched trial.
------------------------------------------------------------------------

record InterruptedTransitionWindow : Set where
  constructor interruptedTransitionWindow
  field
    firstSpokesCouncilDayNovember2011 : Nat
    preTransitionDevelopmentRecordCount : Nat
    postTransitionDevelopmentRecordCount : Nat
    protectedPostTransitionHoldoutCount : Nat
    evictionDayNovember2011 : Nat

open InterruptedTransitionWindow public

canonicalTransitionWindow : InterruptedTransitionWindow
canonicalTransitionWindow = interruptedTransitionWindow 7 35 3 1 15

------------------------------------------------------------------------
-- Source-reported scale shock motivating the structural transition.
--
-- Holmes reports, using a Facilitation Working Group personal communication,
-- that OWS grew from roughly fifty planning participants and around half a
-- dozen working groups to more than four thousand active organizers and more
-- than one hundred working groups by late October. These are retrospective /
-- participant-organizer source coordinates, not census-quality counts.
------------------------------------------------------------------------

record OWSScaleShockContext : Set where
  constructor owsScaleShockContext
  field
    earlyPlanningParticipantApprox : Nat
    earlyWorkingGroupApprox : Nat
    lateOctoberActiveOrganizerLowerBound : Nat
    lateOctoberWorkingGroupLowerBound : Nat
    sourceReportsRapidScaleExpansion : Bool
    countsAreCompleteCensus : Bool

open OWSScaleShockContext public

canonicalOWSScaleShockContext : OWSScaleShockContext
canonicalOWSScaleShockContext = owsScaleShockContext 50 6 4000 100 true false

record InterfaceLexicalAggregate : Set where
  constructor interfaceLexicalAggregate
  field
    reportBackParagraphs : Nat
    delegateParagraphs : Nat
    spokesParagraphs : Nat
    liaisonParagraphs : Nat
    interGroupParagraphs : Nat
    mediationParagraphs : Nat
    tabledParagraphs : Nat
    workingGroupParagraphs : Nat

open InterfaceLexicalAggregate public

-- DASHI sums over the already-frozen development rows. The split is temporal
-- only: records <= 41 are pre-first-Spokes, while 43-45 are post-first-Spokes;
-- protected record 42 (8 Nov) is never opened for this comparison.
preSpokesDevelopmentLexicalAggregate : InterfaceLexicalAggregate
preSpokesDevelopmentLexicalAggregate =
  interfaceLexicalAggregate 24 2 65 4 2 19 15 331

postSpokesDevelopmentLexicalAggregate : InterfaceLexicalAggregate
postSpokesDevelopmentLexicalAggregate =
  interfaceLexicalAggregate 3 4 6 0 0 1 1 49

-- Duration coverage is far too sparse for a before/after effect estimate:
-- five development GA duration rows are pre-Spokes and exactly one is post.
preSpokesDurationRowCount : Nat
preSpokesDurationRowCount = 5

postSpokesDurationRowCount : Nat
postSpokesDurationRowCount = 1

------------------------------------------------------------------------
-- Mixed mechanism observations from Holmes' participant-organizer account.
--
-- These are source claims about the early and later Spokes experience, not
-- DASHI causal estimates. Positive and negative observations are retained.
------------------------------------------------------------------------

record SpokesMechanismObservations : Set where
  constructor spokesMechanismObservations
  field
    groupFirstDiscussionReported : Bool
    inauguralMeetingEasierToHearReported : Bool
    inauguralMeetingMoreInDepthDiscussionReported : Bool
    laterFacilitationBreakdownReported : Bool
    laterConflictReported : Bool
    spokeRotationImplementationProblemReported : Bool
    retrospectivelyMoreConsistentThanNYCGAReported : Bool
    retrospectivelyMoreAccountableThanNYCGAReported : Bool
    decisionsReflectedOccupierNeedsReported : Bool
    persistentDistrustAndAntagonismReported : Bool
    laterSpendingFreezeReported : Bool
    mixedMechanismEvidence : Bool

open SpokesMechanismObservations public

canonicalSpokesMechanismObservations : SpokesMechanismObservations
canonicalSpokesMechanismObservations =
  spokesMechanismObservations
    true true true true true true true true true true true true

record OWSSpokesTransitionBoundary : Set where
  constructor owsSpokesTransitionBoundary
  field
    sameMovementContext : Bool
    flatToNestedStructuralChangePresent : Bool
    protectedHoldoutConsumed : Bool
    randomizedAssignmentPresent : Bool
    issueMixHeldFixed : Bool
    participantCompositionHeldFixed : Bool
    facilitationLearningHeldFixed : Bool
    evictionShockAbsent : Bool
    lexicalBeforeAfterDifferenceIsCausalEffect : Bool
    qualitativeImprovementReportIsCausalEffect : Bool
    retrospectiveAccountEqualsUnderlyingMinuteRecord : Bool
    sourceScaleCountsAreExactPopulationCensus : Bool
    durationCoverageSupportsEffectEstimate : Bool
    transitionUsefulForMechanismAndMeasurementDesign : Bool

open OWSSpokesTransitionBoundary public

canonicalOWSSpokesTransitionBoundary : OWSSpokesTransitionBoundary
canonicalOWSSpokesTransitionBoundary =
  owsSpokesTransitionBoundary
    true true false false false false false false false false false false false true

canonicalOWSSpokesInterruptedTransitionReceipt : GenericReceipt.GenericReceipt
canonicalOWSSpokesInterruptedTransitionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS Spokes Council interrupted same-context transition"
    "DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionExact"
    "canonicalTransitionWindow / canonicalOWSScaleShockContext / canonicalSpokesMechanismObservations / canonicalOWSSpokesTransitionBoundary"
    "recasts the OWS Spokes Council as the closest available same-movement flat-to-nested structural transition, records the retrospective scale shock from roughly fifty planning participants/about six working groups to over four thousand active organizers/over one hundred working groups, preserves the protected 8 November holdout, and retains mixed mechanism evidence including easier/deeper inaugural group-first discussion alongside later conflict, facilitation/rotation problems, persistent distrust and eventual spending freeze"
    "Holmes' participant-organizer account is not substituted for the underlying Spokes minutes or treated as a census; the transition is confounded by changing issue mix, composition, learning and eviction, and neither lexical differences nor qualitative reports are promoted to a causal cost effect or bolo bound"
    "agda -i . DASHI/Governance/BoloBoloOWSSpokesInterruptedTransitionRegression.agda"
