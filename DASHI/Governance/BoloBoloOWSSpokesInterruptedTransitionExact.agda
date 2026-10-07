module DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyOWSDevelopmentInterfaceProcessPanelExact as Interface
import DASHI.Governance.OccupyOWSDevelopmentDurationPanelExact as Duration

------------------------------------------------------------------------
-- OWS SPOKES COUNCIL AS AN INTERRUPTED SAME-CONTEXT STRUCTURAL TRANSITION.
--
-- Source history: the Structure proposal was intended to route operational /
-- logistical work through clustered working groups/caucuses and rotating
-- spokes rather than requiring the mass GA to carry all such discussion.  The
-- first Spokes Council met 7 November 2011.  This is unusually close to the
-- flat-vs-nested counterfactual, but it is not a randomized or matched trial.
--
-- The frozen development corpus contains only three non-holdout GA records
-- strictly after the first Spokes Council and before/at the 15 November raid
-- endpoint (records 43,44,45).  Record 42 (8 Nov) remains protected holdout.
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

-- DASHI sums over the already-frozen development rows.  The split is temporal
-- only: records <= 41 are pre-first-Spokes, while 43-45 are post-first-Spokes;
-- protected record 42 is never opened for this comparison.
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
    durationCoverageSupportsEffectEstimate : Bool
    transitionUsefulForMechanismAndMeasurementDesign : Bool

open OWSSpokesTransitionBoundary public

canonicalOWSSpokesTransitionBoundary : OWSSpokesTransitionBoundary
canonicalOWSSpokesTransitionBoundary =
  owsSpokesTransitionBoundary
    true true false false false false false false false false true

canonicalOWSSpokesInterruptedTransitionReceipt : GenericReceipt.GenericReceipt
canonicalOWSSpokesInterruptedTransitionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS Spokes Council interrupted same-context transition"
    "DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionExact"
    "canonicalTransitionWindow / preSpokesDevelopmentLexicalAggregate / postSpokesDevelopmentLexicalAggregate / canonicalOWSSpokesTransitionBoundary"
    "recasts the creation of the OWS Spokes Council as the closest available same-movement flat-to-nested structural transition and freezes development-only pre/post lexical aggregates while preserving the protected 8 November holdout"
    "the window is extremely short and confounded by changing issue mix, participant composition, facilitation learning and the 15 November eviction; only one post-transition GA duration row is source-paid, so no causal coordination-cost effect or bolo cost bound is promoted"
    "agda -i . DASHI/Governance/BoloBoloOWSSpokesInterruptedTransitionRegression.agda"
