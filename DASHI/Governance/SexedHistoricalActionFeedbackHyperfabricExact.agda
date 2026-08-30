module DASHI.Governance.SexedHistoricalActionFeedbackHyperfabricExact where

------------------------------------------------------------------------
-- ENACTED-CHOICE FEEDBACK OVER THE SEXED HISTORICAL HYPERFABRIC
--
-- Cross-pollinates the formal/effective/conceived choice bridge with the
-- existing co-constitution hyperfabric and revolutionary-practice braid.
--
-- Central separation:
--
--   conceived option != enacted action != downstream historical feedback.
--
-- An enacted action can update self-construction, other-construction, power,
-- memory and later option cones differently.  The same public action does not
-- determine a unique historical effect, and practice is not promoted into a
-- universal emancipatory or reactionary law.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SexedHistoricalChoiceConeBridgeExact as Choice
import DASHI.Governance.SexedHistoricalCoConstitutionHyperfabricExact as Hyper
import DASHI.Governance.RevolutionaryPracticeBraid as Practice

------------------------------------------------------------------------
-- Action surface and feedback channels.
------------------------------------------------------------------------

data EnactedAction : Set where
  suffrageActivism
  religiousExit
  witchSelfIdentification
  crossSexSolidarity
  masculineCounterReaction
  reciprocalCareRearticulation
  : EnactedAction

data FeedbackChannel : Set where
  selfConstructionFeedback
  otherConstructionFeedback
  institutionalPowerFeedback
  historicalMemoryFeedback
  laterOptionConeFeedback
  : FeedbackChannel

data FeedbackStatus : Set where
  expands contracts revises persists contested unresolved : FeedbackStatus

record ActionFeedbackReceipt : Set where
  constructor action-feedback-receipt
  field
    epoch : Hyper.HistoricalEpoch
    actor : Hyper.Position
    target : Hyper.Position
    action : EnactedAction
    conceivedBeforeAction : Choice.ConceivedChoiceSurface
    feedback : FeedbackChannel → FeedbackStatus
    actionDeterminesUniqueFeedback : Bool
    actionDeterminesUniqueFeedbackIsFalse : actionDeterminesUniqueFeedback ≡ false

open ActionFeedbackReceipt public

------------------------------------------------------------------------
-- Finite comparison receipts.  These are DASHI comparison constructions, not
-- empirical population claims about all activists, apostates, witches, men or
-- women in a period.
------------------------------------------------------------------------

suffrageFeedbackExpansive : FeedbackChannel → FeedbackStatus
suffrageFeedbackExpansive selfConstructionFeedback = revises
suffrageFeedbackExpansive otherConstructionFeedback = revises
suffrageFeedbackExpansive institutionalPowerFeedback = expands
suffrageFeedbackExpansive historicalMemoryFeedback = revises
suffrageFeedbackExpansive laterOptionConeFeedback = expands

suffrageFeedbackRepressed : FeedbackChannel → FeedbackStatus
suffrageFeedbackRepressed selfConstructionFeedback = revises
suffrageFeedbackRepressed otherConstructionFeedback = contested
suffrageFeedbackRepressed institutionalPowerFeedback = persists
suffrageFeedbackRepressed historicalMemoryFeedback = revises
suffrageFeedbackRepressed laterOptionConeFeedback = contracts

canonicalSuffrageExpansiveReceipt : ActionFeedbackReceipt
canonicalSuffrageExpansiveReceipt =
  action-feedback-receipt
    Hyper.suffrageRearticulation
    Hyper.feminine
    Hyper.masculine
    suffrageActivism
    Choice.conceivedAsPossible
    suffrageFeedbackExpansive
    false refl

canonicalSuffrageRepressedReceipt : ActionFeedbackReceipt
canonicalSuffrageRepressedReceipt =
  action-feedback-receipt
    Hyper.suffrageRearticulation
    Hyper.feminine
    Hyper.masculine
    suffrageActivism
    Choice.conceivedAsPossible
    suffrageFeedbackRepressed
    false refl

------------------------------------------------------------------------
-- Conceived option does not determine enactment.
------------------------------------------------------------------------

data ChoiceToActionFineState : Set where
  conceivedButNotEnacted
  conceivedAndEnacted
  : ChoiceToActionFineState

conceivedSurface : ChoiceToActionFineState → Choice.ConceivedChoiceSurface
conceivedSurface _ = Choice.conceivedAsPossible

data EnactmentSurface : Set where notEnacted enacted : EnactmentSurface

enactmentSurface : ChoiceToActionFineState → EnactmentSurface
enactmentSurface conceivedButNotEnacted = notEnacted
enactmentSurface conceivedAndEnacted = enacted

conceivedChoiceCannotRecoverEnactment :
  INF.FactorsThrough conceivedSurface enactmentSurface → ⊥
conceivedChoiceCannotRecoverEnactment =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      conceivedButNotEnacted
      conceivedAndEnacted
      refl
      (λ ()))

------------------------------------------------------------------------
-- Same enacted action does not determine downstream feedback.
------------------------------------------------------------------------

data ActionFeedbackFineState : Set where
  suffrageActionWithExpansion
  suffrageActionWithRepression
  : ActionFeedbackFineState

actionSurface : ActionFeedbackFineState → EnactedAction
actionSurface _ = suffrageActivism

laterOptionFeedback : ActionFeedbackFineState → FeedbackStatus
laterOptionFeedback suffrageActionWithExpansion = expands
laterOptionFeedback suffrageActionWithRepression = contracts

sameActionCannotRecoverLaterOptionFeedback :
  INF.FactorsThrough actionSurface laterOptionFeedback → ⊥
sameActionCannotRecoverLaterOptionFeedback =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      suffrageActionWithExpansion
      suffrageActionWithRepression
      refl
      (λ ()))

------------------------------------------------------------------------
-- Same action also cannot recover institutional-power effect.
------------------------------------------------------------------------

institutionalPowerEffect : ActionFeedbackFineState → FeedbackStatus
institutionalPowerEffect suffrageActionWithExpansion = expands
institutionalPowerEffect suffrageActionWithRepression = persists

sameActionCannotRecoverInstitutionalPowerEffect :
  INF.FactorsThrough actionSurface institutionalPowerEffect → ⊥
sameActionCannotRecoverInstitutionalPowerEffect =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      suffrageActionWithExpansion
      suffrageActionWithRepression
      refl
      (λ ()))

------------------------------------------------------------------------
-- Cross-pollination with the revolutionary-practice braid.  Institutional,
-- relational, epistemic and historical-trauma strands remain distinct; action
-- therefore cannot be treated as an automatic all-fibre transformation.
------------------------------------------------------------------------

practiceBraidKeepsInstitutionalAndRelationalChangeDistinct :
  Practice.institutionalChangeImpliesRelationalChange
    Practice.canonicalRevolutionaryPracticeBraidSurface
  ≡ false
practiceBraidKeepsInstitutionalAndRelationalChangeDistinct =
  Practice.RevolutionaryPracticeBraidBoundary.institutionalChangeDoesNotCloseRelationalChange
    Practice.canonicalRevolutionaryPracticeBraidBoundary

------------------------------------------------------------------------
-- No-promotion boundaries for the historical applications discussed in this
-- tranche.  These are structural gates, not empirical verdicts.
------------------------------------------------------------------------

data ActivismGuaranteesInstitutionalVictory : Set where

data ApostasyGuaranteesPsychologicalDeconstruction : Set where

data WitchSelfIdentificationGuaranteesMaterialAutonomy : Set where

data SolidarityGuaranteesPowerParity : Set where

data CounterReactionErasesPriorRearticulation : Set where

data EnactedChoiceGuaranteesHistoricalClosure : Set where

activismDoesNotGuaranteeInstitutionalVictory :
  ActivismGuaranteesInstitutionalVictory → ⊥
activismDoesNotGuaranteeInstitutionalVictory ()

apostasyDoesNotGuaranteePsychologicalDeconstruction :
  ApostasyGuaranteesPsychologicalDeconstruction → ⊥
apostasyDoesNotGuaranteePsychologicalDeconstruction ()

witchSelfIdentificationDoesNotGuaranteeMaterialAutonomy :
  WitchSelfIdentificationGuaranteesMaterialAutonomy → ⊥
witchSelfIdentificationDoesNotGuaranteeMaterialAutonomy ()

solidarityDoesNotGuaranteePowerParity :
  SolidarityGuaranteesPowerParity → ⊥
solidarityDoesNotGuaranteePowerParity ()

counterReactionDoesNotErasePriorRearticulation :
  CounterReactionErasesPriorRearticulation → ⊥
counterReactionDoesNotErasePriorRearticulation ()

enactedChoiceDoesNotGuaranteeHistoricalClosure :
  EnactedChoiceGuaranteesHistoricalClosure → ⊥
enactedChoiceDoesNotGuaranteeHistoricalClosure ()

record SexedHistoricalActionFeedbackBoundary : Set where
  constructor sexed-historical-action-feedback-boundary
  field
    conceivedChoiceEqualsEnactedChoice : Bool
    sameActionMeansSameFeedback : Bool
    actionAutomaticallyChangesEveryFibre : Bool
    activismGuaranteesInstitutionalVictory : Bool
    apostasyGuaranteesPsychologicalDeconstruction : Bool
    witchIdentityGuaranteesMaterialAutonomy : Bool
    solidarityGuaranteesPowerParity : Bool
    reactionErasesPriorChange : Bool
    enactedChoiceGuaranteesClosure : Bool
    feedbackMustRemainChannelIndexed : Bool

canonicalSexedHistoricalActionFeedbackBoundary :
  SexedHistoricalActionFeedbackBoundary
canonicalSexedHistoricalActionFeedbackBoundary =
  sexed-historical-action-feedback-boundary
    false false false false false false false false false true
