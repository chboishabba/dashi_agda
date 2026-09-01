module DASHI.Governance.DrugCategoryAdaptiveQuotientExperimentLoopExact where

open import DASHI.Core.Prelude

import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Governance.DrugCategoryExplicitConsumerQuotientExact as Quotient
import DASHI.Governance.DrugCategoryCostedQuotientDiscriminatorExact as Costed

------------------------------------------------------------------------
-- ADAPTIVE QUOTIENT EXPERIMENT LOOP
--
-- The current clinical quotient leaves subject/history consumers unresolved.
-- A selected discriminator is observed, the live fibre is intersected with its
-- outcome, and the declared consumer closes.  The terminal condition is
-- consumer agreement, not whole-world identity.
------------------------------------------------------------------------

Evidence : Set
Evidence = ⊤

allCompatible : Envelope.Compatible Evidence Quotient.TranslationState
allCompatible evidence state = ⊤

subjectConsumer : Quotient.TranslationState → Quotient.SubjectObservation
subjectConsumer = Quotient.subjectObserver

historyConsumer : Quotient.TranslationState → Quotient.HistoryObservation
historyConsumer = Quotient.historyObserver

------------------------------------------------------------------------
-- A bundle observing the consumer itself prospectively closes that consumer.
------------------------------------------------------------------------

subjectBundleCloses :
  Discriminator.ProspectivelyClosesConsumer
    allCompatible subjectConsumer Costed.subjectBundle
subjectBundleCloses evidence witness compatible left right leftMeasured rightMeasured =
  trans
    (proj₂ leftMeasured)
    (sym (proj₂ rightMeasured))

historyBundleCloses :
  Discriminator.ProspectivelyClosesConsumer
    allCompatible historyConsumer Costed.historyBundle
historyBundleCloses evidence witness compatible left right leftMeasured rightMeasured =
  trans
    (proj₂ leftMeasured)
    (sym (proj₂ rightMeasured))

subjectOneShotPlan :
  Sequential.SequentialConsumerPlan
    subjectConsumer
    (allCompatible tt)
subjectOneShotPlan =
  Sequential.oneShotConsumerClosingPlan
    allCompatible
    subjectConsumer
    tt
    Costed.subjectBundle
    subjectBundleCloses

historyOneShotPlan :
  Sequential.SequentialConsumerPlan
    historyConsumer
    (allCompatible tt)
historyOneShotPlan =
  Sequential.oneShotConsumerClosingPlan
    allCompatible
    historyConsumer
    tt
    Costed.historyBundle
    historyBundleCloses

------------------------------------------------------------------------
-- The observed outcome refines the live fibre exactly by intersection.
------------------------------------------------------------------------

subjectRefinedFibre :
  Quotient.SubjectObservation → Quotient.TranslationState → Set
subjectRefinedFibre outcome =
  Sequential.RefineByBundle
    (allCompatible tt)
    Costed.subjectBundle
    outcome

historyRefinedFibre :
  Quotient.HistoryObservation → Quotient.TranslationState → Set
historyRefinedFibre outcome =
  Sequential.RefineByBundle
    (allCompatible tt)
    Costed.historyBundle
    outcome

subjectOutcomeClosesConsumer :
  (outcome : Quotient.SubjectObservation) →
  Sequential.OutcomePossible
    (allCompatible tt)
    Costed.subjectBundle
    outcome →
  ∀ left right →
    subjectRefinedFibre outcome left →
    subjectRefinedFibre outcome right →
    subjectConsumer left ≡ subjectConsumer right
subjectOutcomeClosesConsumer outcome possible left right leftRefined rightRefined =
  trans (proj₂ leftRefined) (sym (proj₂ rightRefined))

historyOutcomeClosesConsumer :
  (outcome : Quotient.HistoryObservation) →
  Sequential.OutcomePossible
    (allCompatible tt)
    Costed.historyBundle
    outcome →
  ∀ left right →
    historyRefinedFibre outcome left →
    historyRefinedFibre outcome right →
    historyConsumer left ≡ historyConsumer right
historyOutcomeClosesConsumer outcome possible left right leftRefined rightRefined =
  trans (proj₂ leftRefined) (sym (proj₂ rightRefined))

------------------------------------------------------------------------
-- Full-world identity is deliberately not required at terminal closure.
------------------------------------------------------------------------

data ConsumerClosurePromotesWorldIdentity : Set where

data OneShotSubjectPlanPromotesHistoryClosure : Set where

data OneShotHistoryPlanPromotesSubjectClosure : Set where

data ImpossibleOutcomePromotesContinuation : Set where

consumerClosureDoesNotPromoteWorldIdentity :
  ConsumerClosurePromotesWorldIdentity → ⊥
consumerClosureDoesNotPromoteWorldIdentity ()

subjectPlanDoesNotPromoteHistoryClosure :
  OneShotSubjectPlanPromotesHistoryClosure → ⊥
subjectPlanDoesNotPromoteHistoryClosure ()

historyPlanDoesNotPromoteSubjectClosure :
  OneShotHistoryPlanPromotesSubjectClosure → ⊥
historyPlanDoesNotPromoteSubjectClosure ()

impossibleOutcomeDoesNotPromoteContinuation :
  ImpossibleOutcomePromotesContinuation → ⊥
impossibleOutcomeDoesNotPromoteContinuation ()

record DrugCategoryAdaptiveQuotientExperimentBoundary : Set where
  constructor drugCategoryAdaptiveQuotientExperimentBoundary
  field
    selectedProbeCanRefineLiveFibre : Bool
    selectedProbeCanRefineLiveFibreIsTrue :
      selectedProbeCanRefineLiveFibre ≡ true
    subjectProbeCanCloseSubjectConsumer : Bool
    subjectProbeCanCloseSubjectConsumerIsTrue :
      subjectProbeCanCloseSubjectConsumer ≡ true
    historyProbeCanCloseHistoryConsumer : Bool
    historyProbeCanCloseHistoryConsumerIsTrue :
      historyProbeCanCloseHistoryConsumer ≡ true
    terminalClosureRequiresWholeWorldIdentity : Bool
    terminalClosureRequiresWholeWorldIdentityIsFalse :
      terminalClosureRequiresWholeWorldIdentity ≡ false
    oneProbeClosesEveryFineConsumer : Bool
    oneProbeClosesEveryFineConsumerIsFalse :
      oneProbeClosesEveryFineConsumer ≡ false

canonicalDrugCategoryAdaptiveQuotientExperimentBoundary :
  DrugCategoryAdaptiveQuotientExperimentBoundary
canonicalDrugCategoryAdaptiveQuotientExperimentBoundary =
  drugCategoryAdaptiveQuotientExperimentBoundary
    true refl true refl true refl false refl false refl
