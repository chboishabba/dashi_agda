module DASHI.Governance.DrugCategoryCostedQuotientDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Governance.DrugCategoryExplicitConsumerQuotientExact as Quotient
import DASHI.Governance.DrugCategoryConsumerQuotientRefinementExact as Refinement

------------------------------------------------------------------------
-- COSTED QUOTIENT DISCRIMINATOR
--
-- Failed descent through the clinical quotient is turned into an explicit
-- experiment bundle and then into the repository's canonical costed
-- information-move language.  Only probes that actually separate the current
-- collision receive a resolving witness.
------------------------------------------------------------------------

data ProbeKind : Set where
  subjectProbe
  historyProbe
  authorityProbe
  materialBenefitProbe
  sovereigntyProbe
  : ProbeKind

probeCost : ProbeKind → Nat
probeCost subjectProbe = 1
probeCost historyProbe = 2
probeCost authorityProbe = 3
probeCost materialBenefitProbe = 3
probeCost sovereigntyProbe = 4

subjectBundle : Discriminator.ExperimentBundle Quotient.TranslationState
subjectBundle = Discriminator.experimentBundle
  Quotient.SubjectObservation
  Quotient.subjectObserver
  (probeCost subjectProbe)
  "observe originating/represented subject-position"
  "subject-position coding/calibration must preserve originating-vs-represented distinction"

historyBundle : Discriminator.ExperimentBundle Quotient.TranslationState
historyBundle = Discriminator.experimentBundle
  Quotient.HistoryObservation
  Quotient.historyObserver
  (probeCost historyProbe)
  "observe historical classifier-position"
  "history coding/calibration must preserve erased-vs-retained/reintroduced distinction"

subjectCollision : Discriminator.CurrentObserverCollision Quotient.clinicalObserver
subjectCollision = Discriminator.currentObserverCollision
  Quotient.stateLegalState Quotient.livedSubjectState refl

historyCollision : Discriminator.CurrentObserverCollision Quotient.clinicalObserver
historyCollision = Discriminator.currentObserverCollision
  Quotient.stateLegalState Quotient.biomedicalState refl

subjectBundleSeparates :
  Discriminator.BundleSeparates subjectBundle
    Quotient.stateLegalState Quotient.livedSubjectState
subjectBundleSeparates = Discriminator.bundleSeparates
  Quotient.subjectStateLivedNotEquivalent

historyBundleSeparates :
  Discriminator.BundleSeparates historyBundle
    Quotient.stateLegalState Quotient.biomedicalState
historyBundleSeparates = Discriminator.bundleSeparates
  Quotient.historyStateBiomedicalNotEquivalent

subjectLanguageExtension :
  Discriminator.DiscriminatingLanguageExtension Quotient.clinicalObserver
subjectLanguageExtension = Discriminator.discriminatingLanguageExtension
  subjectCollision subjectBundle subjectBundleSeparates

historyLanguageExtension :
  Discriminator.DiscriminatingLanguageExtension Quotient.clinicalObserver
historyLanguageExtension = Discriminator.discriminatingLanguageExtension
  historyCollision historyBundle historyBundleSeparates

------------------------------------------------------------------------
-- Prospective menu.  Remaining probes are candidates, not asserted separators
-- for this finite fixture.
------------------------------------------------------------------------

authorityMove : Choice.InformationMove
authorityMove = Choice.informationMove
  Choice.takeMeasurement (probeCost authorityProbe)
  "probe classification-authority issuer/standing"
  "authority-provenance and coding resources"
  "requires an authority-sensitive live collision"

materialBenefitMove : Choice.InformationMove
materialBenefitMove = Choice.informationMove
  Choice.takeMeasurement (probeCost materialBenefitProbe)
  "probe benefit/externality routing"
  "material-flow measurement resources"
  "requires a material-benefit-sensitive live collision"

sovereigntyMove : Choice.InformationMove
sovereigntyMove = Choice.informationMove
  Choice.takeMeasurement (probeCost sovereigntyProbe)
  "probe sovereign permission/authority"
  "community-governed authority evidence resources"
  "requires a sovereignty-sensitive live collision and valid authority protocol"

subjectMove : Choice.InformationMove
subjectMove = Discriminator.bundleInformationMove subjectBundle

historyMove : Choice.InformationMove
historyMove = Discriminator.bundleInformationMove historyBundle

------------------------------------------------------------------------
-- Actionability problems: resolution is collision-specific.
------------------------------------------------------------------------

data SubjectObstruction : Set where subjectStillCollapsed : SubjectObstruction

data HistoryObstruction : Set where historyStillCollapsed : HistoryObstruction

subjectProblem : Choice.ActionabilityProblem
subjectProblem = Choice.actionabilityProblem
  SubjectObstruction
  subjectStillCollapsed
  (λ move obstruction → move ≡ subjectMove)
  "clinical quotient still collapses state/legal and lived-subject states for the subject-position consumer"
  "originating-subject authority consumer"
  "subject-position interpretation requires independent authority/voice receipt"

historyProblem : Choice.ActionabilityProblem
historyProblem = Choice.actionabilityProblem
  HistoryObstruction
  historyStillCollapsed
  (λ move obstruction → move ≡ historyMove)
  "clinical quotient still collapses state/legal and biomedical states for the historical-continuity consumer"
  "historical-continuity consumer"
  "historical classification requires source/provenance receipt"

subjectResolvingMove : Choice.ResolvingMove subjectProblem
subjectResolvingMove = Choice.resolvingMove subjectMove refl

historyResolvingMove : Choice.ResolvingMove historyProblem
historyResolvingMove = Choice.resolvingMove historyMove refl

data DeclaredProbeMove : Choice.InformationMove → Set where
  declaredSubject : DeclaredProbeMove subjectMove
  declaredHistory : DeclaredProbeMove historyMove
  declaredAuthority : DeclaredProbeMove authorityMove
  declaredMaterial : DeclaredProbeMove materialBenefitMove
  declaredSovereignty : DeclaredProbeMove sovereigntyMove

subjectMinimal :
  (alternative : Choice.InformationMove) →
  DeclaredProbeMove alternative →
  Choice.Resolves subjectProblem alternative
    (Choice.currentObstruction subjectProblem) →
  Choice.cost subjectMove ≤ Choice.cost alternative
subjectMinimal .subjectMove declared refl = s≤s z≤n

historyMinimal :
  (alternative : Choice.InformationMove) →
  DeclaredProbeMove alternative →
  Choice.Resolves historyProblem alternative
    (Choice.currentObstruction historyProblem) →
  Choice.cost historyMove ≤ Choice.cost alternative
historyMinimal .historyMove declared refl = s≤s (s≤s z≤n)

subjectCheapestResolving :
  Choice.CheapestResolvingMove subjectProblem DeclaredProbeMove
subjectCheapestResolving = Choice.cheapestResolvingMove
  subjectResolvingMove
  declaredSubject
  subjectMinimal
  "among the declared menu, only the subject probe carries a subject-obstruction resolution witness"

historyCheapestResolving :
  Choice.CheapestResolvingMove historyProblem DeclaredProbeMove
historyCheapestResolving = Choice.cheapestResolvingMove
  historyResolvingMove
  declaredHistory
  historyMinimal
  "among the declared menu, only the history probe carries a history-obstruction resolution witness"

------------------------------------------------------------------------
-- BIDI weld back to quotient-refinement requests.
------------------------------------------------------------------------

subjectFailedDescentSelectsSubjectProbe :
  Refinement.requiredRefinement Refinement.subjectConsumerDemand
  ≡ Refinement.addSubjectPosition
subjectFailedDescentSelectsSubjectProbe = refl

historyFailedDescentSelectsHistoryProbe :
  Refinement.requiredRefinement Refinement.historyConsumerDemand
  ≡ Refinement.addHistoricalPosition
historyFailedDescentSelectsHistoryProbe = refl

data CheapestProbePromotesScientificallyBest : Set where

data CandidateProbePromotesResolution : Set where

data PairwiseSeparatorPromotesWholeStateIdentification : Set where

data CostPromotesEthicalAuthority : Set where

cheapestDoesNotPromoteScientificallyBest : CheapestProbePromotesScientificallyBest → ⊥
cheapestDoesNotPromoteScientificallyBest ()

candidateDoesNotPromoteResolution : CandidateProbePromotesResolution → ⊥
candidateDoesNotPromoteResolution ()

pairwiseDoesNotPromoteWholeState : PairwiseSeparatorPromotesWholeStateIdentification → ⊥
pairwiseDoesNotPromoteWholeState ()

costDoesNotPromoteEthicalAuthority : CostPromotesEthicalAuthority → ⊥
costDoesNotPromoteEthicalAuthority ()

record DrugCategoryCostedQuotientDiscriminatorBoundary : Set where
  constructor drugCategoryCostedQuotientDiscriminatorBoundary
  field
    failedDescentCanBecomeExperimentBundle : Bool
    failedDescentCanBecomeExperimentBundleIsTrue : failedDescentCanBecomeExperimentBundle ≡ true
    separatingBundleCanBecomeCostedInformationMove : Bool
    separatingBundleCanBecomeCostedInformationMoveIsTrue : separatingBundleCanBecomeCostedInformationMove ≡ true
    menuCanContainNonresolvingCandidateProbes : Bool
    menuCanContainNonresolvingCandidateProbesIsTrue : menuCanContainNonresolvingCandidateProbes ≡ true
    cheapestDeclaredResolvingMoveIsScientificallyBestTheory : Bool
    cheapestDeclaredResolvingMoveIsScientificallyBestTheoryIsFalse : cheapestDeclaredResolvingMoveIsScientificallyBestTheory ≡ false
    pairwiseSeparationEqualsWholeSemanticRecovery : Bool
    pairwiseSeparationEqualsWholeSemanticRecoveryIsFalse : pairwiseSeparationEqualsWholeSemanticRecovery ≡ false

canonicalDrugCategoryCostedQuotientDiscriminatorBoundary :
  DrugCategoryCostedQuotientDiscriminatorBoundary
canonicalDrugCategoryCostedQuotientDiscriminatorBoundary =
  drugCategoryCostedQuotientDiscriminatorBoundary
    true refl true refl true refl false refl false refl
