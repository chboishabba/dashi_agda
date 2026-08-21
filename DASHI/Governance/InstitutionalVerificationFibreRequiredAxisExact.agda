module DASHI.Governance.InstitutionalVerificationFibreRequiredAxisExact where

------------------------------------------------------------------------
-- VERIFICATION FIBRE / REQUIRED-AXIS LEGAL ADEQUACY
--
-- Thin specialization of ObserverRefinement, IntersectionalNonFactorability and
-- RequiredObserverAxisJoinAdequacy.  Knowing the legal question is not the same
-- thing as having a decision-safe verification observer for whether a purported
-- saving branch is genuinely live.  Likewise, reweighting a flat subject label
-- cannot recover a relational access axis that the carrier erased.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as Required
import DASHI.Governance.ContestabilityAccessCostExact as Contestability
import DASHI.Governance.InstitutionalNoticeActuationCulpabilityExact as Notice

------------------------------------------------------------------------
-- 1. A second fibre: verification of the purported saving branch.
------------------------------------------------------------------------

data VerificationState : Set where
  savingBranchActuallyDead savingBranchActuallyLive : VerificationState

data VerificationQuestionSurface : Set where
  isThereSavingAuthorityQuestion : VerificationQuestionSurface

data VerificationAnswer : Set where
  verifiedDead verifiedLive : VerificationAnswer

questionObserver :
  Observer.Observer VerificationState VerificationQuestionSurface
questionObserver _ = isThereSavingAuthorityQuestion

authoritativeVerificationObserver :
  Observer.Observer VerificationState VerificationAnswer
authoritativeVerificationObserver savingBranchActuallyDead = verifiedDead
authoritativeVerificationObserver savingBranchActuallyLive = verifiedLive

verificationDecision : VerificationState → Notice.LegalDecision
verificationDecision savingBranchActuallyDead = Notice.withdrawDecision
verificationDecision savingBranchActuallyLive = Notice.persistDecision

VerificationDecisionSafe :
  ∀ {Observation : Set} →
  Observer.Observer VerificationState Observation → Set
VerificationDecisionSafe observe =
  ∀ x y → observe x ≡ observe y → verificationDecision x ≡ verificationDecision y

questionObserverNotDecisionSafe : VerificationDecisionSafe questionObserver → ⊥
questionObserverNotDecisionSafe safe with
  safe savingBranchActuallyDead savingBranchActuallyLive refl
... | ()

authoritativeVerificationDecisionSafe :
  VerificationDecisionSafe authoritativeVerificationObserver
authoritativeVerificationDecisionSafe savingBranchActuallyDead savingBranchActuallyDead same = refl
authoritativeVerificationDecisionSafe savingBranchActuallyDead savingBranchActuallyLive ()
authoritativeVerificationDecisionSafe savingBranchActuallyLive savingBranchActuallyDead ()
authoritativeVerificationDecisionSafe savingBranchActuallyLive savingBranchActuallyLive same = refl

questionToVerificationStrictRefinement :
  Observer.StrictRefinement questionObserver authoritativeVerificationObserver
questionToVerificationStrictRefinement =
  Observer.strictRefinement
    (λ x y same → refl)
    savingBranchActuallyDead
    savingBranchActuallyLive
    refl
    (λ ())

-- The subject may know exactly which question needs answering while the
-- verification fibre still contains opposite action states.
record QuestionKnownVerificationUnresolved : Set where
  constructor questionKnownVerificationUnresolved
  field
    knownQuestion : VerificationQuestionSurface
    unresolvedCollision : Observer.ObserverCollision questionObserver
    decisionUnsafe : VerificationDecisionSafe questionObserver → ⊥

canonicalQuestionKnownVerificationUnresolved :
  QuestionKnownVerificationUnresolved
canonicalQuestionKnownVerificationUnresolved =
  questionKnownVerificationUnresolved
    isThereSavingAuthorityQuestion
    (Observer.observerCollision
      savingBranchActuallyDead
      savingBranchActuallyLive
      refl
      (λ ()))
    questionObserverNotDecisionSafe

------------------------------------------------------------------------
-- 2. Formal verification availability still does not give affordable access.
------------------------------------------------------------------------

verificationPathFormallyAvailable :
  Contestability.FormallyAvailableContestability
    Contestability.finiteContestabilityInterface
    DASHI.Governance.AsymmetricLegibilityContestabilityExact.case0
verificationPathFormallyAvailable = Contestability.finiteFormalAvailability

verificationPathNotAffordableInCanonicalBudget :
  Contestability.AffordableContestability
    Contestability.finiteCost Contestability.finiteBudget → ⊥
verificationPathNotAffordableInCanonicalBudget =
  Contestability.formalAvailabilityDoesNotEstablishAffordability

record VerificationClosureGap : Set where
  constructor verificationClosureGap
  field
    questionKnown : QuestionKnownVerificationUnresolved
    formalPathExists : Set
    formalPathWitness : formalPathExists
    affordablePathImpossible :
      Contestability.AffordableContestability
        Contestability.finiteCost Contestability.finiteBudget → ⊥

canonicalVerificationClosureGap : VerificationClosureGap
canonicalVerificationClosureGap =
  verificationClosureGap
    canonicalQuestionKnownVerificationUnresolved
    ⊤
    tt
    verificationPathNotAffordableInCanonicalBudget

------------------------------------------------------------------------
-- 3. Intersectional representation, not downstream demographic adjustment.
--
-- The flat observer sees the same subject label.  The fine carrier retains the
-- institutional relation/access configuration and communication modality.
------------------------------------------------------------------------

data SituatedAccessState : Set where
  lowAccessAsynchronous highAccessInteractive : SituatedAccessState

data FlatSubjectLabel : Set where
  sameLaySubjectLabel : FlatSubjectLabel

data RelationAccessAxis : Set where
  lowVerificationAccess highVerificationAccess : RelationAccessAxis

data CommunicationAxis : Set where
  asynchronousNotice interactiveTeachBack : CommunicationAxis

flatSubjectObserver : SituatedAccessState → FlatSubjectLabel
flatSubjectObserver _ = sameLaySubjectLabel

relationAccessAxis : SituatedAccessState → RelationAccessAxis
relationAccessAxis lowAccessAsynchronous = lowVerificationAccess
relationAccessAxis highAccessInteractive = highVerificationAccess

communicationAxis : SituatedAccessState → CommunicationAxis
communicationAxis lowAccessAsynchronous = asynchronousNotice
communicationAxis highAccessInteractive = interactiveTeachBack

relationAccessDiffers :
  relationAccessAxis lowAccessAsynchronous
  ≡ relationAccessAxis highAccessInteractive → ⊥
relationAccessDiffers ()

flatErasesRelationAccess :
  NF.NonFactorabilityWitness flatSubjectObserver relationAccessAxis
flatErasesRelationAccess =
  NF.nonFactorabilityWitness
    lowAccessAsynchronous
    highAccessInteractive
    refl
    relationAccessDiffers

flatAdjustmentCannotRecoverRelationAccess :
  NF.FactorsThrough flatSubjectObserver relationAccessAxis → ⊥
flatAdjustmentCannotRecoverRelationAccess =
  NF.witnessRulesOutEveryFlatFactorisation flatErasesRelationAccess

flatCannotRetainBothRequiredRelationalAxes :
  Required.RetainsBothRequiredAxes
    flatSubjectObserver
    relationAccessAxis
    communicationAxis → ⊥
flatCannotRetainBothRequiredRelationalAxes =
  Required.leftAxisDefectBlocksRetainingBoth flatErasesRelationAccess

jointRelationalObserver :
  SituatedAccessState → RelationAccessAxis × CommunicationAxis
jointRelationalObserver = Required.jointAxis relationAccessAxis communicationAxis

jointRelationalObserverRetainsAccess :
  Required.RetainsAxis jointRelationalObserver relationAccessAxis
jointRelationalObserverRetainsAccess =
  Required.jointRetainsLeft relationAccessAxis communicationAxis

jointRelationalObserverRetainsCommunication :
  Required.RetainsAxis jointRelationalObserver communicationAxis
jointRelationalObserverRetainsCommunication =
  Required.jointRetainsRight relationAccessAxis communicationAxis

record InstitutionalVerificationRequiredAxisBoundary : Set where
  constructor institutionalVerificationRequiredAxisBoundary
  field
    knowingQuestionMeansVerificationClosed : Bool
    formalVerificationPathMeansAffordableVerification : Bool
    flatSubjectAdjustmentRecoversMissingRelation : Bool
    oneStrongAxisCompensatesForMissingRequiredAxis : Bool
    relationalAxesMustBeRepresentedInCarrier : Bool
    authoritativeVerificationCanStrictlyRefineQuestionSurface : Bool

canonicalInstitutionalVerificationRequiredAxisBoundary :
  InstitutionalVerificationRequiredAxisBoundary
canonicalInstitutionalVerificationRequiredAxisBoundary =
  institutionalVerificationRequiredAxisBoundary
    false false false false true true
