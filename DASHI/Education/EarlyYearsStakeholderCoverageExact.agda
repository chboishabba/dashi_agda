module DASHI.Education.EarlyYearsStakeholderCoverageExact where

open import DASHI.Core.Prelude
import DASHI.Core.ActiveObligationEvidenceFibreExact as Active
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.RequiredAxisSupportSquareExact as Required
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as Join

data StakeholderAxis : Set where
  professionalAxis familyAxis childAxis communityAxis : StakeholderAxis

data EvidenceStage : Set where
  professionalPilot familyJoined childJoined communityJoined : EvidenceStage

data EarlyYearsClaim : Set where
  professionalPracticeClaim familyExperienceClaim childExperienceClaim communityExperienceClaim : EarlyYearsClaim

data Never : Set where

ClaimRequires : EvidenceStage → EarlyYearsClaim → StakeholderAxis → Set
ClaimRequires _ professionalPracticeClaim professionalAxis = ⊤
ClaimRequires _ familyExperienceClaim professionalAxis = ⊤
ClaimRequires _ familyExperienceClaim familyAxis = ⊤
ClaimRequires _ childExperienceClaim professionalAxis = ⊤
ClaimRequires _ childExperienceClaim familyAxis = ⊤
ClaimRequires _ childExperienceClaim childAxis = ⊤
ClaimRequires _ communityExperienceClaim professionalAxis = ⊤
ClaimRequires _ communityExperienceClaim communityAxis = ⊤
ClaimRequires _ _ _ = Never

positive : Required.SupportSquare
positive = Required.supportSquare true false

missing : Required.SupportSquare
missing = Required.supportSquare false false

EvidenceAt : EvidenceStage → EarlyYearsClaim → StakeholderAxis → Required.SupportSquare
EvidenceAt professionalPilot _ professionalAxis = positive
EvidenceAt familyJoined _ professionalAxis = positive
EvidenceAt familyJoined _ familyAxis = positive
EvidenceAt childJoined _ professionalAxis = positive
EvidenceAt childJoined _ familyAxis = positive
EvidenceAt childJoined _ childAxis = positive
EvidenceAt communityJoined _ professionalAxis = positive
EvidenceAt communityJoined _ communityAxis = positive
EvidenceAt _ _ _ = missing

stakeholderObligations : Active.ActiveObligationFamily EvidenceStage EarlyYearsClaim StakeholderAxis
stakeholderObligations = Active.activeObligationFamily ClaimRequires EvidenceAt

professionalPilotResolvesProfessionalPractice :
  Active.ResolvedFor stakeholderObligations professionalPilot professionalPracticeClaim
professionalPilotResolvesProfessionalPractice professionalAxis tt = refl , refl
professionalPilotResolvesProfessionalPractice familyAxis ()
professionalPilotResolvesProfessionalPractice childAxis ()
professionalPilotResolvesProfessionalPractice communityAxis ()

missingFamilyAtProfessionalPilot :
  Active.MissingActiveObligation stakeholderObligations professionalPilot familyExperienceClaim
missingFamilyAtProfessionalPilot = Active.missingActiveObligation familyAxis tt (refl , refl)

professionalPilotCannotEstablishFamilyExperience :
  Active.ResolvedFor stakeholderObligations professionalPilot familyExperienceClaim → ⊥
professionalPilotCannotEstablishFamilyExperience =
  Active.missingActiveObligationBlocksResolution missingFamilyAtProfessionalPilot

familyJoinedResolvesFamilyExperience :
  Active.ResolvedFor stakeholderObligations familyJoined familyExperienceClaim
familyJoinedResolvesFamilyExperience professionalAxis tt = refl , refl
familyJoinedResolvesFamilyExperience familyAxis tt = refl , refl
familyJoinedResolvesFamilyExperience childAxis ()
familyJoinedResolvesFamilyExperience communityAxis ()

missingChildAtFamilyJoined :
  Active.MissingActiveObligation stakeholderObligations familyJoined childExperienceClaim
missingChildAtFamilyJoined = Active.missingActiveObligation childAxis tt (refl , refl)

familyEvidenceStillCannotEstablishChildExperience :
  Active.ResolvedFor stakeholderObligations familyJoined childExperienceClaim → ⊥
familyEvidenceStillCannotEstablishChildExperience =
  Active.missingActiveObligationBlocksResolution missingChildAtFamilyJoined

childJoinedResolvesChildExperience :
  Active.ResolvedFor stakeholderObligations childJoined childExperienceClaim
childJoinedResolvesChildExperience professionalAxis tt = refl , refl
childJoinedResolvesChildExperience familyAxis tt = refl , refl
childJoinedResolvesChildExperience childAxis tt = refl , refl
childJoinedResolvesChildExperience communityAxis ()

data FamilySituation : Set where situationA situationB : FamilySituation

professionalSummary : FamilySituation → Bool
professionalSummary situationA = true
professionalSummary situationB = true

familyExperience : FamilySituation → Bool
familyExperience situationA = false
familyExperience situationB = true

familyExperienceDiffers : familyExperience situationA ≡ familyExperience situationB → ⊥
familyExperienceDiffers ()

professionalFamilyCollision : Consumer.ConsumerRelevantCollision professionalSummary familyExperience
professionalFamilyCollision =
  Consumer.consumer-relevant-collision situationA situationB refl familyExperienceDiffers

professionalSurfaceCannotServeFamilyExperience :
  Consumer.ConsumerSufficient professionalSummary familyExperience → ⊥
professionalSurfaceCannotServeFamilyExperience =
  Consumer.coarseCollisionBlocksSufficiency professionalFamilyCollision

anyFamilyExperienceSufficientObserverMustSplitProfessionalCollision :
  ∀ {Surface : Set} (observe : FamilySituation → Surface) →
  Consumer.ConsumerSufficient observe familyExperience →
  observe situationA ≡ observe situationB → ⊥
anyFamilyExperienceSufficientObserverMustSplitProfessionalCollision observe sufficient =
  Consumer.everySufficientObserverSeparatesRelevantCollision professionalFamilyCollision sufficient

familyResidual : FamilySituation → Bool
familyResidual = familyExperience

familyResidualRepair : Consumer.ResidualRepair professionalSummary familyResidual familyExperience
familyResidualRepair = Consumer.residual-repair (λ left right samePair → cong proj₂ samePair)

familyResidualMustSplitProfessionalCollision :
  familyResidual situationA ≡ familyResidual situationB → ⊥
familyResidualMustSplitProfessionalCollision =
  Consumer.residualMustSeparateRelevantCollision professionalFamilyCollision familyResidualRepair

professionalPlusFamilyStrictlyRefinesProfessional :
  Observer.StrictRefinement professionalSummary (Observer.pairObserver professionalSummary familyResidual)
professionalPlusFamilyStrictlyRefinesProfessional =
  Consumer.consumerRelevantResidualGivesStrictRefinement professionalFamilyCollision familyResidualRepair

record StakeholderCoverageBoundary : Set where
  constructor stakeholderCoverageBoundary
  field
    claimRequirementsAreStakeholderIndexed : Bool
    missingInactiveStakeholderInvalidatesClaim : Bool
    missingActiveStakeholderBlocksDirectClaim : Bool
    professionalEvidenceAloneEstablishesFamilyExperience : Bool
    familyEvidenceAloneEstablishesChildExperience : Bool
    addingRequiredStakeholderCanCloseObligation : Bool
    anySufficientFamilyObserverMustSplitRelevantProfessionalCollision : Bool
    jointCoverageMeansWorldCompleteness : Bool

open StakeholderCoverageBoundary public

canonicalStakeholderCoverageBoundary : StakeholderCoverageBoundary
canonicalStakeholderCoverageBoundary =
  stakeholderCoverageBoundary true false true false false true true false
