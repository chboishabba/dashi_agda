module DASHI.Governance.CybersynAuthorityFeedbackExact where

-- Finite DASHI extension: feedback, observed outcomes and authorisation.
-- Attribution: Docs/SourceAttributionPolicy.md.
-- Cybersyn and VSM are context; mathematical examples are DASHI-original.
-- Community consultation is not automatically consent, jurisdiction or
-- culturally situated authority.  These require distinct source receipts.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.CybersynGlobalViabilityMaxCutExact as Cyber
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.PluralEpistemicOperationalClosureExact as Plural
import DASHI.Governance.CyberneticClinicalInstitutionalRepairBridge as Governance

data LocalState : Set where
  accessObstructed : LocalState
  imposedBuild : LocalState
  negotiatedRepair : LocalState

data LocalAction : Set where
  postpone : LocalAction
  impose : LocalAction
  repairWithAuthority : LocalAction

data ActorObservation : Set where
  headlineOnly : ActorObservation
  harmReported : ActorObservation
  repairedAndAccepted : ActorObservation

data RealisedOutcome : Set where
  projectDelayed : RealisedOutcome
  projectProceedsWithoutRepair : RealisedOutcome
  projectProceedsWithRepair : RealisedOutcome

stateStep : Nat → LocalState → LocalAction → LocalState
stateStep _ s postpone = s
stateStep _ _ impose = imposedBuild
stateStep _ _ repairWithAuthority = negotiatedRepair

observes : Cyber.ActorRole → Nat → LocalState → ActorObservation
observes Cyber.investor _ _ = headlineOnly
observes Cyber.lender _ _ = headlineOnly
observes Cyber.government _ _ = headlineOnly
observes Cyber.affectedCommunity _ accessObstructed = harmReported
observes Cyber.affectedCommunity _ imposedBuild = harmReported
observes Cyber.affectedCommunity _ negotiatedRepair = repairedAndAccepted
observes Cyber.worker _ accessObstructed = harmReported
observes Cyber.worker _ imposedBuild = harmReported
observes Cyber.worker _ negotiatedRepair = repairedAndAccepted
observes Cyber.insurer _ _ = headlineOnly
observes Cyber.ecologicalSteward _ accessObstructed = harmReported
observes Cyber.ecologicalSteward _ imposedBuild = harmReported
observes Cyber.ecologicalSteward _ negotiatedRepair = repairedAndAccepted
observes Cyber.coordinatingFederation _ accessObstructed = harmReported
observes Cyber.coordinatingFederation _ imposedBuild = harmReported
observes Cyber.coordinatingFederation _ negotiatedRepair = repairedAndAccepted

outcome : Nat → LocalState → RealisedOutcome
outcome _ accessObstructed = projectDelayed
outcome _ imposedBuild = projectProceedsWithoutRepair
outcome _ negotiatedRepair = projectProceedsWithRepair

-- Toy authority flag is a simulated permission, not an assertion of actual
-- consent, Indigenous standing or legal jurisdiction.
localAuthority : Cyber.ActorRole → Nat → LocalState → Bool
localAuthority Cyber.affectedCommunity _ negotiatedRepair = true
localAuthority Cyber.coordinatingFederation _ negotiatedRepair = true
localAuthority _ _ _ = false

choose : Cyber.ActorRole → Nat → ActorObservation → LocalAction
choose Cyber.affectedCommunity _ harmReported = repairWithAuthority
choose Cyber.coordinatingFederation _ harmReported = repairWithAuthority
choose _ _ _ = postpone

act : Cyber.ActorRole → Nat → LocalState → LocalState
act a t s = stateStep t s (choose a t (observes a t s))

localCybersyn : Cyber.TimeIndexedCybersyn
  LocalState LocalAction ActorObservation RealisedOutcome Bool
localCybersyn = record
  { step = stateStep
  ; observe = observes
  ; realisedEffect = outcome
  ; hasAuthority = localAuthority
  ; intervention = choose
  ; outcomeAfter = act
  ; outcomeAfterLaw = λ a t s → refl
  }

-- Different observers have different observation fibres; signals are never
-- treated as omniscient views of the world.
investorSeesHeadline : (t : Nat) (s : LocalState) →
  observes Cyber.investor t s ≡ headlineOnly
investorSeesHeadline t s = refl

communitySeesUnrepairedHarm : (t : Nat) →
  observes Cyber.affectedCommunity t imposedBuild ≡ harmReported
communitySeesUnrepairedHarm t = refl

-- A material correction can change operation; mere observing/announcement
-- cannot establish that such correction has occurred.
communityCorrectionActuates : (t : Nat) →
  act Cyber.affectedCommunity t accessObstructed ≡ negotiatedRepair
communityCorrectionActuates t = refl

investorOnlyObservationDoesNotActuate : (t : Nat) →
  act Cyber.investor t accessObstructed ≡ accessObstructed
investorOnlyObservationDoesNotActuate t = refl

-- The same investor report covers two genuinely different realised effects.
sameInvestorReport : (t : Nat) →
  observes Cyber.investor t imposedBuild ≡
  observes Cyber.investor t negotiatedRepair
sameInvestorReport t = refl

effectDistinction : (t : Nat) →
  outcome t imposedBuild ≡ outcome t negotiatedRepair → ⊥
effectDistinction t ()

investorReportCannotRecoverEffect : (t : Nat) →
  NonFactor.FactorsThrough
    (observes Cyber.investor t) (outcome t) → ⊥
investorReportCannotRecoverEffect t =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      imposedBuild negotiatedRepair
      (sameInvestorReport t) (effectDistinction t))

-- Consultation/reporting can be true without authority, while a distinct
-- operationally corrected state carries the simulated authority flag.
consultationObserved : LocalState → Bool
consultationObserved _ = true

consultedButNotAuthorised :
  consultationObserved imposedBuild ≡ true
consultedButNotAuthorised = refl

consultationDoesNotProvideAuthority :
  localAuthority Cyber.affectedCommunity 0 imposedBuild ≡ false
consultationDoesNotProvideAuthority = refl

repairCarriesSimulatedAuthority :
  localAuthority Cyber.affectedCommunity 0 negotiatedRepair ≡ true
repairCarriesSimulatedAuthority = refl

-- Distinct from real community-specific permission: a legitimate governance
-- certificate must be provided from a source-appropriate producer.
record GovernanceAdmission : Set where
  constructor governanceAdmission
  field
    communityRecognised : Bool
    meaningfulControl : Bool
    consentSourceChecked : Bool
    appealAndRepair : Bool

open GovernanceAdmission public

governanceAdmitted : GovernanceAdmission → Bool
governanceAdmitted g with communityRecognised g
... | false = false
... | true with meaningfulControl g
...   | false = false
...   | true with consentSourceChecked g
...     | false = false
...     | true = appealAndRepair g

mereConsultation : GovernanceAdmission
mereConsultation = governanceAdmission true false false false

consultationNotAdmission : governanceAdmitted mereConsultation ≡ false
consultationNotAdmission = refl

-- Source-owned cross-check: institutional report alone does not supply an
-- affected community outcome or replace System 5 democratic authority.
pluralOwner : Plural.PluralEvidenceAssessment
pluralOwner = Plural.canonicalPluralEvidenceAssessment

systemFiveOwner : Governance.GovernanceGateRow
systemFiveOwner = Governance.cybersynSystemFiveRow
