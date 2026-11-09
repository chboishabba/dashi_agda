module DASHI.Cognition.CCDCOEP3SameOperationIndexedAdmissionExact where

------------------------------------------------------------------------
-- SAME-OPERATION, SIX-STAGE SOURCE-INDEXED COGNITIVE-WARFARE ADMISSION
--
-- Attribution: GCC original media and policy correspondence 1993;
-- 1998 API Global Climate Science Communications Team proposal is
-- a DIFFERENT original source, author set and time. The 2017
-- Supran/Oreskes analysis is an independent published corpus.
-- Rensberger, Hansen and film creators retain original authorship.
--
-- DASHI only proves dependent-type source/nonpromotion obligations.
-- No source bytes, calibrated effects, hostile purpose or original
-- historical operation witness is manufactured by this module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Core.ObserverRefinementLatticeExact as Observer

data OriginalCase : Set where
  gcc1993 : OriginalCase
  apiProposal1998 : OriginalCase
  exxonCorpus2017 : OriginalCase
  fictionalArt : OriginalCase

data EvidenceStage : Set where
  originalIntervention : EvidenceStage
  recipientExposure : EvidenceStage
  cognitiveMechanism : EvidenceStage
  causalDiscrimination : EvidenceStage
  independentlySourcedIntent : EvidenceStage
  originalAttribution : EvidenceStage

-- Evidence is a proposition indexed by original case AND stage. In
-- particular E gcc1993 recipientExposure does not supply
-- E apiProposal1998 recipientExposure by definitional conversion.
-- An external instantiation must still justify original provenance.
record AdmitsOneOriginalCase
    (E : OriginalCase → EvidenceStage → Set)
    (c : OriginalCase) : Set where
  field
    intervention : E c originalIntervention
    exposure : E c recipientExposure
    mechanism : E c cognitiveMechanism
    causal : E c causalDiscrimination
    intent : E c independentlySourcedIntent
    attribution : E c originalAttribution

-- Reuse of an admitted operation can project evidence for its SAME
-- case and SAME stage, not evidence about a different campaign.
sameCaseExposure :
  (E : OriginalCase → EvidenceStage → Set)
  (c : OriginalCase) →
  AdmitsOneOriginalCase E c → E c recipientExposure
sameCaseExposure E c admitted =
  AdmitsOneOriginalCase.exposure admitted

sameCaseIntent :
  (E : OriginalCase → EvidenceStage → Set)
  (c : OriginalCase) →
  AdmitsOneOriginalCase E c → E c independentlySourcedIntent
sameCaseIntent E c admitted =
  AdmitsOneOriginalCase.intent admitted

gccCaseNot1998Proposal :
  gcc1993 ≡ apiProposal1998 → ⊥
gccCaseNot1998Proposal ()

gccCaseNot2017Corpus :
  gcc1993 ≡ exxonCorpus2017 → ⊥
gccCaseNot2017Corpus ()

originalCaseNotFiction :
  gcc1993 ≡ fictionalArt → ⊥
originalCaseNotFiction ()

exposureIsNotIntent :
  recipientExposure ≡ independentlySourcedIntent → ⊥
exposureIsNotIntent ()

sourceTextIsNotCausalEffect :
  originalIntervention ≡ causalDiscrimination → ⊥
sourceTextIsNotCausalEffect ()

data CaseStage (c : OriginalCase) : Set where
  caseStage : (stage : EvidenceStage) → CaseStage c

-- A claim can carry both dimensions without losing the distinction
-- between author/campaign identity and observation/effect stage.
indexedClaim : (c : OriginalCase) → (stage : EvidenceStage) → CaseStage c
indexedClaim c stage = caseStage stage

-- A projection across cases requires an explicit equality of cases.
transportCaseStage :
  {c d : OriginalCase} →
  c ≡ d → CaseStage c → CaseStage d
transportCaseStage refl x = x

-- There is no case-equality witness authorising transport of
-- 1993 GCC receipts into the 1998 API case.
noGCC1993ToAPI1998Identity :
  gcc1993 ≡ apiProposal1998 → ⊥
noGCC1993ToAPI1998Identity = gccCaseNot1998Proposal

-- This theorem does NOT assert all E are nontrivial: if callers set
-- every E c stage to the unit type, evidence still becomes trivial.
-- A scientific instance must supply externally verified, distinct,
-- source-indexed evidence predicates and original review receipts.

------------------------------------------------------------------------
-- CLOSED INVENTORY NEGATIVE CONTROL.
--
-- The source-located inventory currently admits a catalogue stage
-- for the 1993 GCC communication and 1998 API draft, and attribution
-- of the 2017 content study. It does NOT admit independently measured
-- audience exposure. This says nothing about future historical finds.
------------------------------------------------------------------------

data CurrentlyLocatedEvidence : OriginalCase → EvidenceStage → Set where
  gcc1993OriginalCatalogued :
    CurrentlyLocatedEvidence gcc1993 originalIntervention
  api1998ProposalCatalogued :
    CurrentlyLocatedEvidence apiProposal1998 originalIntervention
  exxon2017StudyAttributed :
    CurrentlyLocatedEvidence exxonCorpus2017 originalAttribution

currentGCCExposureUnavailable :
  CurrentlyLocatedEvidence gcc1993 recipientExposure → ⊥
currentGCCExposureUnavailable ()

currentAPIExposureUnavailable :
  CurrentlyLocatedEvidence apiProposal1998 recipientExposure → ⊥
currentAPIExposureUnavailable ()

selectedGCCDoesNotAdmitFullOperation :
  AdmitsOneOriginalCase CurrentlyLocatedEvidence gcc1993 → ⊥
selectedGCCDoesNotAdmitFullOperation admission =
  currentGCCExposureUnavailable
    (AdmitsOneOriginalCase.exposure admission)

selectedAPIDraftDoesNotAdmitFullOperation :
  AdmitsOneOriginalCase CurrentlyLocatedEvidence apiProposal1998 → ⊥
selectedAPIDraftDoesNotAdmitFullOperation admission =
  currentAPIExposureUnavailable
    (AdmitsOneOriginalCase.exposure admission)

-- These negative proofs concern the declared closed *inventory* only;
-- neither proves a historical absence of delivery, intention or impact.

------------------------------------------------------------------------
-- UNIVERSAL MISSING-GATE CUT (not restricted to a chosen inventory).
--
-- Unlike a theorem which only pattern matches a closed data inventory,
-- this works for EVERY externally selected indexed evidence predicate.
-- If ONE scientifically required stage is uninhabited for a particular
-- case, full operation admission for precisely that case is impossible.
-- A newly located genuine receipt can change the premise, not the law.
------------------------------------------------------------------------

blockedByMissingExposure :
  (E : OriginalCase → EvidenceStage → Set)
  (c : OriginalCase) →
  (E c recipientExposure → ⊥) →
  AdmitsOneOriginalCase E c → ⊥
blockedByMissingExposure E c missing admission =
  missing (AdmitsOneOriginalCase.exposure admission)

blockedByMissingMechanism :
  (E : OriginalCase → EvidenceStage → Set)
  (c : OriginalCase) →
  (E c cognitiveMechanism → ⊥) →
  AdmitsOneOriginalCase E c → ⊥
blockedByMissingMechanism E c missing admission =
  missing (AdmitsOneOriginalCase.mechanism admission)

blockedByMissingCausalDiscriminator :
  (E : OriginalCase → EvidenceStage → Set)
  (c : OriginalCase) →
  (E c causalDiscrimination → ⊥) →
  AdmitsOneOriginalCase E c → ⊥
blockedByMissingCausalDiscriminator E c missing admission =
  missing (AdmitsOneOriginalCase.causal admission)

blockedByMissingIntent :
  (E : OriginalCase → EvidenceStage → Set)
  (c : OriginalCase) →
  (E c independentlySourcedIntent → ⊥) →
  AdmitsOneOriginalCase E c → ⊥
blockedByMissingIntent E c missing admission =
  missing (AdmitsOneOriginalCase.intent admission)

blockedByMissingOriginalIntervention :
  (E : OriginalCase → EvidenceStage → Set)
  (c : OriginalCase) →
  (E c originalIntervention → ⊥) →
  AdmitsOneOriginalCase E c → ⊥
blockedByMissingOriginalIntervention E c missing admission =
  missing (AdmitsOneOriginalCase.intervention admission)

blockedByMissingAttribution :
  (E : OriginalCase → EvidenceStage → Set)
  (c : OriginalCase) →
  (E c originalAttribution → ⊥) →
  AdmitsOneOriginalCase E c → ⊥
blockedByMissingAttribution E c missing admission =
  missing (AdmitsOneOriginalCase.attribution admission)

------------------------------------------------------------------------
-- INDEPENDENT EVIDENCE INTERPRETATION / CONSERVATIVE REFINEMENT.
--
-- An empirically stricter evidence admissibility predicate Strong can
-- be mapped stage-by-stage to Weak. Hence admitted Strong operations
-- imply admitted Weak ones. The converse is NOT asserted. A mere
-- archived catalogue can never be upgraded to a verified causal stage
-- by this theorem; the refinement map must be supplied separately.
------------------------------------------------------------------------

record StagewiseEvidenceRefinement
    (Strong Weak : OriginalCase → EvidenceStage → Set) : Set where
  field
    weaken :
      (c : OriginalCase) (stage : EvidenceStage) →
      Strong c stage → Weak c stage

admissionWeakens :
  (Strong Weak : OriginalCase → EvidenceStage → Set)
  (refinement : StagewiseEvidenceRefinement Strong Weak)
  (c : OriginalCase) →
  AdmitsOneOriginalCase Strong c →
  AdmitsOneOriginalCase Weak c
admissionWeakens Strong Weak refinement c evidence =
  record
    { intervention = StagewiseEvidenceRefinement.weaken refinement
        c originalIntervention (AdmitsOneOriginalCase.intervention evidence)
    ; exposure = StagewiseEvidenceRefinement.weaken refinement
        c recipientExposure (AdmitsOneOriginalCase.exposure evidence)
    ; mechanism = StagewiseEvidenceRefinement.weaken refinement
        c cognitiveMechanism (AdmitsOneOriginalCase.mechanism evidence)
    ; causal = StagewiseEvidenceRefinement.weaken refinement
        c causalDiscrimination (AdmitsOneOriginalCase.causal evidence)
    ; intent = StagewiseEvidenceRefinement.weaken refinement
        c independentlySourcedIntent (AdmitsOneOriginalCase.intent evidence)
    ; attribution = StagewiseEvidenceRefinement.weaken refinement
        c originalAttribution (AdmitsOneOriginalCase.attribution evidence)
    }

-- Non-admission of a weakly sourced operation passes to any stronger
-- predicate that admits a stagewise map to the weak predicate.
nonAdmissionPersistsUnderStrongerStandards :
  (Strong Weak : OriginalCase → EvidenceStage → Set)
  (refinement : StagewiseEvidenceRefinement Strong Weak)
  (c : OriginalCase) →
  (AdmitsOneOriginalCase Weak c → ⊥) →
  AdmitsOneOriginalCase Strong c → ⊥
nonAdmissionPersistsUnderStrongerStandards Strong Weak refinement c blocked strong =
  blocked (admissionWeakens Strong Weak refinement c strong)

-- Concrete instance of the universal theorem, not a separate
-- hypothetical "no exposure ever existed" claim.
selectedGCCBlockedByGeneralMissingGate :
  AdmitsOneOriginalCase CurrentlyLocatedEvidence gcc1993 → ⊥
selectedGCCBlockedByGeneralMissingGate =
  blockedByMissingExposure
    CurrentlyLocatedEvidence gcc1993 currentGCCExposureUnavailable

------------------------------------------------------------------------
-- FINITE NEGATIVE CONTROL: WEAK EVIDENCE DOES NOT UPGRADE ITSELF.
--
-- Both predicates below are purely mathematical TEST FIXTURES.
-- WeakDemo has a receipt at every stage, StrongDemo has no valid
-- independent exposure. Consequently WeakDemo admits an operation
-- while StrongDemo does not, proving that the reverse implication of
-- admissionWeakens is invalid without additional evidentiary work.
------------------------------------------------------------------------

data WeakDemo : OriginalCase → EvidenceStage → Set where
  weakToken : {c : OriginalCase} {s : EvidenceStage} → WeakDemo c s

data StrongDemo : OriginalCase → EvidenceStage → Set where
  strongOriginal :
    (c : OriginalCase) → StrongDemo c originalIntervention
  strongAttribution :
    (c : OriginalCase) → StrongDemo c originalAttribution

weakDemoAdmitsGCC :
  AdmitsOneOriginalCase WeakDemo gcc1993
weakDemoAdmitsGCC =
  record
    { intervention = weakToken
    ; exposure = weakToken
    ; mechanism = weakToken
    ; causal = weakToken
    ; intent = weakToken
    ; attribution = weakToken
    }

strongDemoMissingExposure :
  StrongDemo gcc1993 recipientExposure → ⊥
strongDemoMissingExposure ()

strongDemoDoesNotAdmitGCC :
  AdmitsOneOriginalCase StrongDemo gcc1993 → ⊥
strongDemoDoesNotAdmitGCC =
  blockedByMissingExposure StrongDemo gcc1993 strongDemoMissingExposure

-- We cannot construct a universal converse from weak to strong:
-- even with a weak GCC receipt for recipient exposure, there is
-- provably no corresponding StrongDemo exposure receipt.
noAutomaticUpgradeFromWeakToStrong :
  ((c : OriginalCase) (s : EvidenceStage) →
    WeakDemo c s → StrongDemo c s) → ⊥
noAutomaticUpgradeFromWeakToStrong upgrade =
  strongDemoMissingExposure
    (upgrade gcc1993 recipientExposure weakToken)

noReverseAdmissionImplication :
  (AdmitsOneOriginalCase WeakDemo gcc1993 →
    AdmitsOneOriginalCase StrongDemo gcc1993) → ⊥
noReverseAdmissionImplication promote =
  strongDemoDoesNotAdmitGCC (promote weakDemoAdmitsGCC)

strongDemoRefinesWeakDemo :
  StagewiseEvidenceRefinement StrongDemo WeakDemo
strongDemoRefinesWeakDemo =
  record { weaken = λ c s evidence → weakToken }

------------------------------------------------------------------------
-- SOURCE-BOUND SIX-STAGE ADMISSION (RECEIPT NON-REUSE).
--
-- A case-index alone does not ensure that six stage witnesses are
-- backed by six independent original-source receipts. This *stronger*
-- consumer demands explicit receipt identities, same-original-case
-- ownership, and distinct receipt keys at unequal evidence stages.
-- Observer separation is reused from the Golden owner
-- DASHI.Core.ObserverRefinementLatticeExact; it is not redefined
-- as a fresh singleton/no-collapse principle here. Receipt identities
-- and the source-owner map still require external authentication.
------------------------------------------------------------------------

record SourceBoundAdmission
    (E : OriginalCase → EvidenceStage → Set)
    (Reference : Set)
    (sourceCase : Reference → OriginalCase)
    (c : OriginalCase) : Set where
  field
    stages : AdmitsOneOriginalCase E c
    receiptReference : EvidenceStage → Reference
    referenceBelongsToCase :
      (stage : EvidenceStage) →
      sourceCase (receiptReference stage) ≡ c
    -- Canonical DASHI observer separation, rather than an ad-hoc
    -- per-pair inequality field. Equating receipt references would
    -- force equality of the corresponding evidence-stage coordinates.
    referenceSeparating :
      Observer.Separating receiptReference

sourceBoundImpliesStageAdmission :
  (E : OriginalCase → EvidenceStage → Set)
  (Reference : Set)
  (sourceCase : Reference → OriginalCase)
  (c : OriginalCase) →
  SourceBoundAdmission E Reference sourceCase c →
  AdmitsOneOriginalCase E c
sourceBoundImpliesStageAdmission E Reference sourceCase c admitted =
  SourceBoundAdmission.stages admitted

sourceBoundMissingExposureBlocks :
  (E : OriginalCase → EvidenceStage → Set)
  (Reference : Set)
  (sourceCase : Reference → OriginalCase)
  (c : OriginalCase) →
  (E c recipientExposure → ⊥) →
  SourceBoundAdmission E Reference sourceCase c → ⊥
sourceBoundMissingExposureBlocks E Reference sourceCase c missing admitted =
  blockedByMissingExposure E c missing
    (sourceBoundImpliesStageAdmission E Reference sourceCase c admitted)

sourceBoundMissingIntentBlocks :
  (E : OriginalCase → EvidenceStage → Set)
  (Reference : Set)
  (sourceCase : Reference → OriginalCase)
  (c : OriginalCase) →
  (E c independentlySourcedIntent → ⊥) →
  SourceBoundAdmission E Reference sourceCase c → ⊥
sourceBoundMissingIntentBlocks E Reference sourceCase c missing admitted =
  blockedByMissingIntent E c missing
    (sourceBoundImpliesStageAdmission E Reference sourceCase c admitted)

-- Reuse the canonical observer-collision obstruction for ALL cases,
-- stages and receipt carriers: an observed source-identity collision
-- cannot be reconciled with a separating original-stage observer.
sourceBoundReceiptCollisionImpossible :
  (E : OriginalCase → EvidenceStage → Set)
  (Reference : Set)
  (sourceCase : Reference → OriginalCase)
  (c : OriginalCase) →
  (admitted : SourceBoundAdmission E Reference sourceCase c) →
  Observer.ObserverCollision
    (SourceBoundAdmission.receiptReference admitted) → ⊥
sourceBoundReceiptCollisionImpossible E Reference sourceCase c admitted collision =
  Observer.collisionBlocksSeparation collision
    (SourceBoundAdmission.referenceSeparating admitted)

exposureAndIntentMustHaveDifferentReceipt :
  (E : OriginalCase → EvidenceStage → Set)
  (Reference : Set)
  (sourceCase : Reference → OriginalCase)
  (c : OriginalCase) →
  (admitted : SourceBoundAdmission E Reference sourceCase c) →
  SourceBoundAdmission.receiptReference admitted recipientExposure ≡
  SourceBoundAdmission.receiptReference admitted independentlySourcedIntent →
  ⊥
exposureAndIntentMustHaveDifferentReceipt E Reference sourceCase c admitted =
  exposureIsNotIntent
    (SourceBoundAdmission.referenceSeparating admitted
      recipientExposure independentlySourcedIntent)

interventionAndCausalMustHaveDifferentReceipt :
  (E : OriginalCase → EvidenceStage → Set)
  (Reference : Set)
  (sourceCase : Reference → OriginalCase)
  (c : OriginalCase) →
  (admitted : SourceBoundAdmission E Reference sourceCase c) →
  SourceBoundAdmission.receiptReference admitted originalIntervention ≡
  SourceBoundAdmission.receiptReference admitted causalDiscrimination →
  ⊥
interventionAndCausalMustHaveDifferentReceipt E Reference sourceCase c admitted =
  sourceTextIsNotCausalEffect
    (SourceBoundAdmission.referenceSeparating admitted
      originalIntervention causalDiscrimination)

selectedGCCCannotBeSourceBoundAdmitted :
  (Reference : Set)
  (sourceCase : Reference → OriginalCase) →
  SourceBoundAdmission CurrentlyLocatedEvidence Reference sourceCase gcc1993 → ⊥
selectedGCCCannotBeSourceBoundAdmitted Reference sourceCase =
  sourceBoundMissingExposureBlocks
    CurrentlyLocatedEvidence Reference sourceCase gcc1993
    currentGCCExposureUnavailable

selectedAPICannotBeSourceBoundAdmitted :
  (Reference : Set)
  (sourceCase : Reference → OriginalCase) →
  SourceBoundAdmission CurrentlyLocatedEvidence Reference sourceCase apiProposal1998 → ⊥
selectedAPICannotBeSourceBoundAdmitted Reference sourceCase =
  sourceBoundMissingExposureBlocks
    CurrentlyLocatedEvidence Reference sourceCase apiProposal1998
    currentAPIExposureUnavailable

-- Distinct receipt references are necessary but not sufficient for
-- actual independent confirmation. They may point to duplicated copies
-- of one original record. Independent provenance, reviewer checks,
-- matched exposure/causal measurements and external source validation
-- remain unpaid empirical obligations.

------------------------------------------------------------------------
-- ONE-RECEIPT FINITE REGRESSION OF EXISTING OBSERVER COLLISION
--
-- Even if the caller chooses a trivially inhabited E and a sourceCase
-- map, a singleton receipt-reference carrier cannot discharge a
-- source-bound operation. The ordinary six-stage record did allow this.
------------------------------------------------------------------------

data OneReceipt : Set where
  onlyReceipt : OneReceipt

oneReceiptEquality :
  (left right : OneReceipt) → left ≡ right
oneReceiptEquality onlyReceipt onlyReceipt = refl

oneReceiptCannotSupportSixGates :
  (E : OriginalCase → EvidenceStage → Set)
  (sourceCase : OneReceipt → OriginalCase)
  (c : OriginalCase) →
  SourceBoundAdmission E OneReceipt sourceCase c → ⊥
oneReceiptCannotSupportSixGates E sourceCase c admitted =
  sourceBoundReceiptCollisionImpossible E OneReceipt sourceCase c admitted
    (Observer.observerCollision
      recipientExposure
      independentlySourcedIntent
      (oneReceiptEquality
        (SourceBoundAdmission.receiptReference admitted recipientExposure)
        (SourceBoundAdmission.receiptReference admitted independentlySourcedIntent))
      exposureIsNotIntent)

-- In particular the weak fixture can fill AdmitsOneOriginalCase, but
-- cannot fill SourceBoundAdmission using a singleton source reference.
weakDemoSingleReceiptFailsSourceBoundAdmission :
  (sourceCase : OneReceipt → OriginalCase) →
  SourceBoundAdmission WeakDemo OneReceipt sourceCase gcc1993 → ⊥
weakDemoSingleReceiptFailsSourceBoundAdmission sourceCase =
  oneReceiptCannotSupportSixGates WeakDemo sourceCase gcc1993

------------------------------------------------------------------------
-- CLAIM-SPECIFIC SOURCE PROVENANCE (GENERAL ADMISSION POLICY).
--
-- Distinct propositions do not necessarily require distinct documents.
-- A primary source may properly substantiate more than one stage.
-- What is required is an independently paid *stage-specific support*
-- judgment, with the source attributed to the SAME original case.
-- Such judgments are externally supplied and are not fabricated here.
--
-- SourceBoundAdmission above is retained as an OPTIONAL stricter
-- policy and its singleton obstruction remains a regression for that
-- policy, not a necessary condition for every empirical investigation.
------------------------------------------------------------------------

record ClaimBoundAdmission
    (E : OriginalCase → EvidenceStage → Set)
    (Reference : Set)
    (sourceCase : Reference → OriginalCase)
    (Supports : OriginalCase → EvidenceStage → Reference → Set)
    (c : OriginalCase) : Set where
  field
    stages : AdmitsOneOriginalCase E c
    sourceFor : EvidenceStage → Reference
    sourceBelongsToCase :
      (stage : EvidenceStage) →
      sourceCase (sourceFor stage) ≡ c
    claimSupported :
      (stage : EvidenceStage) →
      Supports c stage (sourceFor stage)

claimBoundImpliesStageAdmission :
  (E : OriginalCase → EvidenceStage → Set)
  (Reference : Set)
  (sourceCase : Reference → OriginalCase)
  (Supports : OriginalCase → EvidenceStage → Reference → Set)
  (c : OriginalCase) →
  ClaimBoundAdmission E Reference sourceCase Supports c →
  AdmitsOneOriginalCase E c
claimBoundImpliesStageAdmission E Reference sourceCase Supports c admitted =
  ClaimBoundAdmission.stages admitted

claimBoundMissingExposureBlocks :
  (E : OriginalCase → EvidenceStage → Set)
  (Reference : Set)
  (sourceCase : Reference → OriginalCase)
  (Supports : OriginalCase → EvidenceStage → Reference → Set)
  (c : OriginalCase) →
  (E c recipientExposure → ⊥) →
  ClaimBoundAdmission E Reference sourceCase Supports c → ⊥
claimBoundMissingExposureBlocks E Reference sourceCase Supports c missing admitted =
  blockedByMissingExposure E c missing
    (claimBoundImpliesStageAdmission E Reference sourceCase Supports c admitted)

-- Every source-bound admission can meet the general policy if a
-- substantive support judgment is additionally supplied for its
-- references. Injectivity alone never creates those judgments.
strictReceiptPolicyRequiresClaimSupport :
  (E : OriginalCase → EvidenceStage → Set)
  (Reference : Set)
  (sourceCase : Reference → OriginalCase)
  (Supports : OriginalCase → EvidenceStage → Reference → Set)
  (c : OriginalCase) →
  (strict : SourceBoundAdmission E Reference sourceCase c) →
  ((stage : EvidenceStage) →
    Supports c stage (SourceBoundAdmission.receiptReference strict)) →
  ClaimBoundAdmission E Reference sourceCase Supports c
strictReceiptPolicyRequiresClaimSupport E Reference sourceCase Supports c strict supported =
  record
    { stages = SourceBoundAdmission.stages strict
    ; sourceFor = SourceBoundAdmission.receiptReference strict
    ; sourceBelongsToCase = SourceBoundAdmission.referenceBelongsToCase strict
    ; claimSupported = supported
    }

------------------------------------------------------------------------
-- NEGATIVE CONTROL: ONE SOURCE MAY SUPPORT MANY DISTINCT CLAIMS.
-- Synthetic only; the uniformly inhabited test predicates do not
-- authenticate any GCC document, exposure, effect, intent or actor.
------------------------------------------------------------------------

open import Agda.Builtin.Unit using (⊤; tt)

oneReceiptOwner : OneReceipt → OriginalCase
oneReceiptOwner onlyReceipt = gcc1993

data SyntheticStageSupport :
    OriginalCase → EvidenceStage → OneReceipt → Set where
  syntheticStageSupport :
    {stage : EvidenceStage} →
    SyntheticStageSupport gcc1993 stage onlyReceipt

sharedSourceCanSupportSeveralDifferentStageClaims :
  ClaimBoundAdmission
    WeakDemo OneReceipt oneReceiptOwner
    SyntheticStageSupport gcc1993
sharedSourceCanSupportSeveralDifferentStageClaims =
  record
    { stages = weakDemoAdmitsGCC
    ; sourceFor = λ stage → onlyReceipt
    ; sourceBelongsToCase = λ stage → refl
    ; claimSupported = λ stage → syntheticStageSupport
    }

-- Reusing the canonical Golden collision theorem, the shared-source
-- example proves that claim-specific support does NOT imply receipt
-- identifier injectivity. This corrects the previous over-restriction.
claimSpecificSupportDoesNotForceDistinctReferences :
  ((admitted : ClaimBoundAdmission
      WeakDemo OneReceipt oneReceiptOwner
      SyntheticStageSupport gcc1993) →
    Observer.Separating (ClaimBoundAdmission.sourceFor admitted)) → ⊥
claimSpecificSupportDoesNotForceDistinctReferences assumeSeparating =
  Observer.collisionBlocksSeparation
    (Observer.observerCollision
      recipientExposure
      independentlySourcedIntent
      refl
      exposureIsNotIntent)
    (assumeSeparating sharedSourceCanSupportSeveralDifferentStageClaims)

-- Under any actually selected original inventory, the universal
-- missing-exposure obstruction remains operative even though source
-- references may be reused for independently justified claims.
selectedGCCNotClaimBoundUnderCurrentInventory :
  (Reference : Set)
  (sourceCase : Reference → OriginalCase)
  (Supports : OriginalCase → EvidenceStage → Reference → Set) →
  ClaimBoundAdmission
    CurrentlyLocatedEvidence Reference sourceCase Supports gcc1993 → ⊥
selectedGCCNotClaimBoundUnderCurrentInventory Reference sourceCase Supports =
  claimBoundMissingExposureBlocks
    CurrentlyLocatedEvidence Reference sourceCase Supports gcc1993
    currentGCCExposureUnavailable
