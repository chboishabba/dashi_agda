module DASHI.Core.EvidenceHyperfabricExact where

------------------------------------------------------------------------
-- EVIDENCE HYPERFABRIC / INVESTIGATIVE NON-PROMOTION CORE
--
-- The purpose of this module is not to decide any concrete historical case.
-- It owns a reusable proof discipline for keeping distinct:
--
--   * testimony from the event proposition testified to,
--   * corroboration from permission to treat testimony as evidence,
--   * institutional classification from underlying forensic proof,
--   * not-located records from known-absent records,
--   * repeated reporting from independent corroboration,
--   * public statements from the mechanisms that produced them.
--
-- The central architectural rule is fibre-preserving: a public case label is
-- only one coordinate.  Provenance, testimony, forensic receipts, witness
-- structure, record availability, chronology, and source independence remain
-- separate fibres and may not be silently flattened into that label.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- Primitive evidence coordinates.
------------------------------------------------------------------------

data EvidenceKind : Set where
  testimony recordEvidence witnessEvidence forensicEvidence
  institutionalEvidence secondaryEvidence : EvidenceKind

data RecordStatus : Set where
  present notLocated knownAbsent : RecordStatus

data TemporalPosition : Set where
  preEvent postEvent : TemporalPosition

data SourceRelation : Set where
  independent sharedLineage unknownLineage : SourceRelation

data AuditStatus : Set where
  publiclyAuditable notPubliclyAuditable : AuditStatus

notLocated≠knownAbsent : notLocated ≡ knownAbsent → ⊥
notLocated≠knownAbsent ()

knownAbsent≠notLocated : knownAbsent ≡ notLocated → ⊥
knownAbsent≠notLocated ()

independent≠sharedLineage : independent ≡ sharedLineage → ⊥
independent≠sharedLineage ()

preEvent≠postEvent : preEvent ≡ postEvent → ⊥
preEvent≠postEvent ()

------------------------------------------------------------------------
-- Provenance fibre.
------------------------------------------------------------------------

record Provenance
    (Creator Time Medium Custody Transformation : Set) : Set where
  constructor provenance
  field
    creator : Creator
    time : Time
    medium : Medium
    custody : Custody
    transformation : Transformation
    temporalPosition : TemporalPosition
    availability : RecordStatus

open Provenance public

record EvidenceNode
    (Id Claim Creator Time Medium Custody Transformation : Set) : Set₁ where
  constructor evidenceNode
  field
    evidenceId : Id
    evidenceKind : EvidenceKind
    assertedClaim : Claim
    nodeProvenance : Provenance Creator Time Medium Custody Transformation

open EvidenceNode public

------------------------------------------------------------------------
-- Testimony is evidence for a proposition without being definitionally equal
-- to proof that the proposition occurred.
------------------------------------------------------------------------

record TestimonyFor {Claim : Set} (claim : Claim) : Set where
  constructor testimonyFor
  field
    isPrimaryTestimony : Bool
    isPrimaryTestimonyIsTrue : isPrimaryTestimony ≡ true

open TestimonyFor public

record EventProof {Claim : Set} (claim : Claim) : Set where
  constructor eventProof
  field
    isEventProof : Bool
    isEventProofIsTrue : isEventProof ≡ true

open EventProof public

record RumourOnly {Claim : Set} (claim : Claim) : Set where
  constructor rumourOnly
  field
    isRumourOnly : Bool
    isRumourOnlyIsTrue : isRumourOnly ≡ true

open RumourOnly public

------------------------------------------------------------------------
-- Corroboration refines an evidence state; it does not create the underlying
-- testimony ex nihilo and is not a precondition for testimony to be evidence.
------------------------------------------------------------------------

record CorroborationGraph (Evidence : Set) : Set₁ where
  field
    Corroborates : Evidence → Evidence → Set
    sourceRelation : Evidence → Evidence → SourceRelation

open CorroborationGraph public

IndependentCorroboration :
  ∀ {Evidence : Set} →
  CorroborationGraph Evidence → Evidence → Evidence → Set
IndependentCorroboration graph corroborator target =
  Corroborates graph corroborator target ×
  sourceRelation graph corroborator target ≡ independent

record EvidenceRefinement (Evidence : Set) : Set₁ where
  constructor evidenceRefinement
  field
    baseEvidence : Evidence
    addedEvidence : Evidence

open EvidenceRefinement public

corroborationAddsCoordinate :
  ∀ {Evidence : Set}
    (graph : CorroborationGraph Evidence)
    {corroborator target : Evidence} →
  Corroborates graph corroborator target →
  EvidenceRefinement Evidence
corroborationAddsCoordinate graph {corroborator} {target} receipt =
  evidenceRefinement target corroborator

------------------------------------------------------------------------
-- Generic state-indexed non-promotion witness.
------------------------------------------------------------------------

record NonPromotion
    {State : Set}
    (Premise Conclusion : State → Set) : Set₁ where
  constructor nonPromotion
  field
    witnessState : State
    premiseHolds : Premise witnessState
    conclusionFails : Conclusion witnessState → ⊥

open NonPromotion public

nonPromotionRefutesUniversalPromotion :
  ∀ {State : Set} {Premise Conclusion : State → Set} →
  NonPromotion Premise Conclusion →
  (∀ state → Premise state → Conclusion state) →
  ⊥
nonPromotionRefutesUniversalPromotion witness promote =
  conclusionFails witness
    (promote (witnessState witness) (premiseHolds witness))

------------------------------------------------------------------------
-- Institutional classification and forensic audit are different fibres.
------------------------------------------------------------------------

record InstitutionalClassification (State Hypothesis : Set) : Set₁ where
  field
    classifiedAs : State → Hypothesis
    classificationAudit : State → AuditStatus

open InstitutionalClassification public

record ForensicEstablishment (State Hypothesis : Set) : Set₁ where
  field
    ForensicallyEstablished : State → Hypothesis → Set

open ForensicEstablishment public

record PublicCaseSurface (State Label : Set) : Set₁ where
  field
    publicLabel : Observer.Observer State Label

open PublicCaseSurface public

record CaseEvidenceFibre
    (State Testimony Record Witness Forensic Institution Secondary : Set) : Set₁ where
  field
    testimonyCoordinate : State → Testimony
    recordCoordinate : State → Record
    witnessCoordinate : State → Witness
    forensicCoordinate : State → Forensic
    institutionalCoordinate : State → Institution
    secondaryCoordinate : State → Secondary

open CaseEvidenceFibre public

caseHypervoxel :
  ∀ {State Testimony Record Witness Forensic Institution Secondary : Set} →
  CaseEvidenceFibre State Testimony Record Witness Forensic Institution Secondary →
  State →
  Testimony × (Record × (Witness × (Forensic × (Institution × Secondary))))
caseHypervoxel fibre state =
  testimonyCoordinate fibre state ,
  (recordCoordinate fibre state ,
  (witnessCoordinate fibre state ,
  (forensicCoordinate fibre state ,
  (institutionalCoordinate fibre state , secondaryCoordinate fibre state))))

------------------------------------------------------------------------
-- Public-surface non-factorability.
------------------------------------------------------------------------

record HiddenCaseEvidence
    {State Label Residual : Set}
    (surface : Observer.Observer State Label)
    (residual : Observer.Observer State Residual) : Set where
  constructor hiddenCaseEvidence
  field
    leftCase rightCase : State
    samePublicLabel : surface leftCase ≡ surface rightCase
    residualSeparates : residual leftCase ≡ residual rightCase → ⊥

open HiddenCaseEvidence public

hiddenCaseEvidenceGivesStrictRefinement :
  ∀ {State Label Residual : Set}
    {surface : Observer.Observer State Label}
    {residual : Observer.Observer State Residual} →
  HiddenCaseEvidence surface residual →
  Observer.StrictRefinement surface (Observer.pairObserver surface residual)
hiddenCaseEvidenceGivesStrictRefinement witness =
  Observer.strictPairRefinement
    _ _
    (leftCase witness)
    (rightCase witness)
    (samePublicLabel witness)
    (residualSeparates witness)

ResidualDescendsThroughPublicLabel :
  ∀ {State Label Residual : Set} →
  Observer.Observer State Label →
  Observer.Observer State Residual →
  Set
ResidualDescendsThroughPublicLabel {Label = Label} {Residual = Residual}
    surface residual =
  Σ (Label → Residual)
    (λ reconstruct → ∀ state → reconstruct (surface state) ≡ residual state)

hiddenCaseEvidenceBlocksPublicDescent :
  ∀ {State Label Residual : Set}
    {surface : Observer.Observer State Label}
    {residual : Observer.Observer State Residual} →
  HiddenCaseEvidence surface residual →
  ResidualDescendsThroughPublicLabel surface residual →
  ⊥
hiddenCaseEvidenceBlocksPublicDescent witness descent =
  residualSeparates witness
    (trans
      (sym (commutes (leftCase witness)))
      (trans
        (cong reconstruct (samePublicLabel witness))
        (commutes (rightCase witness))))
  where
    reconstruct = proj₁ descent
    commutes = proj₂ descent

------------------------------------------------------------------------
-- Explicit investigative firewalls.  These are architecture receipts, not
-- claims about any concrete case.
------------------------------------------------------------------------

record EvidenceBoundary : Set where
  constructor evidenceBoundary
  field
    testimonyIsEvidenceWithoutCorroborationPermission : Bool
    testimonyIsEvidenceWithoutCorroborationPermissionIsTrue :
      testimonyIsEvidenceWithoutCorroborationPermission ≡ true

    testimonyAutomaticallyProvesEvent : Bool
    testimonyAutomaticallyProvesEventIsFalse :
      testimonyAutomaticallyProvesEvent ≡ false

    uncorroboratedAutomaticallyMeansDiscredited : Bool
    uncorroboratedAutomaticallyMeansDiscreditedIsFalse :
      uncorroboratedAutomaticallyMeansDiscredited ≡ false

    officialClassificationAutomaticallyForensicProof : Bool
    officialClassificationAutomaticallyForensicProofIsFalse :
      officialClassificationAutomaticallyForensicProof ≡ false

    missingPublicRecordAutomaticallyMeansNoRecordExists : Bool
    missingPublicRecordAutomaticallyMeansNoRecordExistsIsFalse :
      missingPublicRecordAutomaticallyMeansNoRecordExists ≡ false

    repeatedMediaAutomaticallyIndependentCorroboration : Bool
    repeatedMediaAutomaticallyIndependentCorroborationIsFalse :
      repeatedMediaAutomaticallyIndependentCorroboration ≡ false

    familyAcceptanceAutomaticallyIndependentForensicConfirmation : Bool
    familyAcceptanceAutomaticallyIndependentForensicConfirmationIsFalse :
      familyAcceptanceAutomaticallyIndependentForensicConfirmation ≡ false

    familyAcceptanceAutomaticallyProvesCoercion : Bool
    familyAcceptanceAutomaticallyProvesCoercionIsFalse :
      familyAcceptanceAutomaticallyProvesCoercion ≡ false

    familyAcceptanceAutomaticallyRefutesCoercion : Bool
    familyAcceptanceAutomaticallyRefutesCoercionIsFalse :
      familyAcceptanceAutomaticallyRefutesCoercion ≡ false

    preEventThreatStatementAutomaticallyProvesHomicide : Bool
    preEventThreatStatementAutomaticallyProvesHomicideIsFalse :
      preEventThreatStatementAutomaticallyProvesHomicide ≡ false

    preEventThreatStatementAutomaticallyIrrelevant : Bool
    preEventThreatStatementAutomaticallyIrrelevantIsFalse :
      preEventThreatStatementAutomaticallyIrrelevant ≡ false

canonicalEvidenceBoundary : EvidenceBoundary
canonicalEvidenceBoundary =
  evidenceBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
