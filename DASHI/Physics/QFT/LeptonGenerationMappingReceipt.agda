module DASHI.Physics.QFT.LeptonGenerationMappingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.LeptonSectorGapReceipt as Gap

------------------------------------------------------------------------
-- Candidate lepton-generation mapping receipt.
--
-- This receipt records a candidate structural map from the next three
-- inspected class-number-1 CM discriminants D=-8, D=-11, and D=-12 to the
-- three lepton-generation labels.  It is not a construction of a lepton
-- sector, a Yukawa sector, or an exact Standard Model/DHR promotion.
--
-- Corrected conductor/discriminant caution: the displayed entries
-- D=-8,D=-11,D=-12 are discriminants.  Quadratic-order conductors are not
-- obtained by taking absolute values of those discriminants.  With the usual
-- D = f^2 D_K convention, the recorded candidate order conductors are
-- f=1 for D=-8, f=1 for D=-11, and f=2 for D=-12.  The common Z/2 unit
-- group pattern is diagnostic bookkeeping only.

data LeptonGenerationLabel : Set where
  firstLeptonGeneration :
    LeptonGenerationLabel

  secondLeptonGeneration :
    LeptonGenerationLabel

  thirdLeptonGeneration :
    LeptonGenerationLabel

canonicalLeptonGenerationLabels :
  List LeptonGenerationLabel
canonicalLeptonGenerationLabels =
  firstLeptonGeneration
  ∷ secondLeptonGeneration
  ∷ thirdLeptonGeneration
  ∷ []

leptonGenerationLabelText :
  LeptonGenerationLabel →
  String
leptonGenerationLabelText firstLeptonGeneration =
  "first lepton generation"
leptonGenerationLabelText secondLeptonGeneration =
  "second lepton generation"
leptonGenerationLabelText thirdLeptonGeneration =
  "third lepton generation"

data UnitGroupDiagnosticPattern : Set where
  z2UnitGroupDiagnostic :
    UnitGroupDiagnosticPattern

unitGroupDiagnosticPatternLabel :
  String
unitGroupDiagnosticPatternLabel =
  "Unit group Z/2 pattern is diagnostic only; it does not construct lepton fields or masses"

data LeptonGenerationMappingStatus : Set where
  candidateStructuralMapOnly :
    LeptonGenerationMappingStatus

candidateStructuralMapBoundaryLabel :
  String
candidateStructuralMapBoundaryLabel =
  "Candidate structural map from D=-8,D=-11,D=-12 to three lepton-generation labels only; no lepton sector is constructed"

conductorDiscriminantCautionLabel :
  String
conductorDiscriminantCautionLabel =
  "Corrected caution: D=-8,D=-11,D=-12 are discriminants, not conductor values; the candidate order conductors recorded here are 1,1,2"

record CandidateLeptonGenerationMapEntry : Set where
  field
    discriminant :
      Gap.ClassNumberOneDiscriminant

    discriminantLabel :
      String

    discriminantLabelIsCanonical :
      discriminantLabel ≡ Gap.classNumberOneDiscriminantLabel discriminant

    quadraticOrderConductor :
      Nat

    generation :
      LeptonGenerationLabel

    generationLabel :
      String

    generationLabelIsCanonical :
      generationLabel ≡ leptonGenerationLabelText generation

    unitGroupPattern :
      UnitGroupDiagnosticPattern

    unitGroupPatternIsDiagnosticZ2 :
      unitGroupPattern ≡ z2UnitGroupDiagnostic

    status :
      LeptonGenerationMappingStatus

    statusIsCandidateStructuralMapOnly :
      status ≡ candidateStructuralMapOnly

open CandidateLeptonGenerationMapEntry public

dMinusEightToFirstGenerationCandidate :
  CandidateLeptonGenerationMapEntry
dMinusEightToFirstGenerationCandidate =
  record
    { discriminant =
        Gap.D-8
    ; discriminantLabel =
        "D=-8"
    ; discriminantLabelIsCanonical =
        refl
    ; quadraticOrderConductor =
        1
    ; generation =
        firstLeptonGeneration
    ; generationLabel =
        "first lepton generation"
    ; generationLabelIsCanonical =
        refl
    ; unitGroupPattern =
        z2UnitGroupDiagnostic
    ; unitGroupPatternIsDiagnosticZ2 =
        refl
    ; status =
        candidateStructuralMapOnly
    ; statusIsCandidateStructuralMapOnly =
        refl
    }

dMinusElevenToSecondGenerationCandidate :
  CandidateLeptonGenerationMapEntry
dMinusElevenToSecondGenerationCandidate =
  record
    { discriminant =
        Gap.D-11
    ; discriminantLabel =
        "D=-11"
    ; discriminantLabelIsCanonical =
        refl
    ; quadraticOrderConductor =
        1
    ; generation =
        secondLeptonGeneration
    ; generationLabel =
        "second lepton generation"
    ; generationLabelIsCanonical =
        refl
    ; unitGroupPattern =
        z2UnitGroupDiagnostic
    ; unitGroupPatternIsDiagnosticZ2 =
        refl
    ; status =
        candidateStructuralMapOnly
    ; statusIsCandidateStructuralMapOnly =
        refl
    }

dMinusTwelveToThirdGenerationCandidate :
  CandidateLeptonGenerationMapEntry
dMinusTwelveToThirdGenerationCandidate =
  record
    { discriminant =
        Gap.D-12
    ; discriminantLabel =
        "D=-12"
    ; discriminantLabelIsCanonical =
        refl
    ; quadraticOrderConductor =
        2
    ; generation =
        thirdLeptonGeneration
    ; generationLabel =
        "third lepton generation"
    ; generationLabelIsCanonical =
        refl
    ; unitGroupPattern =
        z2UnitGroupDiagnostic
    ; unitGroupPatternIsDiagnosticZ2 =
        refl
    ; status =
        candidateStructuralMapOnly
    ; statusIsCandidateStructuralMapOnly =
        refl
    }

canonicalCandidateLeptonGenerationMapEntries :
  List CandidateLeptonGenerationMapEntry
canonicalCandidateLeptonGenerationMapEntries =
  dMinusEightToFirstGenerationCandidate
  ∷ dMinusElevenToSecondGenerationCandidate
  ∷ dMinusTwelveToThirdGenerationCandidate
  ∷ []

record LeptonGenerationMappingReceipt : Setω where
  field
    leptonSectorGapReceipt :
      Gap.LeptonSectorGapReceipt

    sourceCandidateDiscriminants :
      List Gap.ClassNumberOneDiscriminant

    sourceCandidateDiscriminantsAreGapCandidates :
      sourceCandidateDiscriminants
      ≡
      Gap.nextLeptonLaneCandidateDiscriminants

    targetGenerationLabels :
      List LeptonGenerationLabel

    targetGenerationLabelsAreCanonical :
      targetGenerationLabels ≡ canonicalLeptonGenerationLabels

    candidateEntries :
      List CandidateLeptonGenerationMapEntry

    candidateEntriesAreCanonical :
      candidateEntries ≡ canonicalCandidateLeptonGenerationMapEntries

    dMinusEightCandidate :
      CandidateLeptonGenerationMapEntry

    dMinusEightCandidateIsCanonical :
      dMinusEightCandidate ≡ dMinusEightToFirstGenerationCandidate

    dMinusEightOrderConductorIsOne :
      quadraticOrderConductor dMinusEightCandidate ≡ 1

    dMinusElevenCandidate :
      CandidateLeptonGenerationMapEntry

    dMinusElevenCandidateIsCanonical :
      dMinusElevenCandidate ≡ dMinusElevenToSecondGenerationCandidate

    dMinusElevenOrderConductorIsOne :
      quadraticOrderConductor dMinusElevenCandidate ≡ 1

    dMinusTwelveCandidate :
      CandidateLeptonGenerationMapEntry

    dMinusTwelveCandidateIsCanonical :
      dMinusTwelveCandidate ≡ dMinusTwelveToThirdGenerationCandidate

    dMinusTwelveOrderConductorIsTwo :
      quadraticOrderConductor dMinusTwelveCandidate ≡ 2

    candidateStructuralMap :
      Bool

    candidateStructuralMapIsTrue :
      candidateStructuralMap ≡ true

    leptonSectorConstructed :
      Bool

    leptonSectorConstructedIsFalse :
      leptonSectorConstructed ≡ false

    standardModelSectorConstructed :
      Bool

    standardModelSectorConstructedIsFalse :
      standardModelSectorConstructed ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    unitGroupZ2PatternDiagnosticOnly :
      Bool

    unitGroupZ2PatternDiagnosticOnlyIsTrue :
      unitGroupZ2PatternDiagnosticOnly ≡ true

    unitGroupDiagnosticPatternStatement :
      String

    unitGroupDiagnosticPatternStatementIsCanonical :
      unitGroupDiagnosticPatternStatement
      ≡
      unitGroupDiagnosticPatternLabel

    conductorDiscriminantCaution :
      String

    conductorDiscriminantCautionIsCanonical :
      conductorDiscriminantCaution ≡ conductorDiscriminantCautionLabel

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ candidateStructuralMapBoundaryLabel

    auditTrail :
      List String

open LeptonGenerationMappingReceipt public

canonicalLeptonGenerationMappingReceipt :
  LeptonGenerationMappingReceipt
canonicalLeptonGenerationMappingReceipt =
  record
    { leptonSectorGapReceipt =
        Gap.canonicalLeptonSectorGapReceipt
    ; sourceCandidateDiscriminants =
        Gap.nextLeptonLaneCandidateDiscriminants
    ; sourceCandidateDiscriminantsAreGapCandidates =
        refl
    ; targetGenerationLabels =
        canonicalLeptonGenerationLabels
    ; targetGenerationLabelsAreCanonical =
        refl
    ; candidateEntries =
        canonicalCandidateLeptonGenerationMapEntries
    ; candidateEntriesAreCanonical =
        refl
    ; dMinusEightCandidate =
        dMinusEightToFirstGenerationCandidate
    ; dMinusEightCandidateIsCanonical =
        refl
    ; dMinusEightOrderConductorIsOne =
        refl
    ; dMinusElevenCandidate =
        dMinusElevenToSecondGenerationCandidate
    ; dMinusElevenCandidateIsCanonical =
        refl
    ; dMinusElevenOrderConductorIsOne =
        refl
    ; dMinusTwelveCandidate =
        dMinusTwelveToThirdGenerationCandidate
    ; dMinusTwelveCandidateIsCanonical =
        refl
    ; dMinusTwelveOrderConductorIsTwo =
        refl
    ; candidateStructuralMap =
        true
    ; candidateStructuralMapIsTrue =
        refl
    ; leptonSectorConstructed =
        false
    ; leptonSectorConstructedIsFalse =
        refl
    ; standardModelSectorConstructed =
        false
    ; standardModelSectorConstructedIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; unitGroupZ2PatternDiagnosticOnly =
        true
    ; unitGroupZ2PatternDiagnosticOnlyIsTrue =
        refl
    ; unitGroupDiagnosticPatternStatement =
        unitGroupDiagnosticPatternLabel
    ; unitGroupDiagnosticPatternStatementIsCanonical =
        refl
    ; conductorDiscriminantCaution =
        conductorDiscriminantCautionLabel
    ; conductorDiscriminantCautionIsCanonical =
        refl
    ; receiptBoundary =
        candidateStructuralMapBoundaryLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; auditTrail =
        "Candidate mapping recorded: D=-8 -> first lepton generation"
        ∷ "Candidate mapping recorded: D=-11 -> second lepton generation"
        ∷ "Candidate mapping recorded: D=-12 -> third lepton generation"
        ∷ "D=-8,D=-11,D=-12 are discriminants; the candidate quadratic-order conductors recorded here are 1,1,2"
        ∷ "The shared Z/2 unit-group pattern is diagnostic only"
        ∷ "candidateStructuralMap=true, while leptonSectorConstructed=false"
        ∷ "standardModelSectorConstructed=false, exactStandardModelPromotion=false, and gDHREqualsGSMPromoted=false"
        ∷ []
    }

leptonGenerationMappingKeepsLeptonSectorUnconstructed :
  leptonSectorConstructed canonicalLeptonGenerationMappingReceipt
  ≡
  false
leptonGenerationMappingKeepsLeptonSectorUnconstructed =
  refl

leptonGenerationMappingKeepsSMConstructionFalse :
  standardModelSectorConstructed canonicalLeptonGenerationMappingReceipt
  ≡
  false
leptonGenerationMappingKeepsSMConstructionFalse =
  refl

leptonGenerationMappingKeepsGDHRSMFalse :
  gDHREqualsGSMPromoted canonicalLeptonGenerationMappingReceipt
  ≡
  false
leptonGenerationMappingKeepsGDHRSMFalse =
  refl

leptonGenerationMappingRecordsZ2AsDiagnosticOnly :
  unitGroupZ2PatternDiagnosticOnly canonicalLeptonGenerationMappingReceipt
  ≡
  true
leptonGenerationMappingRecordsZ2AsDiagnosticOnly =
  refl
