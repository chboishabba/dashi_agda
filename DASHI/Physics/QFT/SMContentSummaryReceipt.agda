module DASHI.Physics.QFT.SMContentSummaryReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Standard Model content summary receipt.
--
-- This receipt compiles the current finite carrier/SM content map.  It is
-- deliberately a summary boundary: some rows are structural results, some
-- rows are diagnostics, and several rows are open blockers.  It does not
-- construct a full Standard Model sector, a continuous U(1)_Y, exact
-- SU(2)_L, exact SU(3)_c, physical CKM closure, a lepton sector, or a
-- fourth-generation exclusion mechanism.

data SMContentStatus : Set where
  derivedStructural :
    SMContentStatus

  candidateStructural :
    SMContentStatus

  diagnosticNumerical :
    SMContentStatus

  openBlocker :
    SMContentStatus

data MatterLaneKind : Set where
  quarkLane :
    MatterLaneKind

  leptonLaneCandidate :
    MatterLaneKind

data SMContentItem : Set where
  threeQuarkGenerations :
    SMContentItem

  threeLeptonGenerations :
    SMContentItem

  hyperchargeUnitOneSixth :
    SMContentItem

  u1YContinuity :
    SMContentItem

  su2LLevelOne :
    SMContentItem

  su3CChiralLimit :
    SMContentItem

  wolfensteinLambda :
    SMContentItem

  wolfensteinA :
    SMContentItem

  vubEntry :
    SMContentItem

  cpPhase :
    SMContentItem

  higgsMass :
    SMContentItem

  fourthGenerationMechanism :
    SMContentItem

smContentItemLabel :
  SMContentItem →
  String
smContentItemLabel threeQuarkGenerations =
  "3 quark generations"
smContentItemLabel threeLeptonGenerations =
  "3 lepton generations"
smContentItemLabel hyperchargeUnitOneSixth =
  "charge quantisation unit 1/6"
smContentItemLabel u1YContinuity =
  "continuous U(1)_Y"
smContentItemLabel su2LLevelOne =
  "SU(2)_L level 1"
smContentItemLabel su3CChiralLimit =
  "SU(3)_c approximate chiral-limit candidate"
smContentItemLabel wolfensteinLambda =
  "Wolfenstein lambda"
smContentItemLabel wolfensteinA =
  "Wolfenstein A"
smContentItemLabel vubEntry =
  "|V_ub|"
smContentItemLabel cpPhase =
  "CKM CP phase"
smContentItemLabel higgsMass =
  "Higgs mass"
smContentItemLabel fourthGenerationMechanism =
  "no-fourth-generation mechanism"

record MatterLaneEntry : Set where
  field
    laneKind :
      MatterLaneKind

    positionInContentMap :
      Nat

    discriminantLabel :
      String

    generationLabel :
      String

    status :
      SMContentStatus

    summary :
      String

open MatterLaneEntry public

quarkLaneDMinusFour :
  MatterLaneEntry
quarkLaneDMinusFour =
  record
    { laneKind =
        quarkLane
    ; positionInContentMap =
        1
    ; discriminantLabel =
        "D=-4"
    ; generationLabel =
        "quark generation 1"
    ; status =
        candidateStructural
    ; summary =
        "p2/CM lane included in the first three quark-generation positions"
    }

quarkLaneDMinusThree :
  MatterLaneEntry
quarkLaneDMinusThree =
  record
    { laneKind =
        quarkLane
    ; positionInContentMap =
        2
    ; discriminantLabel =
        "D=-3"
    ; generationLabel =
        "quark generation 2"
    ; status =
        candidateStructural
    ; summary =
        "p3/CM lane included in the first three quark-generation positions"
    }

quarkLaneDMinusSeven :
  MatterLaneEntry
quarkLaneDMinusSeven =
  record
    { laneKind =
        quarkLane
    ; positionInContentMap =
        3
    ; discriminantLabel =
        "D=-7"
    ; generationLabel =
        "quark generation 3"
    ; status =
        candidateStructural
    ; summary =
        "p5/CM lane included in the first three quark-generation positions"
    }

leptonLaneDMinusEight :
  MatterLaneEntry
leptonLaneDMinusEight =
  record
    { laneKind =
        leptonLaneCandidate
    ; positionInContentMap =
        4
    ; discriminantLabel =
        "D=-8"
    ; generationLabel =
        "lepton generation 1 candidate"
    ; status =
        candidateStructural
    ; summary =
        "candidate first lepton lane after the three quark lanes"
    }

leptonLaneDMinusEleven :
  MatterLaneEntry
leptonLaneDMinusEleven =
  record
    { laneKind =
        leptonLaneCandidate
    ; positionInContentMap =
        5
    ; discriminantLabel =
        "D=-11"
    ; generationLabel =
        "lepton generation 2 candidate"
    ; status =
        candidateStructural
    ; summary =
        "candidate second lepton lane after the three quark lanes"
    }

leptonLaneDMinusTwelve :
  MatterLaneEntry
leptonLaneDMinusTwelve =
  record
    { laneKind =
        leptonLaneCandidate
    ; positionInContentMap =
        6
    ; discriminantLabel =
        "D=-12"
    ; generationLabel =
        "lepton generation 3 candidate"
    ; status =
        candidateStructural
    ; summary =
        "candidate third lepton lane after the three quark lanes"
    }

canonicalQuarkLaneEntries :
  List MatterLaneEntry
canonicalQuarkLaneEntries =
  quarkLaneDMinusFour
  ∷ quarkLaneDMinusThree
  ∷ quarkLaneDMinusSeven
  ∷ []

canonicalLeptonLaneCandidateEntries :
  List MatterLaneEntry
canonicalLeptonLaneCandidateEntries =
  leptonLaneDMinusEight
  ∷ leptonLaneDMinusEleven
  ∷ leptonLaneDMinusTwelve
  ∷ []

record SMContentRow : Set where
  field
    item :
      SMContentItem

    itemLabel :
      String

    itemLabelIsCanonical :
      itemLabel ≡ smContentItemLabel item

    status :
      SMContentStatus

    summary :
      String

open SMContentRow public

threeQuarkGenerationRow :
  SMContentRow
threeQuarkGenerationRow =
  record
    { item =
        threeQuarkGenerations
    ; itemLabel =
        "3 quark generations"
    ; itemLabelIsCanonical =
        refl
    ; status =
        candidateStructural
    ; summary =
        "recorded from D=-4,D=-3,D=-7 in positions 1-3; exact quark fields are not constructed here"
    }

threeLeptonGenerationRow :
  SMContentRow
threeLeptonGenerationRow =
  record
    { item =
        threeLeptonGenerations
    ; itemLabel =
        "3 lepton generations"
    ; itemLabelIsCanonical =
        refl
    ; status =
        candidateStructural
    ; summary =
        "candidate lanes D=-8,D=-11,D=-12 in positions 4-6; no lepton sector is constructed"
    }

hyperchargeUnitOneSixthRow :
  SMContentRow
hyperchargeUnitOneSixthRow =
  record
    { item =
        hyperchargeUnitOneSixth
    ; itemLabel =
        "charge quantisation unit 1/6"
    ; itemLabelIsCanonical =
        refl
    ; status =
        derivedStructural
    ; summary =
        "finite charge quantisation unit 1/6 is recorded structurally from the p3-lane Z/6 CM character group"
    }

u1YContinuityRow :
  SMContentRow
u1YContinuityRow =
  record
    { item =
        u1YContinuity
    ; itemLabel =
        "continuous U(1)_Y"
    ; itemLabelIsCanonical =
        refl
    ; status =
        openBlocker
    ; summary =
        "continuous U(1)_Y is open; the finite Z/6 quantisation row does not supply the continuous gauge group"
    }

su2LLevelOneRow :
  SMContentRow
su2LLevelOneRow =
  record
    { item =
        su2LLevelOne
    ; itemLabel =
        "SU(2)_L level 1"
    ; itemLabelIsCanonical =
        refl
    ; status =
        candidateStructural
    ; summary =
        "candidate SU(2)_L level 1 arises from Chern-Simons level flow; exact weak-sector reconstruction remains open"
    }

su3CChiralLimitRow :
  SMContentRow
su3CChiralLimitRow =
  record
    { item =
        su3CChiralLimit
    ; itemLabel =
        "SU(3)_c approximate chiral-limit candidate"
    ; itemLabelIsCanonical =
        refl
    ; status =
        candidateStructural
    ; summary =
        "approximate colour candidate comes from the chiral-limit three-lane metric; exact continuous SU(3)_c is open"
    }

lambdaRow :
  SMContentRow
lambdaRow =
  record
    { item =
        wolfensteinLambda
    ; itemLabel =
        "Wolfenstein lambda"
    ; itemLabelIsCanonical =
        refl
    ; status =
        diagnosticNumerical
    ; summary =
        "lambda diagnostic: carrier formula recorded at about 0.04 percent error"
    }

wolfensteinARow :
  SMContentRow
wolfensteinARow =
  record
    { item =
        wolfensteinA
    ; itemLabel =
        "Wolfenstein A"
    ; itemLabelIsCanonical =
        refl
    ; status =
        diagnosticNumerical
    ; summary =
        "A diagnostic: geometric-resummation formula recorded at about 0.05 percent error"
    }

vubRow :
  SMContentRow
vubRow =
  record
    { item =
        vubEntry
    ; itemLabel =
        "|V_ub|"
    ; itemLabelIsCanonical =
        refl
    ; status =
        openBlocker
    ; summary =
        "|V_ub| remains open; current degree-28 and NLO-QCD routes are diagnostic hypotheses"
    }

cpPhaseRow :
  SMContentRow
cpPhaseRow =
  record
    { item =
        cpPhase
    ; itemLabel =
        "CKM CP phase"
    ; itemLabelIsCanonical =
        refl
    ; status =
        openBlocker
    ; summary =
        "CP phase remains open; the recorded Hecke-character phase is diagnostic only"
    }

higgsMassRow :
  SMContentRow
higgsMassRow =
  record
    { item =
        higgsMass
    ; itemLabel =
        "Higgs mass"
    ; itemLabelIsCanonical =
        refl
    ; status =
        diagnosticNumerical
    ; summary =
        "Higgs mass is a diagnostic row; no carrier VEV or exact Higgs-sector derivation is supplied"
    }

fourthGenerationMechanismRow :
  SMContentRow
fourthGenerationMechanismRow =
  record
    { item =
        fourthGenerationMechanism
    ; itemLabel =
        "no-fourth-generation mechanism"
    ; itemLabelIsCanonical =
        refl
    ; status =
        openBlocker
    ; summary =
        "absence of a fourth generation remains open; no exclusion mechanism is constructed"
    }

canonicalSMContentRows :
  List SMContentRow
canonicalSMContentRows =
  threeQuarkGenerationRow
  ∷ threeLeptonGenerationRow
  ∷ hyperchargeUnitOneSixthRow
  ∷ u1YContinuityRow
  ∷ su2LLevelOneRow
  ∷ su3CChiralLimitRow
  ∷ lambdaRow
  ∷ wolfensteinARow
  ∷ vubRow
  ∷ cpPhaseRow
  ∷ higgsMassRow
  ∷ fourthGenerationMechanismRow
  ∷ []

summaryBoundaryLabel :
  String
summaryBoundaryLabel =
  "SM content map summary only: structural and diagnostic rows are recorded while all terminal promotions remain false"

record SMContentSummaryReceipt : Set where
  field
    quarkLaneEntries :
      List MatterLaneEntry

    quarkLaneEntriesAreCanonical :
      quarkLaneEntries ≡ canonicalQuarkLaneEntries

    leptonLaneCandidateEntries :
      List MatterLaneEntry

    leptonLaneCandidateEntriesAreCanonical :
      leptonLaneCandidateEntries ≡ canonicalLeptonLaneCandidateEntries

    contentRows :
      List SMContentRow

    contentRowsAreCanonical :
      contentRows ≡ canonicalSMContentRows

    quarkGenerationTripletRecorded :
      Bool

    quarkGenerationTripletRecordedIsTrue :
      quarkGenerationTripletRecorded ≡ true

    leptonGenerationTripletCandidateRecorded :
      Bool

    leptonGenerationTripletCandidateRecordedIsTrue :
      leptonGenerationTripletCandidateRecorded ≡ true

    chargeQuantisationOneSixthDerivedStructurally :
      Bool

    chargeQuantisationOneSixthDerivedStructurallyIsTrue :
      chargeQuantisationOneSixthDerivedStructurally ≡ true

    u1YContinuityOpen :
      Bool

    u1YContinuityOpenIsTrue :
      u1YContinuityOpen ≡ true

    su2LLevelOneCandidateViaCSFlow :
      Bool

    su2LLevelOneCandidateViaCSFlowIsTrue :
      su2LLevelOneCandidateViaCSFlow ≡ true

    su3CApproximateChiralLimitCandidate :
      Bool

    su3CApproximateChiralLimitCandidateIsTrue :
      su3CApproximateChiralLimitCandidate ≡ true

    lambdaDiagnosticRecorded :
      Bool

    lambdaDiagnosticRecordedIsTrue :
      lambdaDiagnosticRecorded ≡ true

    lambdaDiagnosticErrorLabel :
      String

    lambdaDiagnosticErrorLabelIsCanonical :
      lambdaDiagnosticErrorLabel ≡ "0.04 percent diagnostic"

    wolfensteinADiagnosticRecorded :
      Bool

    wolfensteinADiagnosticRecordedIsTrue :
      wolfensteinADiagnosticRecorded ≡ true

    wolfensteinADiagnosticErrorLabel :
      String

    wolfensteinADiagnosticErrorLabelIsCanonical :
      wolfensteinADiagnosticErrorLabel ≡ "0.05 percent diagnostic via geometric resummation"

    vubOpen :
      Bool

    vubOpenIsTrue :
      vubOpen ≡ true

    cpPhaseOpen :
      Bool

    cpPhaseOpenIsTrue :
      cpPhaseOpen ≡ true

    higgsMassDiagnosticRecorded :
      Bool

    higgsMassDiagnosticRecordedIsTrue :
      higgsMassDiagnosticRecorded ≡ true

    fourthGenerationMechanismOpen :
      Bool

    fourthGenerationMechanismOpenIsTrue :
      fourthGenerationMechanismOpen ≡ true

    exactQuarkSectorConstructed :
      Bool

    exactQuarkSectorConstructedIsFalse :
      exactQuarkSectorConstructed ≡ false

    leptonSectorConstructed :
      Bool

    leptonSectorConstructedIsFalse :
      leptonSectorConstructed ≡ false

    u1YContinuousConstructed :
      Bool

    u1YContinuousConstructedIsFalse :
      u1YContinuousConstructed ≡ false

    exactSU2LConstructed :
      Bool

    exactSU2LConstructedIsFalse :
      exactSU2LConstructed ≡ false

    exactSU3CConstructed :
      Bool

    exactSU3CConstructedIsFalse :
      exactSU3CConstructed ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    higgsMassPromoted :
      Bool

    higgsMassPromotedIsFalse :
      higgsMassPromoted ≡ false

    fourthGenerationMechanismConstructed :
      Bool

    fourthGenerationMechanismConstructedIsFalse :
      fourthGenerationMechanismConstructed ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    summaryBoundary :
      String

    summaryBoundaryIsCanonical :
      summaryBoundary ≡ summaryBoundaryLabel

    auditTrail :
      List String

open SMContentSummaryReceipt public

canonicalSMContentSummaryReceipt :
  SMContentSummaryReceipt
canonicalSMContentSummaryReceipt =
  record
    { quarkLaneEntries =
        canonicalQuarkLaneEntries
    ; quarkLaneEntriesAreCanonical =
        refl
    ; leptonLaneCandidateEntries =
        canonicalLeptonLaneCandidateEntries
    ; leptonLaneCandidateEntriesAreCanonical =
        refl
    ; contentRows =
        canonicalSMContentRows
    ; contentRowsAreCanonical =
        refl
    ; quarkGenerationTripletRecorded =
        true
    ; quarkGenerationTripletRecordedIsTrue =
        refl
    ; leptonGenerationTripletCandidateRecorded =
        true
    ; leptonGenerationTripletCandidateRecordedIsTrue =
        refl
    ; chargeQuantisationOneSixthDerivedStructurally =
        true
    ; chargeQuantisationOneSixthDerivedStructurallyIsTrue =
        refl
    ; u1YContinuityOpen =
        true
    ; u1YContinuityOpenIsTrue =
        refl
    ; su2LLevelOneCandidateViaCSFlow =
        true
    ; su2LLevelOneCandidateViaCSFlowIsTrue =
        refl
    ; su3CApproximateChiralLimitCandidate =
        true
    ; su3CApproximateChiralLimitCandidateIsTrue =
        refl
    ; lambdaDiagnosticRecorded =
        true
    ; lambdaDiagnosticRecordedIsTrue =
        refl
    ; lambdaDiagnosticErrorLabel =
        "0.04 percent diagnostic"
    ; lambdaDiagnosticErrorLabelIsCanonical =
        refl
    ; wolfensteinADiagnosticRecorded =
        true
    ; wolfensteinADiagnosticRecordedIsTrue =
        refl
    ; wolfensteinADiagnosticErrorLabel =
        "0.05 percent diagnostic via geometric resummation"
    ; wolfensteinADiagnosticErrorLabelIsCanonical =
        refl
    ; vubOpen =
        true
    ; vubOpenIsTrue =
        refl
    ; cpPhaseOpen =
        true
    ; cpPhaseOpenIsTrue =
        refl
    ; higgsMassDiagnosticRecorded =
        true
    ; higgsMassDiagnosticRecordedIsTrue =
        refl
    ; fourthGenerationMechanismOpen =
        true
    ; fourthGenerationMechanismOpenIsTrue =
        refl
    ; exactQuarkSectorConstructed =
        false
    ; exactQuarkSectorConstructedIsFalse =
        refl
    ; leptonSectorConstructed =
        false
    ; leptonSectorConstructedIsFalse =
        refl
    ; u1YContinuousConstructed =
        false
    ; u1YContinuousConstructedIsFalse =
        refl
    ; exactSU2LConstructed =
        false
    ; exactSU2LConstructedIsFalse =
        refl
    ; exactSU3CConstructed =
        false
    ; exactSU3CConstructedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; higgsMassPromoted =
        false
    ; higgsMassPromotedIsFalse =
        refl
    ; fourthGenerationMechanismConstructed =
        false
    ; fourthGenerationMechanismConstructedIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; summaryBoundary =
        summaryBoundaryLabel
    ; summaryBoundaryIsCanonical =
        refl
    ; auditTrail =
        "Quark lanes recorded: D=-4,D=-3,D=-7 at positions 1-3"
        ∷ "Lepton lanes recorded only as candidates: D=-8,D=-11,D=-12 at positions 4-6"
        ∷ "Charge quantisation unit 1/6 is the finite p3 Z/6 structural row"
        ∷ "Continuous U(1)_Y, exact SU(2)_L, and exact SU(3)_c remain open"
        ∷ "lambda and A are diagnostic numerical rows, while |V_ub| and CP phase remain open"
        ∷ "Higgs mass remains diagnostic and no fourth-generation exclusion mechanism is constructed"
        ∷ "All exact SM, G_DHR ~= G_SM, CKM, Higgs, and terminal promotion flags remain false"
        ∷ []
    }

smContentSummaryKeepsExactSMFalse :
  exactStandardModelPromotion canonicalSMContentSummaryReceipt
  ≡
  false
smContentSummaryKeepsExactSMFalse =
  refl

smContentSummaryKeepsGDHRSMFalse :
  gDHREqualsGSMPromoted canonicalSMContentSummaryReceipt
  ≡
  false
smContentSummaryKeepsGDHRSMFalse =
  refl

smContentSummaryKeepsTerminalFalse :
  terminalClaimPromoted canonicalSMContentSummaryReceipt
  ≡
  false
smContentSummaryKeepsTerminalFalse =
  refl

smContentSummaryKeepsCKMFalse :
  physicalCKMPromoted canonicalSMContentSummaryReceipt
  ≡
  false
smContentSummaryKeepsCKMFalse =
  refl

smContentSummaryRecordsChargeQuantisation :
  chargeQuantisationOneSixthDerivedStructurally canonicalSMContentSummaryReceipt
  ≡
  true
smContentSummaryRecordsChargeQuantisation =
  refl

smContentSummaryRecordsLeptonLanesAsCandidates :
  leptonGenerationTripletCandidateRecorded canonicalSMContentSummaryReceipt
  ≡
  true
smContentSummaryRecordsLeptonLanesAsCandidates =
  refl

smContentSummaryKeepsLeptonSectorUnconstructed :
  leptonSectorConstructed canonicalSMContentSummaryReceipt
  ≡
  false
smContentSummaryKeepsLeptonSectorUnconstructed =
  refl

smContentSummaryRecordsOpenFourthGenerationMechanism :
  fourthGenerationMechanismOpen canonicalSMContentSummaryReceipt
  ≡
  true
smContentSummaryRecordsOpenFourthGenerationMechanism =
  refl
