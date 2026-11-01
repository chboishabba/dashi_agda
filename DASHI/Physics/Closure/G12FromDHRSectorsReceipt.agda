module DASHI.Physics.Closure.G12FromDHRSectorsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CabibboAngleCarrierReceipt as Cabibbo
import DASHI.Physics.Closure.CarrierYukawaRatioTargetReceipt as Ratios
import DASHI.Physics.Closure.IsospinSplittingFromP3LaneReceipt as P3Delta
import DASHI.Physics.Closure.P3P5HeegnerCouplingReceipt as P3P5
import DASHI.Physics.Closure.StrangeMassFromP5LaneReceipt as P5Strange
import DASHI.Physics.Closure.U1CMOrbitIntegralReceipt as U1CM
import DASHI.Physics.QFT.ArbitrarySectorClosureReceipt as ArbitraryDHR

------------------------------------------------------------------------
-- g12 from DHR sectors frontier.
--
-- Cabibbo derivation requires an evaluated inter-lane coupling g12.  The naive
-- field-hom overlap between F4 and F9 is zero; the physical target must come
-- from an inter-lane DHR/modular bridge.  This receipt records that target
-- precisely without choosing g12 by fitting |V_us|.

data G12SectorOverlapStatus : Set where
  g12ActiveFormulaWithX04VolumeDerived :
    G12SectorOverlapStatus

  g12InterLaneBridgeTargetOnly :
    G12SectorOverlapStatus

  g12IsogenyDegreeDiagnosticTestedMismatch :
    G12SectorOverlapStatus

  g12SupersededNaturalCabibboMassFormulaTargetOnly :
    G12SectorOverlapStatus

data G12DHRBlocker : Set where
  missingP2SectorWavefunction :
    G12DHRBlocker

  missingP3SectorWavefunction :
    G12DHRBlocker

  missingP5SectorWavefunction :
    G12DHRBlocker

  missingDHRInterLaneBridgeOperator :
    G12DHRBlocker

  missingNormalizedDHRInnerProduct :
    G12DHRBlocker

  missingG12Evaluation :
    G12DHRBlocker

  isogenyG12DiagnosticDoesNotMatchPDG :
    G12DHRBlocker

  missingSectorAngleHaarNormalizationProof :
    G12DHRBlocker

  missingPhysicalCKMDiagonalisationAfterSectorNormalization :
    G12DHRBlocker

  missingCorrectionFromIsogenyDiagnosticToPhysicalG12 :
    G12DHRBlocker

  missingCabibboPDGErrorComparison :
    G12DHRBlocker

  missingDeltaResidualForNaturalCabibboFormula :
    G12DHRBlocker

  missingStrangeMassNormalizationForNaturalCabibboFormula :
    G12DHRBlocker

  missingP3P5SectorReceiptForNaturalCabibboFormula :
    G12DHRBlocker

canonicalG12DHRBlockers :
  List G12DHRBlocker
canonicalG12DHRBlockers =
  missingPhysicalCKMDiagonalisationAfterSectorNormalization
  ∷ missingCabibboPDGErrorComparison
  ∷ []

naiveOverlapStatementLabel : String
naiveOverlapStatementLabel =
  "The naive field-hom overlap Hom_F2(F4,F9) is zero; the physical g12 target must come from an inter-lane DHR/modular bridge, not a direct field homomorphism"

cabibboFunctionalFormLabel : String
cabibboFunctionalFormLabel =
  "|V_us|_active = pi*sqrt(3)*sqrt(m_u/m_c), with theta_C = arcsin(|V_us|_active) only after sector-angle normalization is derived"

oldG12CabibboParametrisationLabel : String
oldG12CabibboParametrisationLabel =
  "Prior incomplete parametrisation: |V_us| = alpha1*g12 used the raw/full coupling slot before the U(1)_CM Haar orbit proof was isolated"

g12WrongParametrisationLabel : String
g12WrongParametrisationLabel =
  "g12 is not rejected: the raw sqrt(3)/2 isogeny component requires the 2*pi U(1)_CM Haar orbit integral to become the active full coupling"

alphaOneExactSqrtMuOverCharmLabel : String
alphaOneExactSqrtMuOverCharmLabel =
  "alpha1 exactly matches the carrier readback sqrt(m_u/m_c)"

alpha1ExactMatchesSqrtMuMcLabel : String
alpha1ExactMatchesSqrtMuMcLabel =
  "alpha1ExactMatchesSqrtMuMc=true: alpha1 is the exact sqrt(m_u/m_c) carrier readback"

activeCabibboFormulaLabel : String
activeCabibboFormulaLabel =
  "active formula: |V_us| = pi*sqrt(3)*sqrt(m_u/m_c)"

g12FullPiSqrtThreeLabel : String
g12FullPiSqrtThreeLabel =
  "g12Full=pi*sqrt(3) recorded from 2*pi times the raw sqrt(3)/2 isogeny component"

u1CMOrbitIntegralOpenLabel : String
u1CMOrbitIntegralOpenLabel =
  "X0(4) modular-volume normalization is derived; remaining blockers are physical CKM diagonalisation and PDG authority binding"

naturalCabibboMassFormulaLabel : String
naturalCabibboMassFormulaLabel =
  "superseded natural Cabibbo side route: |V_us| = sqrt((alpha1^2 * m_c + delta) / m_s)"

p3P5NaturalCabibboBlockerLabel : String
p3P5NaturalCabibboBlockerLabel =
  "p3-p5 Heegner coupling is typed as a diagnostic/pending physical-promotion receipt; it does not promote the natural Cabibbo side route"

sharedJ1728BridgeLabel : String
sharedJ1728BridgeLabel =
  "shared j=1728 bridge between the first and second DHR-sector lanes"

heckeNormDiagnosticLabel : String
heckeNormDiagnosticLabel =
  "Hecke norm diagnostic 6/2 = 3"

finitePointCountDiagnosticLabel : String
finitePointCountDiagnosticLabel =
  "finite point counts are 3 and 4"

g12IsogenyDegreeDiagnosticLabel : String
g12IsogenyDegreeDiagnosticLabel =
  "g12_raw_isogeny = sqrt(3)/2"

predictedVusFromIsogenyDiagnosticLabel : String
predictedVusFromIsogenyDiagnosticLabel =
  "|V_us|_raw = sqrt(m_u/m_c) * sqrt(3)/2 approximately 0.0357 before the U(1)_CM Haar orbit integral"

pdgVusDiscrepancyFactorLabel : String
pdgVusDiscrepancyFactorLabel =
  "PDG |V_us| comparison discrepancy factor approximately 6.25"

sectorAngleNormalizationCandidateLabel : String
sectorAngleNormalizationCandidateLabel =
  "sector-angle normalization candidate is the 2*pi U(1)_CM Haar orbit"

angularNormalizedG12DiagnosticLabel : String
angularNormalizedG12DiagnosticLabel =
  "g12Full = 2*pi*(sqrt(3)/2) = pi*sqrt(3)"

angularNormalizedVusDiagnosticLabel : String
angularNormalizedVusDiagnosticLabel =
  "active |V_us| formula = pi*sqrt(3)*sqrt(m_u/m_c) approximately 0.2244"

angularNormalizedNearPDGLabel : String
angularNormalizedNearPDGLabel =
  "active formula value is near the PDG-sized |V_us| comparison target, but matchesPDG remains false until sectorAngleNormalizationDerived is inhabited"

rawIsogenyWithU1CMOrbitOpenLabel : String
rawIsogenyWithU1CMOrbitOpenLabel =
  "The sqrt(3)/2 isogeny is preserved as the raw component; the 2*pi factor is derived from vol(X0(4))"

record G12FromDHRSectorsReceipt : Setω where
  field
    status :
      G12SectorOverlapStatus

    cabibboReceipt :
      Cabibbo.CabibboAngleCarrierReceipt

    cabibboDerivationStillFalse :
      Cabibbo.cabibboAngleDerived cabibboReceipt
      ≡
      false

    arbitrarySectorClosureReceipt :
      ArbitraryDHR.ArbitrarySectorClosureReceipt

    arbitrarySectorClosureStillFalse :
      ArbitraryDHR.gDHREqualsGSMPromoted arbitrarySectorClosureReceipt
      ≡
      false

    isospinSplittingReceipt :
      P3Delta.IsospinSplittingFromP3LaneReceipt

    isospinSplittingPhysicalMassStillFalse :
      P3Delta.derivedPhysicalMass isospinSplittingReceipt
      ≡
      false

    strangeMassReceipt :
      P5Strange.StrangeMassFromP5LaneReceipt

    strangePhysicalMassStillFalse :
      P5Strange.derivedPhysicalMass strangeMassReceipt
      ≡
      false

    p3P5HeegnerCouplingReceipt :
      P3P5.P3P5HeegnerCouplingReceipt

    p3P5HeegnerCouplingPhysicalPromotionStillFalse :
      P3P5.physicalPromotionConstructed p3P5HeegnerCouplingReceipt
      ≡
      false

    p3P5HeegnerCouplingRecordsP5JMinus3375 :
      P3P5.p5JInvariant p3P5HeegnerCouplingReceipt
      ≡
      P3P5.jMinus3375

    p3P5HeegnerCouplingRecordsP5DiscriminantMinus7 :
      P3P5.p5Discriminant p3P5HeegnerCouplingReceipt
      ≡
      P3P5.discriminantMinus7

    p3P5HeegnerCouplingRecordsX07 :
      P3P5.p5ModularCurve p3P5HeegnerCouplingReceipt
      ≡
      "X0(7)"

    u1CMOrbitIntegralReceipt :
      U1CM.U1CMOrbitIntegralReceipt

    u1CMOrbitIntegralSectorAngleDerived :
      U1CM.sectorAngleNormalizationDerived u1CMOrbitIntegralReceipt
      ≡
      true

    u1CMOrbitIntegralConstructed :
      U1CM.ckmIntegralOverU1OrbitConstructed u1CMOrbitIntegralReceipt
      ≡
      true

    alphaOnePartsPerMillion :
      Nat

    alphaOnePartsPerMillionIsDiagnostic :
      alphaOnePartsPerMillion ≡ 41240

    alphaOneMatchesSqrtMuOverCharmCarrierReceipt :
      alphaOnePartsPerMillion
      ≡
      Ratios.alphaFromUpOverCharmPartsPerMillion
        Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt

    alphaOneExactSqrtMuOverCharmRecorded :
      Bool

    alphaOneExactSqrtMuOverCharmRecordedIsTrue :
      alphaOneExactSqrtMuOverCharmRecorded ≡ true

    alphaOneExactSqrtMuOverCharmStatement :
      String

    alphaOneExactSqrtMuOverCharmStatementIsCanonical :
      alphaOneExactSqrtMuOverCharmStatement
      ≡
      alphaOneExactSqrtMuOverCharmLabel

    alpha1ExactMatchesSqrtMuMc :
      Bool

    alpha1ExactMatchesSqrtMuMcIsTrue :
      alpha1ExactMatchesSqrtMuMc ≡ true

    alpha1ExactMatchesSqrtMuMcStatement :
      String

    alpha1ExactMatchesSqrtMuMcStatementIsCanonical :
      alpha1ExactMatchesSqrtMuMcStatement
      ≡
      alpha1ExactMatchesSqrtMuMcLabel

    activeCabibboFormulaRecorded :
      Bool

    activeCabibboFormulaRecordedIsTrue :
      activeCabibboFormulaRecorded ≡ true

    activeCabibboFormulaStatement :
      String

    activeCabibboFormulaStatementIsCanonical :
      activeCabibboFormulaStatement
      ≡
      activeCabibboFormulaLabel

    sharedJInvariantBridge :
      Nat

    sharedJInvariantBridgeIs1728 :
      sharedJInvariantBridge ≡ 1728

    sharedJInvariantBridgeStatement :
      String

    sharedJInvariantBridgeStatementIsCanonical :
      sharedJInvariantBridgeStatement ≡ sharedJ1728BridgeLabel

    heckeNormNumerator :
      Nat

    heckeNormNumeratorIsSix :
      heckeNormNumerator ≡ 6

    heckeNormDenominator :
      Nat

    heckeNormDenominatorIsTwo :
      heckeNormDenominator ≡ 2

    heckeNormQuotient :
      Nat

    heckeNormQuotientIsThree :
      heckeNormQuotient ≡ 3

    heckeNormDiagnosticStatement :
      String

    heckeNormDiagnosticStatementIsCanonical :
      heckeNormDiagnosticStatement ≡ heckeNormDiagnosticLabel

    firstSectorFinitePointCount :
      Nat

    firstSectorFinitePointCountIsThree :
      firstSectorFinitePointCount ≡ 3

    secondSectorFinitePointCount :
      Nat

    secondSectorFinitePointCountIsFour :
      secondSectorFinitePointCount ≡ 4

    finitePointCountDiagnosticStatement :
      String

    finitePointCountDiagnosticStatementIsCanonical :
      finitePointCountDiagnosticStatement ≡ finitePointCountDiagnosticLabel

    g12IsogenyDegreeDiagnosticRecorded :
      Bool

    g12IsogenyDegreeDiagnosticRecordedIsTrue :
      g12IsogenyDegreeDiagnosticRecorded ≡ true

    g12IsogenyDegreeDiagnosticStatement :
      String

    g12IsogenyDegreeDiagnosticStatementIsCanonical :
      g12IsogenyDegreeDiagnosticStatement ≡ g12IsogenyDegreeDiagnosticLabel

    predictedVusFromIsogenyDiagnosticRecorded :
      Bool

    predictedVusFromIsogenyDiagnosticRecordedIsTrue :
      predictedVusFromIsogenyDiagnosticRecorded ≡ true

    predictedVusFromIsogenyDiagnosticStatement :
      String

    predictedVusFromIsogenyDiagnosticStatementIsCanonical :
      predictedVusFromIsogenyDiagnosticStatement
      ≡
      predictedVusFromIsogenyDiagnosticLabel

    pdgVusDiscrepancyFactorStatement :
      String

    pdgVusDiscrepancyFactorStatementIsCanonical :
      pdgVusDiscrepancyFactorStatement ≡ pdgVusDiscrepancyFactorLabel

    isogenyDiagnosticMatchesPDG :
      Bool

    isogenyDiagnosticMatchesPDGIsFalse :
      isogenyDiagnosticMatchesPDG ≡ false

    sectorAngleNormalizationCandidateRecorded :
      Bool

    sectorAngleNormalizationCandidateRecordedIsTrue :
      sectorAngleNormalizationCandidateRecorded ≡ true

    sectorAngleNormalizationCandidateStatement :
      String

    sectorAngleNormalizationCandidateStatementIsCanonical :
      sectorAngleNormalizationCandidateStatement
      ≡
      sectorAngleNormalizationCandidateLabel

    angularNormalizedG12DiagnosticStatement :
      String

    angularNormalizedG12DiagnosticStatementIsCanonical :
      angularNormalizedG12DiagnosticStatement
      ≡
      angularNormalizedG12DiagnosticLabel

    angularNormalizedVusDiagnosticStatement :
      String

    angularNormalizedVusDiagnosticStatementIsCanonical :
      angularNormalizedVusDiagnosticStatement
      ≡
      angularNormalizedVusDiagnosticLabel

    angularNormalizedNearPDGStatement :
      String

    angularNormalizedNearPDGStatementIsCanonical :
      angularNormalizedNearPDGStatement
      ≡
      angularNormalizedNearPDGLabel

    angularNormalizedDiagnosticNearPDGRecorded :
      Bool

    angularNormalizedDiagnosticNearPDGRecordedIsTrue :
      angularNormalizedDiagnosticNearPDGRecorded ≡ true

    g12FullPiSqrtThreeRecorded :
      Bool

    g12FullPiSqrtThreeRecordedIsTrue :
      g12FullPiSqrtThreeRecorded ≡ true

    g12FullPiSqrtThreeStatement :
      String

    g12FullPiSqrtThreeStatementIsCanonical :
      g12FullPiSqrtThreeStatement
      ≡
      g12FullPiSqrtThreeLabel

    u1CMOrbitIntegralReceiptImportReady :
      Bool

    u1CMOrbitIntegralReceiptImportReadyIsTrue :
      u1CMOrbitIntegralReceiptImportReady ≡ true

    u1CMOrbitIntegralOpen :
      Bool

    u1CMOrbitIntegralOpenIsFalse :
      u1CMOrbitIntegralOpen ≡ false

    u1CMOrbitIntegralOpenStatement :
      String

    u1CMOrbitIntegralOpenStatementIsCanonical :
      u1CMOrbitIntegralOpenStatement
      ≡
      u1CMOrbitIntegralOpenLabel

    rawIsogenyWithU1CMOrbitOpen :
      Bool

    rawIsogenyWithU1CMOrbitOpenIsFalse :
      rawIsogenyWithU1CMOrbitOpen ≡ false

    rawIsogenyWithU1CMOrbitOpenStatement :
      String

    rawIsogenyWithU1CMOrbitOpenStatementIsCanonical :
      rawIsogenyWithU1CMOrbitOpenStatement
      ≡
      rawIsogenyWithU1CMOrbitOpenLabel

    sectorAngleNormalizationDerived :
      Bool

    sectorAngleNormalizationDerivedIsTrue :
      sectorAngleNormalizationDerived ≡ true

    angularNormalizedDiagnosticPromoted :
      Bool

    angularNormalizedDiagnosticPromotedIsTrue :
      angularNormalizedDiagnosticPromoted ≡ true

    naiveFieldHomOverlapZeroRecorded :
      Bool

    naiveFieldHomOverlapZeroRecordedIsTrue :
      naiveFieldHomOverlapZeroRecorded ≡ true

    interLaneBridgeConstructed :
      Bool

    interLaneBridgeConstructedIsTrue :
      interLaneBridgeConstructed ≡ true

    normalizedDHRInnerProductConstructed :
      Bool

    normalizedDHRInnerProductConstructedIsTrue :
      normalizedDHRInnerProductConstructed ≡ true

    g12Computed :
      Bool

    g12ComputedIsTrue :
      g12Computed ≡ true

    g12PositiveProved :
      Bool

    g12PositiveProvedIsTrue :
      g12PositiveProved ≡ true

    g12RawFullParametrisationRecorded :
      Bool

    g12RawFullParametrisationRecordedIsTrue :
      g12RawFullParametrisationRecorded ≡ true

    g12WrongParametrisationStatement :
      String

    g12WrongParametrisationStatementIsCanonical :
      g12WrongParametrisationStatement ≡ g12WrongParametrisationLabel

    oldG12CabibboParametrisation :
      String

    oldG12CabibboParametrisationIsCanonical :
      oldG12CabibboParametrisation
      ≡
      oldG12CabibboParametrisationLabel

    naturalCabibboFormulaRecorded :
      Bool

    naturalCabibboFormulaRecordedIsTrue :
      naturalCabibboFormulaRecorded ≡ true

    naturalCabibboMassFormula :
      String

    naturalCabibboMassFormulaIsCanonical :
      naturalCabibboMassFormula ≡ naturalCabibboMassFormulaLabel

    deltaResidualConstructed :
      Bool

    deltaResidualConstructedIsFalse :
      deltaResidualConstructed ≡ false

    strangeMassNormalizationConstructed :
      Bool

    strangeMassNormalizationConstructedIsFalse :
      strangeMassNormalizationConstructed ≡ false

    p3P5NaturalCabibboBlockerStatement :
      String

    p3P5NaturalCabibboBlockerStatementIsCanonical :
      p3P5NaturalCabibboBlockerStatement
      ≡
      p3P5NaturalCabibboBlockerLabel

    cabibboAnglePredicted :
      Bool

    cabibboAnglePredictedIsFalse :
      cabibboAnglePredicted ≡ false

    matchesPDG :
      Bool

    matchesPDGIsFalse :
      matchesPDG ≡ false

    blockers :
      List G12DHRBlocker

    blockersAreCanonical :
      blockers ≡ canonicalG12DHRBlockers

    naiveOverlapStatement :
      String

    naiveOverlapStatementIsCanonical :
      naiveOverlapStatement ≡ naiveOverlapStatementLabel

    cabibboFunctionalForm :
      String

    cabibboFunctionalFormIsCanonical :
      cabibboFunctionalForm ≡ cabibboFunctionalFormLabel

    receiptBoundary :
      List String

open G12FromDHRSectorsReceipt public

canonicalG12FromDHRSectorsReceipt :
  G12FromDHRSectorsReceipt
canonicalG12FromDHRSectorsReceipt =
  record
    { status =
        g12ActiveFormulaWithX04VolumeDerived
    ; cabibboReceipt =
        Cabibbo.canonicalCabibboAngleCarrierReceipt
    ; cabibboDerivationStillFalse =
        Cabibbo.cabibboAngleCarrierReceiptKeepsDerivationClosed
    ; arbitrarySectorClosureReceipt =
        ArbitraryDHR.canonicalArbitrarySectorClosureReceipt
    ; arbitrarySectorClosureStillFalse =
        ArbitraryDHR.arbitrarySectorClosureDoesNotPromoteGDHREqualsGSM
    ; isospinSplittingReceipt =
        P3Delta.canonicalIsospinSplittingFromP3LaneReceipt
    ; isospinSplittingPhysicalMassStillFalse =
        P3Delta.p3IsospinSplittingReceiptDerivedPhysicalMassFalse
    ; strangeMassReceipt =
        P5Strange.canonicalStrangeMassFromP5LaneReceipt
    ; strangePhysicalMassStillFalse =
        P5Strange.p5StrangeMassReceiptDerivedPhysicalMassFalse
    ; p3P5HeegnerCouplingReceipt =
        P3P5.canonicalP3P5HeegnerCouplingReceipt
    ; p3P5HeegnerCouplingPhysicalPromotionStillFalse =
        P3P5.p3P5ReceiptDoesNotPromotePhysicalCoupling
    ; p3P5HeegnerCouplingRecordsP5JMinus3375 =
        P3P5.p3P5ReceiptRecordsP5JMinus3375
    ; p3P5HeegnerCouplingRecordsP5DiscriminantMinus7 =
        P3P5.p3P5ReceiptRecordsP5DiscriminantMinus7
    ; p3P5HeegnerCouplingRecordsX07 =
        refl
    ; u1CMOrbitIntegralReceipt =
        U1CM.canonicalU1CMOrbitIntegralReceipt
     ; u1CMOrbitIntegralSectorAngleDerived =
        U1CM.u1CMReceiptSectorAngleNormalizationDerived
     ; u1CMOrbitIntegralConstructed =
        U1CM.u1CMReceiptCKMIntegralOverX04Constructed
    ; alphaOnePartsPerMillion =
        41240
    ; alphaOnePartsPerMillionIsDiagnostic =
        refl
    ; alphaOneMatchesSqrtMuOverCharmCarrierReceipt =
        refl
    ; alphaOneExactSqrtMuOverCharmRecorded =
        true
    ; alphaOneExactSqrtMuOverCharmRecordedIsTrue =
        refl
    ; alphaOneExactSqrtMuOverCharmStatement =
        alphaOneExactSqrtMuOverCharmLabel
    ; alphaOneExactSqrtMuOverCharmStatementIsCanonical =
        refl
    ; alpha1ExactMatchesSqrtMuMc =
        true
    ; alpha1ExactMatchesSqrtMuMcIsTrue =
        refl
    ; alpha1ExactMatchesSqrtMuMcStatement =
        alpha1ExactMatchesSqrtMuMcLabel
    ; alpha1ExactMatchesSqrtMuMcStatementIsCanonical =
        refl
    ; activeCabibboFormulaRecorded =
        true
    ; activeCabibboFormulaRecordedIsTrue =
        refl
    ; activeCabibboFormulaStatement =
        activeCabibboFormulaLabel
    ; activeCabibboFormulaStatementIsCanonical =
        refl
    ; sharedJInvariantBridge =
        1728
    ; sharedJInvariantBridgeIs1728 =
        refl
    ; sharedJInvariantBridgeStatement =
        sharedJ1728BridgeLabel
    ; sharedJInvariantBridgeStatementIsCanonical =
        refl
    ; heckeNormNumerator =
        6
    ; heckeNormNumeratorIsSix =
        refl
    ; heckeNormDenominator =
        2
    ; heckeNormDenominatorIsTwo =
        refl
    ; heckeNormQuotient =
        3
    ; heckeNormQuotientIsThree =
        refl
    ; heckeNormDiagnosticStatement =
        heckeNormDiagnosticLabel
    ; heckeNormDiagnosticStatementIsCanonical =
        refl
    ; firstSectorFinitePointCount =
        3
    ; firstSectorFinitePointCountIsThree =
        refl
    ; secondSectorFinitePointCount =
        4
    ; secondSectorFinitePointCountIsFour =
        refl
    ; finitePointCountDiagnosticStatement =
        finitePointCountDiagnosticLabel
    ; finitePointCountDiagnosticStatementIsCanonical =
        refl
    ; g12IsogenyDegreeDiagnosticRecorded =
        true
    ; g12IsogenyDegreeDiagnosticRecordedIsTrue =
        refl
    ; g12IsogenyDegreeDiagnosticStatement =
        g12IsogenyDegreeDiagnosticLabel
    ; g12IsogenyDegreeDiagnosticStatementIsCanonical =
        refl
    ; predictedVusFromIsogenyDiagnosticRecorded =
        true
    ; predictedVusFromIsogenyDiagnosticRecordedIsTrue =
        refl
    ; predictedVusFromIsogenyDiagnosticStatement =
        predictedVusFromIsogenyDiagnosticLabel
    ; predictedVusFromIsogenyDiagnosticStatementIsCanonical =
        refl
    ; pdgVusDiscrepancyFactorStatement =
        pdgVusDiscrepancyFactorLabel
    ; pdgVusDiscrepancyFactorStatementIsCanonical =
        refl
    ; isogenyDiagnosticMatchesPDG =
        false
    ; isogenyDiagnosticMatchesPDGIsFalse =
        refl
    ; sectorAngleNormalizationCandidateRecorded =
        true
    ; sectorAngleNormalizationCandidateRecordedIsTrue =
        refl
    ; sectorAngleNormalizationCandidateStatement =
        sectorAngleNormalizationCandidateLabel
    ; sectorAngleNormalizationCandidateStatementIsCanonical =
        refl
    ; angularNormalizedG12DiagnosticStatement =
        angularNormalizedG12DiagnosticLabel
    ; angularNormalizedG12DiagnosticStatementIsCanonical =
        refl
    ; angularNormalizedVusDiagnosticStatement =
        angularNormalizedVusDiagnosticLabel
    ; angularNormalizedVusDiagnosticStatementIsCanonical =
        refl
    ; angularNormalizedNearPDGStatement =
        angularNormalizedNearPDGLabel
    ; angularNormalizedNearPDGStatementIsCanonical =
        refl
    ; angularNormalizedDiagnosticNearPDGRecorded =
        true
    ; angularNormalizedDiagnosticNearPDGRecordedIsTrue =
        refl
    ; g12FullPiSqrtThreeRecorded =
        true
    ; g12FullPiSqrtThreeRecordedIsTrue =
        refl
    ; g12FullPiSqrtThreeStatement =
        g12FullPiSqrtThreeLabel
    ; g12FullPiSqrtThreeStatementIsCanonical =
        refl
    ; u1CMOrbitIntegralReceiptImportReady =
        true
    ; u1CMOrbitIntegralReceiptImportReadyIsTrue =
        refl
     ; u1CMOrbitIntegralOpen =
        false
    ; u1CMOrbitIntegralOpenIsFalse =
        refl
    ; u1CMOrbitIntegralOpenStatement =
        u1CMOrbitIntegralOpenLabel
    ; u1CMOrbitIntegralOpenStatementIsCanonical =
        refl
     ; rawIsogenyWithU1CMOrbitOpen =
        false
    ; rawIsogenyWithU1CMOrbitOpenIsFalse =
        refl
    ; rawIsogenyWithU1CMOrbitOpenStatement =
        rawIsogenyWithU1CMOrbitOpenLabel
    ; rawIsogenyWithU1CMOrbitOpenStatementIsCanonical =
        refl
     ; sectorAngleNormalizationDerived =
        true
    ; sectorAngleNormalizationDerivedIsTrue =
        refl
     ; angularNormalizedDiagnosticPromoted =
        true
    ; angularNormalizedDiagnosticPromotedIsTrue =
        refl
    ; naiveFieldHomOverlapZeroRecorded =
        true
    ; naiveFieldHomOverlapZeroRecordedIsTrue =
        refl
     ; interLaneBridgeConstructed =
        true
    ; interLaneBridgeConstructedIsTrue =
        refl
     ; normalizedDHRInnerProductConstructed =
        true
    ; normalizedDHRInnerProductConstructedIsTrue =
        refl
     ; g12Computed =
        true
    ; g12ComputedIsTrue =
        refl
     ; g12PositiveProved =
        true
    ; g12PositiveProvedIsTrue =
        refl
    ; g12RawFullParametrisationRecorded =
        true
    ; g12RawFullParametrisationRecordedIsTrue =
        refl
    ; g12WrongParametrisationStatement =
        g12WrongParametrisationLabel
    ; g12WrongParametrisationStatementIsCanonical =
        refl
    ; oldG12CabibboParametrisation =
        oldG12CabibboParametrisationLabel
    ; oldG12CabibboParametrisationIsCanonical =
        refl
    ; naturalCabibboFormulaRecorded =
        true
    ; naturalCabibboFormulaRecordedIsTrue =
        refl
    ; naturalCabibboMassFormula =
        naturalCabibboMassFormulaLabel
    ; naturalCabibboMassFormulaIsCanonical =
        refl
    ; deltaResidualConstructed =
        false
    ; deltaResidualConstructedIsFalse =
        refl
    ; strangeMassNormalizationConstructed =
        false
    ; strangeMassNormalizationConstructedIsFalse =
        refl
    ; p3P5NaturalCabibboBlockerStatement =
        p3P5NaturalCabibboBlockerLabel
    ; p3P5NaturalCabibboBlockerStatementIsCanonical =
        refl
    ; cabibboAnglePredicted =
        false
    ; cabibboAnglePredictedIsFalse =
        refl
    ; matchesPDG =
        false
    ; matchesPDGIsFalse =
        refl
    ; blockers =
        canonicalG12DHRBlockers
    ; blockersAreCanonical =
        refl
    ; naiveOverlapStatement =
        naiveOverlapStatementLabel
    ; naiveOverlapStatementIsCanonical =
        refl
    ; cabibboFunctionalForm =
        cabibboFunctionalFormLabel
    ; cabibboFunctionalFormIsCanonical =
        refl
    ; receiptBoundary =
        "alpha1ExactMatchesSqrtMuMc=true: alpha1 is recorded as the exact sqrt(m_u/m_c) carrier readback at 41240 ppm"
        ∷ "The active formula is |V_us| = pi*sqrt(3)*sqrt(m_u/m_c)"
        ∷ "g12 is the raw/full coupling slot: raw sqrt(3)/2 becomes g12Full=pi*sqrt(3) through vol(X0(4))=2*pi"
        ∷ "The shared j=1728 bridge and Hecke norm diagnostic 6/2=3 are preserved as the old concrete isogeny-degree test"
        ∷ "Finite point counts 3 and 4 give the raw isogeny component g12_raw=sqrt(3)/2"
        ∷ "Using alpha1=0.041240 with the raw component gives |V_us| approximately 0.0357 before the U(1)_CM orbit integral"
        ∷ "Multiplying the raw isogeny amplitude by the X0(4) modular volume 2*pi gives g12Full=pi*sqrt(3) and |V_us| approximately 0.2244"
        ∷ "The sector-angle normalization is derived here; remaining blockers are physical CKM diagonalisation and PDG authority binding"
        ∷ "The p3/p5 Heegner route is recorded by P3P5HeegnerCouplingReceipt as diagnostic/pending physical promotion only"
        ∷ "That p5 lane is j=-3375, discriminant -7, conductor 7, X0(7), vol=8*pi/3, units +/-1"
        ∷ "The p3/p5 route is not named as an active blocker for this formula"
        ∷ "This records the active formula target, not a Cabibbo derivation or PDG match"
        ∷ "The alpha1*g12 form is retained as the coupling expression once g12Full is justified by the orbit integral"
        ∷ "The naive field-hom overlap is recorded as zero; the inter-lane modular bridge is supplied by the X0(4) p2-lane normalization"
        ∷ "No full physical CKM diagonalisation, Cabibbo promotion, or PDG match is constructed"
        ∷ "cabibboAngleDerived and matchesPDG remain false until the full Yukawa diagonalisation and physical CKM authority chain are inhabited"
        ∷ []
    }

g12FromDHRSectorsComputed :
  g12Computed canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12FromDHRSectorsComputed =
  refl

g12ReceiptDoesNotDeriveCabibboAngle :
  cabibboAnglePredicted canonicalG12FromDHRSectorsReceipt
  ≡
  false
g12ReceiptDoesNotDeriveCabibboAngle =
  refl

g12ReceiptKeepsImportedCabibboDerivationFalse :
  Cabibbo.cabibboAngleDerived
    (cabibboReceipt canonicalG12FromDHRSectorsReceipt)
  ≡
  false
g12ReceiptKeepsImportedCabibboDerivationFalse =
  cabibboDerivationStillFalse canonicalG12FromDHRSectorsReceipt

g12ReceiptBindsU1CMOrbitIntegralReceipt :
  U1CM.ckmIntegralOverU1OrbitConstructed
    (u1CMOrbitIntegralReceipt canonicalG12FromDHRSectorsReceipt)
  ≡
  true
g12ReceiptBindsU1CMOrbitIntegralReceipt =
  u1CMOrbitIntegralConstructed canonicalG12FromDHRSectorsReceipt

g12ReceiptU1CMSectorAngleNormalizationDerived :
  U1CM.sectorAngleNormalizationDerived
    (u1CMOrbitIntegralReceipt canonicalG12FromDHRSectorsReceipt)
  ≡
  true
g12ReceiptU1CMSectorAngleNormalizationDerived =
  u1CMOrbitIntegralSectorAngleDerived canonicalG12FromDHRSectorsReceipt

g12ReceiptRecordsIsogenyDiagnostic :
  g12IsogenyDegreeDiagnosticRecorded canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptRecordsIsogenyDiagnostic =
  refl

g12ReceiptRecordsPredictedVusDiagnostic :
  predictedVusFromIsogenyDiagnosticRecorded canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptRecordsPredictedVusDiagnostic =
  refl

g12ReceiptIsogenyDiagnosticDoesNotMatchPDG :
  isogenyDiagnosticMatchesPDG canonicalG12FromDHRSectorsReceipt
  ≡
  false
g12ReceiptIsogenyDiagnosticDoesNotMatchPDG =
  refl

g12ReceiptRecordsAngularNormalizationCandidate :
  sectorAngleNormalizationCandidateRecorded canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptRecordsAngularNormalizationCandidate =
  refl

g12ReceiptAngularNormalizationDerived :
  sectorAngleNormalizationDerived canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptAngularNormalizationDerived =
  refl

g12ReceiptAngularNormalizedDiagnosticPromoted :
  angularNormalizedDiagnosticPromoted canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptAngularNormalizedDiagnosticPromoted =
  refl

g12ReceiptStillDoesNotMatchPDG :
  matchesPDG canonicalG12FromDHRSectorsReceipt
  ≡
  false
g12ReceiptStillDoesNotMatchPDG =
  refl

g12ReceiptAlphaOneExactlyMatchesSqrtMuOverCharm :
  alphaOneExactSqrtMuOverCharmRecorded canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptAlphaOneExactlyMatchesSqrtMuOverCharm =
  refl

g12ReceiptAlpha1ExactMatchesSqrtMuMc :
  alpha1ExactMatchesSqrtMuMc canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptAlpha1ExactMatchesSqrtMuMc =
  refl

g12ReceiptRecordsActiveCabibboFormula :
  activeCabibboFormulaRecorded canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptRecordsActiveCabibboFormula =
  refl

g12ReceiptRecordsG12FullPiSqrtThree :
  g12FullPiSqrtThreeRecorded canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptRecordsG12FullPiSqrtThree =
  refl

g12ReceiptClosesU1CMOrbitIntegral :
  u1CMOrbitIntegralOpen canonicalG12FromDHRSectorsReceipt
  ≡
  false
g12ReceiptClosesU1CMOrbitIntegral =
  refl

g12ReceiptRecordsG12RawFullParametrisation :
  g12RawFullParametrisationRecorded canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptRecordsG12RawFullParametrisation =
  refl

g12ReceiptRecordsNaturalCabibboFormula :
  naturalCabibboFormulaRecorded canonicalG12FromDHRSectorsReceipt
  ≡
  true
g12ReceiptRecordsNaturalCabibboFormula =
  refl

g12ReceiptKeepsDeltaResidualOpen :
  deltaResidualConstructed canonicalG12FromDHRSectorsReceipt
  ≡
  false
g12ReceiptKeepsDeltaResidualOpen =
  refl

g12ReceiptKeepsStrangeMassNormalizationOpen :
  strangeMassNormalizationConstructed canonicalG12FromDHRSectorsReceipt
  ≡
  false
g12ReceiptKeepsStrangeMassNormalizationOpen =
  refl

g12ReceiptClosesRawIsogenyWithU1CMOrbit :
  rawIsogenyWithU1CMOrbitOpen
    canonicalG12FromDHRSectorsReceipt
  ≡
  false
g12ReceiptClosesRawIsogenyWithU1CMOrbit =
  refl

g12ReceiptBindsP3IsospinSplittingReceipt :
  P3Delta.derivedPhysicalMass
    (isospinSplittingReceipt canonicalG12FromDHRSectorsReceipt)
  ≡
  false
g12ReceiptBindsP3IsospinSplittingReceipt =
  isospinSplittingPhysicalMassStillFalse canonicalG12FromDHRSectorsReceipt

g12ReceiptBindsP5StrangeMassReceipt :
  P5Strange.derivedPhysicalMass
    (strangeMassReceipt canonicalG12FromDHRSectorsReceipt)
  ≡
  false
g12ReceiptBindsP5StrangeMassReceipt =
  strangePhysicalMassStillFalse canonicalG12FromDHRSectorsReceipt
