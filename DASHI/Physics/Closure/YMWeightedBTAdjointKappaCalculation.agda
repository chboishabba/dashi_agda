module DASHI.Physics.Closure.YMWeightedBTAdjointKappaCalculation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _-_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.BTFiniteMetricGaugeCompatibilityKappaBoundary as Kappa
import DASHI.Physics.Closure.FiniteGaugeHodgeAdjointCompatibility as Adj
import DASHI.Physics.Closure.YMBTMetricRatioDefectGapFinite as FiniteGap

------------------------------------------------------------------------
-- Weighted BT adjoint/kappa calculation boundary.
--
-- This module refines the finite Hodge/Yang-Mills route by recording the
-- concrete weighted primal/dual metric-ratio target
--
--   w(sigma^k_d) / wDual(sigma^(n-k)_d) = p ^ ((n - 2k) * d),
--
-- together with the finite prime-sample kappa rows
--
--   kappa_p = (p - 1)^2 / p^2
--
-- for p = 2, 3, 5.  It consumes the finite selected Hodge adjoint boundary,
-- the BT metric/gauge kappa boundary, and the existing finite kappa sample
-- receipt.  It does not prove the metric weighted adjoint theorem, the
-- uniform positive infimum, the self-adjoint Hamiltonian quotient, continuum
-- transfer, or Clay Yang-Mills.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

pow : Nat → Nat → Nat
pow base zero =
  1
pow base (suc exponent) =
  base * pow base exponent

double : Nat → Nat
double k =
  2 * k

metricRatioExponent : Nat → Nat → Nat → Nat
metricRatioExponent n k d =
  (n - double k) * d

metricRatioPower : Nat → Nat → Nat → Nat → Nat
metricRatioPower p n k d =
  pow p (metricRatioExponent n k d)

data WeightedBTAdjointKappaCalculationStatus : Set where
  weightedBTAdjointKappaFiniteCalculationRecordedPromotionBlocked :
    WeightedBTAdjointKappaCalculationStatus

data BTDimension : Set where
  btDimension4 :
    BTDimension

dimensionNat : BTDimension → Nat
dimensionNat btDimension4 =
  4

data FormDegree : Set where
  degree1GaugePotential :
    FormDegree
  degree2Curvature :
    FormDegree

degreeNat : FormDegree → Nat
degreeNat degree1GaugePotential =
  1
degreeNat degree2Curvature =
  2

data BTAdjointDepth : Set where
  depth0 :
    BTAdjointDepth
  depth1 :
    BTAdjointDepth
  depth2 :
    BTAdjointDepth
  arbitraryDepth :
    BTAdjointDepth

depthNat : BTAdjointDepth → Nat
depthNat depth0 =
  0
depthNat depth1 =
  1
depthNat depth2 =
  2
depthNat arbitraryDepth =
  0

canonicalFiniteDepths : List BTAdjointDepth
canonicalFiniteDepths =
  depth0
  ∷ depth1
  ∷ depth2
  ∷ []

data WeightedBTMetricRatioTarget : Set where
  weightedBTMetricRatioTarget :
    (p n k d : Nat) →
    (ratioPower : Nat) →
    ratioPower ≡ metricRatioPower p n k d →
    WeightedBTMetricRatioTarget

canonicalP2N4K1D0RatioTarget :
  WeightedBTMetricRatioTarget
canonicalP2N4K1D0RatioTarget =
  weightedBTMetricRatioTarget
    2
    4
    1
    0
    (metricRatioPower 2 4 1 0)
    refl

canonicalP2N4K1D1RatioTarget :
  WeightedBTMetricRatioTarget
canonicalP2N4K1D1RatioTarget =
  weightedBTMetricRatioTarget
    2
    4
    1
    1
    (metricRatioPower 2 4 1 1)
    refl

canonicalP2N4K1D2RatioTarget :
  WeightedBTMetricRatioTarget
canonicalP2N4K1D2RatioTarget =
  weightedBTMetricRatioTarget
    2
    4
    1
    2
    (metricRatioPower 2 4 1 2)
    refl

p2N4K1D0RatioIsOne :
  metricRatioPower 2 4 1 0 ≡ 1
p2N4K1D0RatioIsOne =
  refl

p2N4K1D1RatioIsFour :
  metricRatioPower 2 4 1 1 ≡ 4
p2N4K1D1RatioIsFour =
  refl

p2N4K1D2RatioIsSixteen :
  metricRatioPower 2 4 1 2 ≡ 16
p2N4K1D2RatioIsSixteen =
  refl

p3N4K1D1RatioIsNine :
  metricRatioPower 3 4 1 1 ≡ 9
p3N4K1D1RatioIsNine =
  refl

p5N4K1D1RatioIsTwentyFive :
  metricRatioPower 5 4 1 1 ≡ 25
p5N4K1D1RatioIsTwentyFive =
  refl

data WeightedBTMetricRatioRow : Set where
  weightedBTMetricRatioRow :
    BTDimension →
    FormDegree →
    BTAdjointDepth →
    FiniteGap.PrimeSample →
    WeightedBTMetricRatioTarget →
    WeightedBTMetricRatioRow

canonicalMetricRatioRows : List WeightedBTMetricRatioRow
canonicalMetricRatioRows =
  weightedBTMetricRatioRow
    btDimension4
    degree1GaugePotential
    depth0
    FiniteGap.p2
    canonicalP2N4K1D0RatioTarget
  ∷ weightedBTMetricRatioRow
    btDimension4
    degree1GaugePotential
    depth1
    FiniteGap.p2
    canonicalP2N4K1D1RatioTarget
  ∷ weightedBTMetricRatioRow
    btDimension4
    degree1GaugePotential
    depth2
    FiniteGap.p2
    canonicalP2N4K1D2RatioTarget
  ∷ []

record ImportedFiniteKappaSampleRows : Set where
  constructor mkImportedFiniteKappaSampleRows
  field
    p2Row :
      FiniteGap.FinitePrimeKappaRow
    p2RowIsCanonical :
      p2Row ≡ FiniteGap.p2KappaRow
    p3Row :
      FiniteGap.FinitePrimeKappaRow
    p3RowIsCanonical :
      p3Row ≡ FiniteGap.p3KappaRow
    p5Row :
      FiniteGap.FinitePrimeKappaRow
    p5RowIsCanonical :
      p5Row ≡ FiniteGap.p5KappaRow
    rows :
      List FiniteGap.FinitePrimeKappaRow
    rowsAreCanonical :
      rows ≡ FiniteGap.canonicalFinitePrimeKappaRows

open ImportedFiniteKappaSampleRows public

canonicalImportedFiniteKappaSampleRows :
  ImportedFiniteKappaSampleRows
canonicalImportedFiniteKappaSampleRows =
  mkImportedFiniteKappaSampleRows
    FiniteGap.p2KappaRow
    refl
    FiniteGap.p3KappaRow
    refl
    FiniteGap.p5KappaRow
    refl
    FiniteGap.canonicalFinitePrimeKappaRows
    refl

data YMWeightedBTAdjointKappaRow : Set where
  finiteGaugeHodgeAdjointCompatibilityConsumedRow :
    YMWeightedBTAdjointKappaRow
  btFiniteMetricGaugeKappaBoundaryConsumedRow :
    YMWeightedBTAdjointKappaRow
  finiteMetricRatioDefectGapSampleConsumedRow :
    YMWeightedBTAdjointKappaRow
  metricRatioFormulaRecordedRow :
    YMWeightedBTAdjointKappaRow
  p2KappaFiniteSampleImportedRow :
    YMWeightedBTAdjointKappaRow
  p3KappaFiniteSampleImportedRow :
    YMWeightedBTAdjointKappaRow
  p5KappaFiniteSampleImportedRow :
    YMWeightedBTAdjointKappaRow
  weightedAdjointCompatibilityStillOpenRow :
    YMWeightedBTAdjointKappaRow
  uniformKappaPositivityStillOpenRow :
    YMWeightedBTAdjointKappaRow
  selfAdjointHamiltonianQuotientStillOpenRow :
    YMWeightedBTAdjointKappaRow
  continuumTransferStillOpenRow :
    YMWeightedBTAdjointKappaRow
  clayAndTerminalHeldFalseRow :
    YMWeightedBTAdjointKappaRow

canonicalYMWeightedBTAdjointKappaRows :
  List YMWeightedBTAdjointKappaRow
canonicalYMWeightedBTAdjointKappaRows =
  finiteGaugeHodgeAdjointCompatibilityConsumedRow
  ∷ btFiniteMetricGaugeKappaBoundaryConsumedRow
  ∷ finiteMetricRatioDefectGapSampleConsumedRow
  ∷ metricRatioFormulaRecordedRow
  ∷ p2KappaFiniteSampleImportedRow
  ∷ p3KappaFiniteSampleImportedRow
  ∷ p5KappaFiniteSampleImportedRow
  ∷ weightedAdjointCompatibilityStillOpenRow
  ∷ uniformKappaPositivityStillOpenRow
  ∷ selfAdjointHamiltonianQuotientStillOpenRow
  ∷ continuumTransferStillOpenRow
  ∷ clayAndTerminalHeldFalseRow
  ∷ []

data YMWeightedBTAdjointKappaBlocker : Set where
  weightedAdjointCompatibilityNotProvedForBTCells :
    YMWeightedBTAdjointKappaBlocker
  importedFiniteKappaRowsDoNotProveUniformInfimum :
    YMWeightedBTAdjointKappaBlocker
  selfAdjointYMHamiltonianOnGaugeQuotientMissing :
    YMWeightedBTAdjointKappaBlocker
  reflectionPositivityAndOSTransferMissing :
    YMWeightedBTAdjointKappaBlocker
  continuumTransferFromDepthFamilyMissing :
    YMWeightedBTAdjointKappaBlocker
  clayYangMillsAuthorityTokenMissing :
    YMWeightedBTAdjointKappaBlocker

canonicalYMWeightedBTAdjointKappaBlockers :
  List YMWeightedBTAdjointKappaBlocker
canonicalYMWeightedBTAdjointKappaBlockers =
  weightedAdjointCompatibilityNotProvedForBTCells
  ∷ importedFiniteKappaRowsDoNotProveUniformInfimum
  ∷ selfAdjointYMHamiltonianOnGaugeQuotientMissing
  ∷ reflectionPositivityAndOSTransferMissing
  ∷ continuumTransferFromDepthFamilyMissing
  ∷ clayYangMillsAuthorityTokenMissing
  ∷ []

metricRatioFormulaRecorded : Bool
metricRatioFormulaRecorded =
  true

finiteKappaSamplesImported : Bool
finiteKappaSamplesImported =
  true

weightedGaugeHodgeAdjointCompatibilityProved : Bool
weightedGaugeHodgeAdjointCompatibilityProved =
  false

uniformInfimumKappaPositiveProved : Bool
uniformInfimumKappaPositiveProved =
  false

selfAdjointHamiltonianQuotientProved : Bool
selfAdjointHamiltonianQuotientProved =
  false

continuumTransferFromKappaFamilyProved : Bool
continuumTransferFromKappaFamilyProved =
  false

finiteMassGapDiagnosticPromoted : Bool
finiteMassGapDiagnosticPromoted =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

metricRatioFormulaRecordedIsTrue :
  metricRatioFormulaRecorded ≡ true
metricRatioFormulaRecordedIsTrue =
  refl

finiteKappaSamplesImportedIsTrue :
  finiteKappaSamplesImported ≡ true
finiteKappaSamplesImportedIsTrue =
  refl

weightedGaugeHodgeAdjointCompatibilityProvedIsFalse :
  weightedGaugeHodgeAdjointCompatibilityProved ≡ false
weightedGaugeHodgeAdjointCompatibilityProvedIsFalse =
  refl

uniformInfimumKappaPositiveProvedIsFalse :
  uniformInfimumKappaPositiveProved ≡ false
uniformInfimumKappaPositiveProvedIsFalse =
  refl

selfAdjointHamiltonianQuotientProvedIsFalse :
  selfAdjointHamiltonianQuotientProved ≡ false
selfAdjointHamiltonianQuotientProvedIsFalse =
  refl

continuumTransferFromKappaFamilyProvedIsFalse :
  continuumTransferFromKappaFamilyProved ≡ false
continuumTransferFromKappaFamilyProvedIsFalse =
  refl

finiteMassGapDiagnosticPromotedIsFalse :
  finiteMassGapDiagnosticPromoted ≡ false
finiteMassGapDiagnosticPromotedIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

record YMWeightedBTAdjointKappaCalculation : Setω where
  field
    status :
      WeightedBTAdjointKappaCalculationStatus

    consumedFiniteGaugeHodgeAdjointCompatibility :
      Adj.FiniteGaugeHodgeAdjointCompatibility

    consumedFiniteGaugeHodgeAdjointCompatibilityIsCanonical :
      consumedFiniteGaugeHodgeAdjointCompatibility
      ≡
      Adj.canonicalFiniteGaugeHodgeAdjointCompatibility

    consumedBTFiniteMetricGaugeCompatibilityKappaBoundary :
      Kappa.BTFiniteMetricGaugeCompatibilityKappaBoundary

    consumedBTFiniteMetricGaugeCompatibilityKappaBoundaryIsCanonical :
      consumedBTFiniteMetricGaugeCompatibilityKappaBoundary
      ≡
      Kappa.canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary

    consumedMetricRatioDefectGapFiniteReceipt :
      FiniteGap.YMBTMetricRatioDefectGapFiniteReceipt

    consumedMetricRatioDefectGapFiniteReceiptIsCanonical :
      consumedMetricRatioDefectGapFiniteReceipt
      ≡
      FiniteGap.canonicalYMBTMetricRatioDefectGapFiniteReceipt

    weightedMetricRatioFormula :
      String

    dimension :
      BTDimension

    dimensionIsFour :
      dimension ≡ btDimension4

    gaugePotentialDegree :
      FormDegree

    gaugePotentialDegreeIsOne :
      gaugePotentialDegree ≡ degree1GaugePotential

    finiteDepths :
      List BTAdjointDepth

    finiteDepthsAreCanonical :
      finiteDepths ≡ canonicalFiniteDepths

    metricRatioRows :
      List WeightedBTMetricRatioRow

    metricRatioRowsAreCanonical :
      metricRatioRows ≡ canonicalMetricRatioRows

    importedFiniteKappaRows :
      ImportedFiniteKappaSampleRows

    importedFiniteKappaRowsAreCanonical :
      importedFiniteKappaRows ≡ canonicalImportedFiniteKappaSampleRows

    importedP2KappaNumeratorIsOne :
      FiniteGap.numerator FiniteGap.p2KappaRatio ≡ 1

    importedP2KappaDenominatorIsFour :
      FiniteGap.denominator FiniteGap.p2KappaRatio ≡ 4

    importedP3KappaNumeratorIsFour :
      FiniteGap.numerator FiniteGap.p3KappaRatio ≡ 4

    importedP3KappaDenominatorIsNine :
      FiniteGap.denominator FiniteGap.p3KappaRatio ≡ 9

    importedP5KappaNumeratorIsSixteen :
      FiniteGap.numerator FiniteGap.p5KappaRatio ≡ 16

    importedP5KappaDenominatorIsTwentyFive :
      FiniteGap.denominator FiniteGap.p5KappaRatio ≡ 25

    p2DepthIndependenceImported :
      FiniteGap.kappaAtDepth FiniteGap.p2 FiniteGap.depthZero
      ≡
      FiniteGap.kappaAtDepth FiniteGap.p2 FiniteGap.depthOne

    p3DepthIndependenceImported :
      FiniteGap.kappaAtDepth FiniteGap.p3 FiniteGap.depthZero
      ≡
      FiniteGap.kappaAtDepth FiniteGap.p3 FiniteGap.depthOne

    p5DepthIndependenceImported :
      FiniteGap.kappaAtDepth FiniteGap.p5 FiniteGap.depthZero
      ≡
      FiniteGap.kappaAtDepth FiniteGap.p5 FiniteGap.depthOne

    upstreamAdjointCompatibilityStillFalse :
      Adj.compatibilityDefectZeroProved
        consumedFiniteGaugeHodgeAdjointCompatibility
      ≡
      false

    upstreamMetricWeightedAdjointnessStillFalse :
      Adj.metricWeightedAdjointnessPromoted
        consumedFiniteGaugeHodgeAdjointCompatibility
      ≡
      false

    upstreamUniformKappaStillFalse :
      Kappa.uniformInfimumKappaPositive
        consumedBTFiniteMetricGaugeCompatibilityKappaBoundary
      ≡
      false

    upstreamContinuumTransferStillFalse :
      Kappa.continuumTransferFromKappaFamily
        consumedBTFiniteMetricGaugeCompatibilityKappaBoundary
      ≡
      false

    upstreamClayYMStillFalse :
      Kappa.clayYangMillsPromotedField
        consumedBTFiniteMetricGaugeCompatibilityKappaBoundary
      ≡
      false

    importedFiniteSampleNotContinuumPromotion :
      FiniteGap.continuumMassGapPromotedFlag
        consumedMetricRatioDefectGapFiniteReceipt
      ≡
      false

    rows :
      List YMWeightedBTAdjointKappaRow

    rowsAreCanonical :
      rows ≡ canonicalYMWeightedBTAdjointKappaRows

    rowCount :
      Nat

    rowCountIs12 :
      rowCount ≡ 12

    blockers :
      List YMWeightedBTAdjointKappaBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMWeightedBTAdjointKappaBlockers

    blockerCount :
      Nat

    blockerCountIs6 :
      blockerCount ≡ 6

    metricRatioFormulaRecordedFlag :
      Bool

    metricRatioFormulaRecordedFlagIsTrue :
      metricRatioFormulaRecordedFlag ≡ true

    finiteKappaSamplesImportedFlag :
      Bool

    finiteKappaSamplesImportedFlagIsTrue :
      finiteKappaSamplesImportedFlag ≡ true

    weightedGaugeHodgeAdjointCompatibilityProvedFlag :
      Bool

    weightedGaugeHodgeAdjointCompatibilityProvedFlagIsFalse :
      weightedGaugeHodgeAdjointCompatibilityProvedFlag ≡ false

    uniformInfimumKappaPositiveProvedFlag :
      Bool

    uniformInfimumKappaPositiveProvedFlagIsFalse :
      uniformInfimumKappaPositiveProvedFlag ≡ false

    selfAdjointHamiltonianQuotientProvedFlag :
      Bool

    selfAdjointHamiltonianQuotientProvedFlagIsFalse :
      selfAdjointHamiltonianQuotientProvedFlag ≡ false

    continuumTransferFromKappaFamilyProvedFlag :
      Bool

    continuumTransferFromKappaFamilyProvedFlagIsFalse :
      continuumTransferFromKappaFamilyProvedFlag ≡ false

    finiteMassGapDiagnosticPromotedFlag :
      Bool

    finiteMassGapDiagnosticPromotedFlagIsFalse :
      finiteMassGapDiagnosticPromotedFlag ≡ false

    clayYangMillsPromotedFlag :
      Bool

    clayYangMillsPromotedFlagIsFalse :
      clayYangMillsPromotedFlag ≡ false

    terminalPromotionFlag :
      Bool

    terminalPromotionFlagIsFalse :
      terminalPromotionFlag ≡ false

    boundary :
      List String

open YMWeightedBTAdjointKappaCalculation public

canonicalYMWeightedBTAdjointKappaCalculation :
  YMWeightedBTAdjointKappaCalculation
canonicalYMWeightedBTAdjointKappaCalculation =
  record
    { status =
        weightedBTAdjointKappaFiniteCalculationRecordedPromotionBlocked
    ; consumedFiniteGaugeHodgeAdjointCompatibility =
        Adj.canonicalFiniteGaugeHodgeAdjointCompatibility
    ; consumedFiniteGaugeHodgeAdjointCompatibilityIsCanonical =
        refl
    ; consumedBTFiniteMetricGaugeCompatibilityKappaBoundary =
        Kappa.canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
    ; consumedBTFiniteMetricGaugeCompatibilityKappaBoundaryIsCanonical =
        refl
    ; consumedMetricRatioDefectGapFiniteReceipt =
        FiniteGap.canonicalYMBTMetricRatioDefectGapFiniteReceipt
    ; consumedMetricRatioDefectGapFiniteReceiptIsCanonical =
        refl
    ; weightedMetricRatioFormula =
        "w(sigma^k_d)/wDual(sigma^(n-k)_d) = p^((n-2k)*d); for n=4,k=1 this is p^(2d)"
    ; dimension =
        btDimension4
    ; dimensionIsFour =
        refl
    ; gaugePotentialDegree =
        degree1GaugePotential
    ; gaugePotentialDegreeIsOne =
        refl
    ; finiteDepths =
        canonicalFiniteDepths
    ; finiteDepthsAreCanonical =
        refl
    ; metricRatioRows =
        canonicalMetricRatioRows
    ; metricRatioRowsAreCanonical =
        refl
    ; importedFiniteKappaRows =
        canonicalImportedFiniteKappaSampleRows
    ; importedFiniteKappaRowsAreCanonical =
        refl
    ; importedP2KappaNumeratorIsOne =
        FiniteGap.p2KappaNumeratorIsOne
    ; importedP2KappaDenominatorIsFour =
        FiniteGap.p2KappaDenominatorIsFour
    ; importedP3KappaNumeratorIsFour =
        FiniteGap.p3KappaNumeratorIsFour
    ; importedP3KappaDenominatorIsNine =
        FiniteGap.p3KappaDenominatorIsNine
    ; importedP5KappaNumeratorIsSixteen =
        FiniteGap.p5KappaNumeratorIsSixteen
    ; importedP5KappaDenominatorIsTwentyFive =
        FiniteGap.p5KappaDenominatorIsTwentyFive
    ; p2DepthIndependenceImported =
        FiniteGap.p2DepthIndependent
    ; p3DepthIndependenceImported =
        FiniteGap.p3DepthIndependent
    ; p5DepthIndependenceImported =
        FiniteGap.p5DepthIndependent
    ; upstreamAdjointCompatibilityStillFalse =
        Adj.FiniteGaugeHodgeAdjointCompatibility.compatibilityDefectZeroProvedIsFalse
          Adj.canonicalFiniteGaugeHodgeAdjointCompatibility
    ; upstreamMetricWeightedAdjointnessStillFalse =
        Adj.FiniteGaugeHodgeAdjointCompatibility.metricWeightedAdjointnessPromotedIsFalse
          Adj.canonicalFiniteGaugeHodgeAdjointCompatibility
    ; upstreamUniformKappaStillFalse =
        Kappa.BTFiniteMetricGaugeCompatibilityKappaBoundary.uniformInfimumKappaPositiveIsFalse
          Kappa.canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
    ; upstreamContinuumTransferStillFalse =
        Kappa.BTFiniteMetricGaugeCompatibilityKappaBoundary.continuumTransferFromKappaFamilyIsFalse
          Kappa.canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
    ; upstreamClayYMStillFalse =
        Kappa.BTFiniteMetricGaugeCompatibilityKappaBoundary.clayYangMillsPromotedFieldIsFalse
          Kappa.canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
    ; importedFiniteSampleNotContinuumPromotion =
        FiniteGap.continuumMassGapPromotedFlagIsFalse
          FiniteGap.canonicalYMBTMetricRatioDefectGapFiniteReceipt
    ; rows =
        canonicalYMWeightedBTAdjointKappaRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        12
    ; rowCountIs12 =
        refl
    ; blockers =
        canonicalYMWeightedBTAdjointKappaBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        6
    ; blockerCountIs6 =
        refl
    ; metricRatioFormulaRecordedFlag =
        metricRatioFormulaRecorded
    ; metricRatioFormulaRecordedFlagIsTrue =
        refl
    ; finiteKappaSamplesImportedFlag =
        finiteKappaSamplesImported
    ; finiteKappaSamplesImportedFlagIsTrue =
        refl
    ; weightedGaugeHodgeAdjointCompatibilityProvedFlag =
        weightedGaugeHodgeAdjointCompatibilityProved
    ; weightedGaugeHodgeAdjointCompatibilityProvedFlagIsFalse =
        refl
    ; uniformInfimumKappaPositiveProvedFlag =
        uniformInfimumKappaPositiveProved
    ; uniformInfimumKappaPositiveProvedFlagIsFalse =
        refl
    ; selfAdjointHamiltonianQuotientProvedFlag =
        selfAdjointHamiltonianQuotientProved
    ; selfAdjointHamiltonianQuotientProvedFlagIsFalse =
        refl
    ; continuumTransferFromKappaFamilyProvedFlag =
        continuumTransferFromKappaFamilyProved
    ; continuumTransferFromKappaFamilyProvedFlagIsFalse =
        refl
    ; finiteMassGapDiagnosticPromotedFlag =
        finiteMassGapDiagnosticPromoted
    ; finiteMassGapDiagnosticPromotedFlagIsFalse =
        refl
    ; clayYangMillsPromotedFlag =
        clayYangMillsPromoted
    ; clayYangMillsPromotedFlagIsFalse =
        refl
    ; terminalPromotionFlag =
        terminalPromotion
    ; terminalPromotionFlagIsFalse =
        refl
    ; boundary =
        "Consumes FiniteGaugeHodgeAdjointCompatibility, BTFiniteMetricGaugeCompatibilityKappaBoundary, and YMBTMetricRatioDefectGapFinite"
        ∷ "Records weighted BT primal/dual metric ratio target w/wDual = p^((n-2k)*d)"
        ∷ "Checks n=4,k=1 sample ratios for p=2 at depths 0,1,2 and imports p=2,3,5 finite kappa rows"
        ∷ "Records kappa_p=(p-1)^2/p^2 samples: p=2 -> 1/4, p=3 -> 4/9, p=5 -> 16/25"
        ∷ "Finite sample depth independence is imported, but uniform infimum over depth is not proved here"
        ∷ "Weighted adjoint compatibility, self-adjoint Hamiltonian quotient, reflection positivity, continuum transfer, Clay YM, and terminal promotion remain false"
        ∷ []
    }

canonicalYMWeightedBTAdjointKappaRowCountIs12 :
  rowCount canonicalYMWeightedBTAdjointKappaCalculation ≡ 12
canonicalYMWeightedBTAdjointKappaRowCountIs12 =
  refl

canonicalYMWeightedBTAdjointKappaBlockerCountIs6 :
  blockerCount canonicalYMWeightedBTAdjointKappaCalculation ≡ 6
canonicalYMWeightedBTAdjointKappaBlockerCountIs6 =
  refl

canonicalYMWeightedBTAdjointKappaUniformInfimumFalse :
  uniformInfimumKappaPositiveProvedFlag
    canonicalYMWeightedBTAdjointKappaCalculation
  ≡
  false
canonicalYMWeightedBTAdjointKappaUniformInfimumFalse =
  refl

canonicalYMWeightedBTAdjointKappaContinuumTransferFalse :
  continuumTransferFromKappaFamilyProvedFlag
    canonicalYMWeightedBTAdjointKappaCalculation
  ≡
  false
canonicalYMWeightedBTAdjointKappaContinuumTransferFalse =
  refl

canonicalYMWeightedBTAdjointKappaClayYMFalse :
  clayYangMillsPromotedFlag canonicalYMWeightedBTAdjointKappaCalculation
  ≡
  false
canonicalYMWeightedBTAdjointKappaClayYMFalse =
  refl

canonicalYMWeightedBTAdjointKappaTerminalFalse :
  terminalPromotionFlag canonicalYMWeightedBTAdjointKappaCalculation
  ≡
  false
canonicalYMWeightedBTAdjointKappaTerminalFalse =
  refl
