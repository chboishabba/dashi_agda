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

metricRatioExponentN4K1 : Nat → Nat
metricRatioExponentN4K1 d =
  metricRatioExponent 4 1 d

metricRatioPowerN4K1 : Nat → Nat → Nat
metricRatioPowerN4K1 p d =
  metricRatioPower p 4 1 d

metricRatioExponentN4K1Is2D :
  (d : Nat) → metricRatioExponentN4K1 d ≡ 2 * d
metricRatioExponentN4K1Is2D d =
  refl

metricRatioPowerN4K1IsP2D :
  (p d : Nat) → metricRatioPowerN4K1 p d ≡ pow p (2 * d)
metricRatioPowerN4K1IsP2D p d =
  refl

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

canonicalP3N4K1D1RatioTarget :
  WeightedBTMetricRatioTarget
canonicalP3N4K1D1RatioTarget =
  weightedBTMetricRatioTarget
    3
    4
    1
    1
    (metricRatioPower 3 4 1 1)
    refl

canonicalP5N4K1D1RatioTarget :
  WeightedBTMetricRatioTarget
canonicalP5N4K1D1RatioTarget =
  weightedBTMetricRatioTarget
    5
    4
    1
    1
    (metricRatioPower 5 4 1 1)
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

data WeightedBTMetricRatioFormulaRow : Set where
  generalWWDualEqualsPToNMinus2KDepthRow :
    WeightedBTMetricRatioFormulaRow
  gaugePotentialN4K1SpecializesToPTo2DepthRow :
    WeightedBTMetricRatioFormulaRow
  p2N4K1Depth1RatioEqualsFourRow :
    WeightedBTMetricRatioFormulaRow
  p3N4K1Depth1RatioEqualsNineRow :
    WeightedBTMetricRatioFormulaRow
  p5N4K1Depth1RatioEqualsTwentyFiveRow :
    WeightedBTMetricRatioFormulaRow

canonicalWeightedBTMetricRatioFormulaRows :
  List WeightedBTMetricRatioFormulaRow
canonicalWeightedBTMetricRatioFormulaRows =
  generalWWDualEqualsPToNMinus2KDepthRow
  ∷ gaugePotentialN4K1SpecializesToPTo2DepthRow
  ∷ p2N4K1Depth1RatioEqualsFourRow
  ∷ p3N4K1Depth1RatioEqualsNineRow
  ∷ p5N4K1Depth1RatioEqualsTwentyFiveRow
  ∷ []

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
  ∷ weightedBTMetricRatioRow
    btDimension4
    degree1GaugePotential
    depth1
    FiniteGap.p3
    canonicalP3N4K1D1RatioTarget
  ∷ weightedBTMetricRatioRow
    btDimension4
    degree1GaugePotential
    depth1
    FiniteGap.p5
    canonicalP5N4K1D1RatioTarget
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

record UniformInfimumKappaTargetBoundary : Set where
  constructor mkUniformInfimumKappaTargetBoundary
  field
    targetFormula :
      String
    symbolicRatioRows :
      List WeightedBTMetricRatioFormulaRow
    symbolicRatioRowsAreCanonical :
      symbolicRatioRows ≡ canonicalWeightedBTMetricRatioFormulaRows
    symbolicRatioRowCount :
      Nat
    symbolicRatioRowCountIs5 :
      symbolicRatioRowCount ≡ 5
    metricRatioRows :
      List WeightedBTMetricRatioRow
    metricRatioRowsAreCanonical :
      metricRatioRows ≡ canonicalMetricRatioRows
    metricRatioRowCount :
      Nat
    metricRatioRowCountIs5 :
      metricRatioRowCount ≡ 5
    finiteKappaSupportRows :
      ImportedFiniteKappaSampleRows
    finiteKappaSupportRowsAreCanonical :
      finiteKappaSupportRows ≡ canonicalImportedFiniteKappaSampleRows
    finiteSamplesSupportUniformInfimumTarget :
      Bool
    finiteSamplesSupportUniformInfimumTargetIsTrue :
      finiteSamplesSupportUniformInfimumTarget ≡ true
    uniformInfimumKappaPositivePromoted :
      Bool
    uniformInfimumKappaPositivePromotedIsFalse :
      uniformInfimumKappaPositivePromoted ≡ false
    clayYangMillsPromotedByTarget :
      Bool
    clayYangMillsPromotedByTargetIsFalse :
      clayYangMillsPromotedByTarget ≡ false

open UniformInfimumKappaTargetBoundary public

canonicalUniformInfimumKappaTargetBoundary :
  UniformInfimumKappaTargetBoundary
canonicalUniformInfimumKappaTargetBoundary =
  mkUniformInfimumKappaTargetBoundary
    "Target: infer inf_d kappa_d > 0 from weighted BT adjoint compatibility plus finite p=2,3,5 support; not promoted here"
    canonicalWeightedBTMetricRatioFormulaRows
    refl
    5
    refl
    canonicalMetricRatioRows
    refl
    5
    refl
    canonicalImportedFiniteKappaSampleRows
    refl
    true
    refl
    false
    refl
    false
    refl

data WeightedBTKappaFiniteSupport : Set where
  p2Depth0RatioOneSupport :
    WeightedBTKappaFiniteSupport

  p2Depth1RatioFourSupport :
    WeightedBTKappaFiniteSupport

  p2Depth2RatioSixteenSupport :
    WeightedBTKappaFiniteSupport

  p3Depth1RatioNineSupport :
    WeightedBTKappaFiniteSupport

  p5Depth1RatioTwentyFiveSupport :
    WeightedBTKappaFiniteSupport

  p2KappaOneOverFourSupport :
    WeightedBTKappaFiniteSupport

  p3KappaFourOverNineSupport :
    WeightedBTKappaFiniteSupport

  p5KappaSixteenOverTwentyFiveSupport :
    WeightedBTKappaFiniteSupport

canonicalWeightedBTKappaFiniteSupport :
  List WeightedBTKappaFiniteSupport
canonicalWeightedBTKappaFiniteSupport =
  p2Depth0RatioOneSupport
  ∷ p2Depth1RatioFourSupport
  ∷ p2Depth2RatioSixteenSupport
  ∷ p3Depth1RatioNineSupport
  ∷ p5Depth1RatioTwentyFiveSupport
  ∷ p2KappaOneOverFourSupport
  ∷ p3KappaFourOverNineSupport
  ∷ p5KappaSixteenOverTwentyFiveSupport
  ∷ []

data WeightedBTKappaFailClosedGate : Set where
  finitePrimeSampleOnlyGate :
    WeightedBTKappaFailClosedGate

  weightedAdjointCompatibilityGate :
    WeightedBTKappaFailClosedGate

  uniformInfimumOverAllDepthsGate :
    WeightedBTKappaFailClosedGate

  gaugeQuotientHamiltonianGate :
    WeightedBTKappaFailClosedGate

  continuumOSTransferGate :
    WeightedBTKappaFailClosedGate

  clayAuthorityGate :
    WeightedBTKappaFailClosedGate

canonicalWeightedBTKappaFailClosedGates :
  List WeightedBTKappaFailClosedGate
canonicalWeightedBTKappaFailClosedGates =
  finitePrimeSampleOnlyGate
  ∷ weightedAdjointCompatibilityGate
  ∷ uniformInfimumOverAllDepthsGate
  ∷ gaugeQuotientHamiltonianGate
  ∷ continuumOSTransferGate
  ∷ clayAuthorityGate
  ∷ []

record WeightedBTKappaFiniteCalculationLedger : Set where
  constructor mkWeightedBTKappaFiniteCalculationLedger
  field
    finiteSupportRows :
      List WeightedBTKappaFiniteSupport
    finiteSupportRowsAreCanonical :
      finiteSupportRows ≡ canonicalWeightedBTKappaFiniteSupport
    finiteSupportRowCount :
      Nat
    finiteSupportRowCountIs8 :
      finiteSupportRowCount ≡ 8
    failClosedGates :
      List WeightedBTKappaFailClosedGate
    failClosedGatesAreCanonical :
      failClosedGates ≡ canonicalWeightedBTKappaFailClosedGates
    failClosedGateCount :
      Nat
    failClosedGateCountIs6 :
      failClosedGateCount ≡ 6
    p2Depth0RatioOne :
      metricRatioPower 2 4 1 0 ≡ 1
    p2Depth1RatioFour :
      metricRatioPower 2 4 1 1 ≡ 4
    p2Depth2RatioSixteen :
      metricRatioPower 2 4 1 2 ≡ 16
    p3Depth1RatioNine :
      metricRatioPower 3 4 1 1 ≡ 9
    p5Depth1RatioTwentyFive :
      metricRatioPower 5 4 1 1 ≡ 25
    finiteSamplesRecorded :
      Bool
    finiteSamplesRecordedIsTrue :
      finiteSamplesRecorded ≡ true
    weightedAdjointClosedByLedger :
      Bool
    weightedAdjointClosedByLedgerIsFalse :
      weightedAdjointClosedByLedger ≡ false
    uniformInfimumClosedByLedger :
      Bool
    uniformInfimumClosedByLedgerIsFalse :
      uniformInfimumClosedByLedger ≡ false
    continuumTransferClosedByLedger :
      Bool
    continuumTransferClosedByLedgerIsFalse :
      continuumTransferClosedByLedger ≡ false
    clayPromotedByLedger :
      Bool
    clayPromotedByLedgerIsFalse :
      clayPromotedByLedger ≡ false

open WeightedBTKappaFiniteCalculationLedger public

canonicalWeightedBTKappaFiniteCalculationLedger :
  WeightedBTKappaFiniteCalculationLedger
canonicalWeightedBTKappaFiniteCalculationLedger =
  mkWeightedBTKappaFiniteCalculationLedger
    canonicalWeightedBTKappaFiniteSupport
    refl
    8
    refl
    canonicalWeightedBTKappaFailClosedGates
    refl
    6
    refl
    refl
    refl
    refl
    refl
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
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
  symbolicMetricRatioRowsRecordedRow :
    YMWeightedBTAdjointKappaRow
  n4K1SpecializationRecordedRow :
    YMWeightedBTAdjointKappaRow
  p2KappaFiniteSampleImportedRow :
    YMWeightedBTAdjointKappaRow
  p3KappaFiniteSampleImportedRow :
    YMWeightedBTAdjointKappaRow
  p5KappaFiniteSampleImportedRow :
    YMWeightedBTAdjointKappaRow
  finiteSupportLedgerRecordedRow :
    YMWeightedBTAdjointKappaRow
  failClosedGateLedgerRecordedRow :
    YMWeightedBTAdjointKappaRow
  uniformInfimumTargetBoundaryRecordedRow :
    YMWeightedBTAdjointKappaRow
  importedFiniteSamplesDoNotCloseUniformInfimumRow :
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
  ∷ symbolicMetricRatioRowsRecordedRow
  ∷ n4K1SpecializationRecordedRow
  ∷ p2KappaFiniteSampleImportedRow
  ∷ p3KappaFiniteSampleImportedRow
  ∷ p5KappaFiniteSampleImportedRow
  ∷ finiteSupportLedgerRecordedRow
  ∷ failClosedGateLedgerRecordedRow
  ∷ uniformInfimumTargetBoundaryRecordedRow
  ∷ importedFiniteSamplesDoNotCloseUniformInfimumRow
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

    consumedBTFiniteMetricGaugeCompatibilityKappaBoundaryCanonicalGuard :
      Bool

    consumedBTFiniteMetricGaugeCompatibilityKappaBoundaryCanonicalGuardIsTrue :
      consumedBTFiniteMetricGaugeCompatibilityKappaBoundaryCanonicalGuard
      ≡
      true

    consumedMetricRatioDefectGapFiniteReceipt :
      FiniteGap.YMBTMetricRatioDefectGapFiniteReceipt

    consumedMetricRatioDefectGapFiniteReceiptIsCanonical :
      consumedMetricRatioDefectGapFiniteReceipt
      ≡
      FiniteGap.canonicalYMBTMetricRatioDefectGapFiniteReceipt

    weightedMetricRatioFormula :
      String

    symbolicMetricRatioFormulaRows :
      List WeightedBTMetricRatioFormulaRow

    symbolicMetricRatioFormulaRowsAreCanonical :
      symbolicMetricRatioFormulaRows ≡ canonicalWeightedBTMetricRatioFormulaRows

    symbolicMetricRatioFormulaRowCount :
      Nat

    symbolicMetricRatioFormulaRowCountIs5 :
      symbolicMetricRatioFormulaRowCount ≡ 5

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

    metricRatioRowCount :
      Nat

    metricRatioRowCountIs5 :
      metricRatioRowCount ≡ 5

    p3N4K1D1RatioSupport :
      metricRatioPower 3 4 1 1 ≡ 9

    p5N4K1D1RatioSupport :
      metricRatioPower 5 4 1 1 ≡ 25

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
      FiniteGap.YMBTMetricRatioDefectGapFiniteReceipt.continuumMassGapPromotedFlag
        consumedMetricRatioDefectGapFiniteReceipt
      ≡
      false

    finiteCalculationLedger :
      WeightedBTKappaFiniteCalculationLedger

    finiteCalculationLedgerIsCanonical :
      finiteCalculationLedger ≡ canonicalWeightedBTKappaFiniteCalculationLedger

    finiteCalculationLedgerSupportCount :
      finiteSupportRowCount finiteCalculationLedger ≡ 8

    finiteCalculationLedgerGateCount :
      failClosedGateCount finiteCalculationLedger ≡ 6

    finiteCalculationLedgerAdjointFalse :
      weightedAdjointClosedByLedger finiteCalculationLedger ≡ false

    finiteCalculationLedgerUniformInfimumFalse :
      uniformInfimumClosedByLedger finiteCalculationLedger ≡ false

    finiteCalculationLedgerContinuumFalse :
      continuumTransferClosedByLedger finiteCalculationLedger ≡ false

    finiteCalculationLedgerClayFalse :
      clayPromotedByLedger finiteCalculationLedger ≡ false

    uniformInfimumTargetBoundary :
      UniformInfimumKappaTargetBoundary

    uniformInfimumTargetBoundaryIsCanonical :
      uniformInfimumTargetBoundary ≡ canonicalUniformInfimumKappaTargetBoundary

    uniformInfimumTargetFiniteSupportFlag :
      finiteSamplesSupportUniformInfimumTarget uniformInfimumTargetBoundary
      ≡
      true

    uniformInfimumTargetStillFalse :
      uniformInfimumKappaPositivePromoted uniformInfimumTargetBoundary
      ≡
      false

    uniformInfimumTargetClayYMStillFalse :
      clayYangMillsPromotedByTarget uniformInfimumTargetBoundary
      ≡
      false

    rows :
      List YMWeightedBTAdjointKappaRow

    rowsAreCanonical :
      rows ≡ canonicalYMWeightedBTAdjointKappaRows

    rowCount :
      Nat

    rowCountIs18 :
      rowCount ≡ 18

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
    ; consumedBTFiniteMetricGaugeCompatibilityKappaBoundaryCanonicalGuard =
        true
    ; consumedBTFiniteMetricGaugeCompatibilityKappaBoundaryCanonicalGuardIsTrue =
        refl
    ; consumedMetricRatioDefectGapFiniteReceipt =
        FiniteGap.canonicalYMBTMetricRatioDefectGapFiniteReceipt
    ; consumedMetricRatioDefectGapFiniteReceiptIsCanonical =
        refl
    ; weightedMetricRatioFormula =
        "w(sigma^k_d)/wDual(sigma^(n-k)_d) = p^((n-2k)*d); for n=4,k=1 this is p^(2d)"
    ; symbolicMetricRatioFormulaRows =
        canonicalWeightedBTMetricRatioFormulaRows
    ; symbolicMetricRatioFormulaRowsAreCanonical =
        refl
    ; symbolicMetricRatioFormulaRowCount =
        5
    ; symbolicMetricRatioFormulaRowCountIs5 =
        refl
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
    ; metricRatioRowCount =
        5
    ; metricRatioRowCountIs5 =
        refl
    ; p3N4K1D1RatioSupport =
        refl
    ; p5N4K1D1RatioSupport =
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
        FiniteGap.YMBTMetricRatioDefectGapFiniteReceipt.continuumMassGapPromotedFlagIsFalse
          FiniteGap.canonicalYMBTMetricRatioDefectGapFiniteReceipt
    ; finiteCalculationLedger =
        canonicalWeightedBTKappaFiniteCalculationLedger
    ; finiteCalculationLedgerIsCanonical =
        refl
    ; finiteCalculationLedgerSupportCount =
        refl
    ; finiteCalculationLedgerGateCount =
        refl
    ; finiteCalculationLedgerAdjointFalse =
        refl
    ; finiteCalculationLedgerUniformInfimumFalse =
        refl
    ; finiteCalculationLedgerContinuumFalse =
        refl
    ; finiteCalculationLedgerClayFalse =
        refl
    ; uniformInfimumTargetBoundary =
        canonicalUniformInfimumKappaTargetBoundary
    ; uniformInfimumTargetBoundaryIsCanonical =
        refl
    ; uniformInfimumTargetFiniteSupportFlag =
        refl
    ; uniformInfimumTargetStillFalse =
        refl
    ; uniformInfimumTargetClayYMStillFalse =
        refl
    ; rows =
        canonicalYMWeightedBTAdjointKappaRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        18
    ; rowCountIs18 =
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
        ∷ "Checks n=4,k=1 sample ratios for p=2 at depths 0,1,2 and for p=3,5 at depth 1"
        ∷ "Records kappa_p=(p-1)^2/p^2 samples: p=2 -> 1/4, p=3 -> 4/9, p=5 -> 16/25"
        ∷ "Finite calculation ledger records eight support rows and six fail-closed gates; the ledger itself keeps weighted adjoint, uniform infimum, continuum transfer, and Clay promotion false"
        ∷ "Records a uniform-infimum target boundary with finite samples/support, but uniform infimum over depth is not proved here"
        ∷ "Weighted adjoint compatibility, self-adjoint Hamiltonian quotient, reflection positivity, continuum transfer, Clay YM, and terminal promotion remain false"
        ∷ []
    }

canonicalYMWeightedBTAdjointKappaRowCountIs18 :
  rowCount canonicalYMWeightedBTAdjointKappaCalculation ≡ 18
canonicalYMWeightedBTAdjointKappaRowCountIs18 =
  refl

canonicalWeightedBTKappaFiniteSupportCountIs8 :
  listCount canonicalWeightedBTKappaFiniteSupport ≡ 8
canonicalWeightedBTKappaFiniteSupportCountIs8 =
  refl

canonicalWeightedBTKappaFailClosedGateCountIs6 :
  listCount canonicalWeightedBTKappaFailClosedGates ≡ 6
canonicalWeightedBTKappaFailClosedGateCountIs6 =
  refl

canonicalYMWeightedBTAdjointKappaLedgerUniformInfimumFalse :
  uniformInfimumClosedByLedger
    (finiteCalculationLedger canonicalYMWeightedBTAdjointKappaCalculation)
  ≡
  false
canonicalYMWeightedBTAdjointKappaLedgerUniformInfimumFalse =
  refl

canonicalYMWeightedBTAdjointKappaLedgerContinuumFalse :
  continuumTransferClosedByLedger
    (finiteCalculationLedger canonicalYMWeightedBTAdjointKappaCalculation)
  ≡
  false
canonicalYMWeightedBTAdjointKappaLedgerContinuumFalse =
  refl

canonicalYMWeightedBTAdjointKappaLedgerClayFalse :
  clayPromotedByLedger
    (finiteCalculationLedger canonicalYMWeightedBTAdjointKappaCalculation)
  ≡
  false
canonicalYMWeightedBTAdjointKappaLedgerClayFalse =
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
