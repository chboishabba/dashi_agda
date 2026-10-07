module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralCompanion20261007Exact where

------------------------------------------------------------------------
-- POSITIVE B4 / LITERAL CORE COMPANION + NON-VACUOUS STRICT SPLIT
--
-- The old strict certificates carried `coreCompanionMass` as a free scalar.
-- A condition theta < 1 is not physically meaningful unless that scalar is
-- itself tied to one fixed observable on the SAME physical state/output.
--
-- Use the already-proved same-pair coherent Young envelope, but ONLY on the
-- literal Core-Core rows selected by the B4 principal carrier:
--
--   M_core := sum_(Core-Core rows a,b)
--       |S_a-S_b| * 2 * ( ||M||^2 + ||A_a-A_b||^2 ).
--
-- Every principal row satisfies its coefficient-one Young bound, hence
--
--   P_Core-Core <= M_core.
--
-- Thus the remaining principal theorem is genuinely a STRICT improvement
--
--   P_Core-Core <= theta_P M_core + c_P ED,    theta_P < 1,
--
-- against a fixed literal companion, rather than against a producer-chosen
-- scalar.  The defect estimate remains on the literal Core-noncore rows.
--
-- This owner introduces no new estimate beyond the existing pairwise Young
-- theorem.  It fixes the semantic target and compiles a physically meaningful
-- strict split into the existing generic B4 compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _<_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceQuantitativePairBoundExact as Quant
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Rows
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalDefectRows20261007Exact as SplitRows
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingStrictSplitMaxCutExact as Strict

F : C3.RealField _
F = Rational.rationalRealField

rowCompanion :
  C3.Complex3 F →
  (Physical.PhysicalTriadIncidence → ℚ) →
  (Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Rows.LiteralPairRow → ℚ
rowCompanion mixed rate value row =
  Quant.rateWeightedYoungPair
    mixed rate value (Rows.alpha row) (Rows.beta row)

companionSum :
  C3.Complex3 F →
  (Physical.PhysicalTriadIncidence → ℚ) →
  (Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Rows.LiteralPairRow → ℚ
companionSum mixed rate value [] = 0ℚ
companionSum mixed rate value (row ∷ rest) =
  rowCompanion mixed rate value row + companionSum mixed rate value rest

negativeCoherentPairTermBelowYoung :
  (mixed : C3.Complex3 F) →
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  0ℚ -
    ((rate alpha - rate beta)
      * (Pair.cellWork mixed value alpha - Pair.cellWork mixed value beta))
  ≤ Quant.rateWeightedYoungPair mixed rate value alpha beta
negativeCoherentPairTermBelowYoung mixed rate value alpha beta =
  let
    rateDifference = rate alpha - rate beta
    workDifference =
      Pair.cellWork mixed value alpha - Pair.cellWork mixed value beta
    product = rateDifference * workDifference

    raw : 0ℚ - product ≤ ∣ 0ℚ - product ∣
    raw = ℚP.p≤∣p∣ (0ℚ - product)

    negMeaning : 0ℚ - product ≡ - product
    negMeaning = solve (product ∷ [])

    absNeg : ∣ 0ℚ - product ∣ ≡ ∣ product ∣
    absNeg =
      trans
        (cong ∣_∣ negMeaning)
        (ℚP.∣-p∣≡∣p∣ product)

    absProduct :
      ∣ product ∣ ≡ ∣ rateDifference ∣ * ∣ workDifference ∣
    absProduct = ℚP.∣p*q∣≡∣p∣*∣q∣ rateDifference workDifference

    toAbsolute :
      0ℚ - product ≤ ∣ rateDifference ∣ * ∣ workDifference ∣
    toAbsolute =
      subst
        (λ upper → 0ℚ - product ≤ upper)
        (trans absNeg absProduct)
        raw
  in
  ℚP.≤-trans
    toAbsolute
    (Quant.absoluteCoherentPairBelowYoung mixed rate value alpha beta)

rowSignedBelowCompanion :
  (mixed : C3.Complex3 F) →
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (row : Rows.LiteralPairRow) →
  Rows.rowSignedValue rate (Pair.cellWork mixed value) row
  ≤ rowCompanion mixed rate value row
rowSignedBelowCompanion mixed rate value row =
  negativeCoherentPairTermBelowYoung
    mixed rate value (Rows.alpha row) (Rows.beta row)

rowSumBelowCompanion :
  (mixed : C3.Complex3 F) →
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (rows : List Rows.LiteralPairRow) →
  Rows.sumRows rate (Pair.cellWork mixed value) rows
  ≤ companionSum mixed rate value rows
rowSumBelowCompanion mixed rate value [] = ℚP.≤-refl
rowSumBelowCompanion mixed rate value (row ∷ rest) =
  ℚP.+-mono-≤
    (rowSignedBelowCompanion mixed rate value row)
    (rowSumBelowCompanion mixed rate value rest)

module LiveLiteralCompanion
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output
  module R = SplitRows.LivePrincipalDefect physicalSystem S output
  module G = Strict.StrictSplit physicalSystem S output

  coreCompanionMass : ℚ
  coreCompanionMass =
    companionSum
      (Live.mixed output)
      Rate.inputMass
      Live.value
      R.principalLiteralRows

  principalBelowLiteralCompanion :
    R.principal ≤ coreCompanionMass
  principalBelowLiteralCompanion =
    rowSumBelowCompanion
      (Live.mixed output)
      Rate.inputMass
      Live.value
      R.principalLiteralRows

  record LiteralCompanionStrictSplitData : Set where
    constructor literal-companion-strict-split-data
    field
      localED : ℚ
      thetaPrincipal thetaDefect : ℚ
      principalEDCoefficient defectEDCoefficient : ℚ

      thetaPrincipalNN : 0ℚ ≤ thetaPrincipal
      thetaDefectNN : 0ℚ ≤ thetaDefect
      combinedThetaStrictlyBelowOne : thetaPrincipal + thetaDefect < 1ℚ

      principalStrictBound :
        R.principal
        ≤ thetaPrincipal * coreCompanionMass
          + principalEDCoefficient * localED

      defectBound :
        R.defect
        ≤ thetaDefect * coreCompanionMass
          + defectEDCoefficient * localED

  open LiteralCompanionStrictSplitData public

  toGenericStrictSplit :
    LiteralCompanionStrictSplitData → G.StrictSplitRowData
  toGenericStrictSplit D = record
    { G.principal = R.principal
    ; G.defect = R.defect
    ; G.coreCompanionMass = coreCompanionMass
    ; G.localED = localED D
    ; G.thetaPrincipal = thetaPrincipal D
    ; G.thetaDefect = thetaDefect D
    ; G.principalEDCoefficient = principalEDCoefficient D
    ; G.defectEDCoefficient = defectEDCoefficient D
    ; G.thetaPrincipalNN = thetaPrincipalNN D
    ; G.thetaDefectNN = thetaDefectNN D
    ; G.combinedThetaStrictlyBelowOne = combinedThetaStrictlyBelowOne D
    ; G.rowDecomposition = R.literalRowSumSplit
    ; G.principalBound = principalStrictBound D
    ; G.defectBound = defectBound D
    }

  buildsLiteralB4Certificate :
    (D : LiteralCompanionStrictSplitData) →
    G.O.LiteralRowStrictCriticalTouchingCertificate
  buildsLiteralB4Certificate D =
    G.strictSplitBuildsLiteralRowCertificate (toGenericStrictSplit D)

b4LiteralCoreCompanionMeaningClosed : Bool
b4LiteralCoreCompanionMeaningClosed = true

b4PrincipalBaselineYoungBoundClosed : Bool
b4PrincipalBaselineYoungBoundClosed = true

b4LiteralCompanionStrictSplitCompilerClosed : Bool
b4LiteralCompanionStrictSplitCompilerClosed = true

b4PrincipalStrictImprovementBelowOneClosed : Bool
b4PrincipalStrictImprovementBelowOneClosed = false

b4DefectPhysicalPaymentClosed : Bool
b4DefectPhysicalPaymentClosed = false

b4FreeCompanionScalarStillRequiredByPreferredRoute : Bool
b4FreeCompanionScalarStillRequiredByPreferredRoute = false

clayPromotion : Bool
clayPromotion = false

b4LiteralCoreCompanionMeaningClosedIsTrue :
  b4LiteralCoreCompanionMeaningClosed ≡ true
b4LiteralCoreCompanionMeaningClosedIsTrue = refl

b4PrincipalBaselineYoungBoundClosedIsTrue :
  b4PrincipalBaselineYoungBoundClosed ≡ true
b4PrincipalBaselineYoungBoundClosedIsTrue = refl

b4LiteralCompanionStrictSplitCompilerClosedIsTrue :
  b4LiteralCompanionStrictSplitCompilerClosed ≡ true
b4LiteralCompanionStrictSplitCompilerClosedIsTrue = refl

b4PrincipalStrictImprovementBelowOneClosedIsFalse :
  b4PrincipalStrictImprovementBelowOneClosed ≡ false
b4PrincipalStrictImprovementBelowOneClosedIsFalse = refl

b4DefectPhysicalPaymentClosedIsFalse :
  b4DefectPhysicalPaymentClosed ≡ false
b4DefectPhysicalPaymentClosedIsFalse = refl
