module DASHI.Physics.Closure.NSTriadKNLiteralNestedOuterRadiusDefectRound431Exact where

------------------------------------------------------------------------
-- ROUND431 / PHYSICAL RADIUS CALIBRATION -> DIVISION-FREE OUTER-SLOT GAIN
--
-- R430 proves on the literal R329 nested carrier
--
--   ||G_outer||^2
--     <= 12 ||P+Q||^2 ||F_inner||^2 ||u_q||^2.
--
-- R146/R175 own the complementary resonant geometry in division-free form:
--
--   r_p r_q ||P+Q||^2 <= r_k^2.
--
-- The repository's weak RealField deliberately does not permit cancelling a
-- nonzero helical component to manufacture the scalar equation m(k)^2=|k|^2
-- from the vector action theorem of R126.  This owner therefore isolates the
-- exact physical radius calibration needed to connect those two already-owned
-- theorem families.  No new Navier--Stokes estimate is hidden in the receipt.
--
-- Once supplied, the compiler proves
--
--   (r_p r_q) ||G_outer||^2
--     <= 12 |k|^2 ||F_inner||^2 ||u_q||^2.
--
-- This is the form wanted before heat/resolvent aggregation: no square root,
-- no division, no shell count and no fibre-cardinality factor occur.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNLiteralNestedOuterAntiParallelNormRound430Exact as R430
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174

F = R329.F

record LiteralOuterRadiusCalibration
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (C : R329.StrongLowLiteralNestedCell E I O system S L H W) : Set where
  constructor literal-outer-radius-calibration
  field
    radiusP radiusQ radiusK : ℚ

    radiusPMeaning : radiusP ≡ Helical.modeNorm S (Physical.p (R329.outer C))
    radiusQMeaning : radiusQ ≡ Helical.modeNorm S (Physical.q (R329.outer C))

    -- This is the scalar physical calibration that R126 intentionally does not
    -- derive by cancellation on the weak RealField carrier.
    outputRadiusSquareMeaning :
      radiusK * radiusK ≡ C3.normSquared I (Physical.k (R329.outer C))

    radiusProductNN : 0ℚ ≤ radiusP * radiusQ
    outputSquareNN : 0ℚ ≤ radiusK * radiusK

    scaledNormalizedDefectBound :
      (radiusP * radiusQ)
        * L2.complex3NormSquared
            (R329.outerAntiParallelDefect E I O system S L H W C)
      ≤ radiusK * radiusK

open LiteralOuterRadiusCalibration public

literalOuterSlotDivisionFreeLowOutputBound :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  (cal : LiteralOuterRadiusCalibration E I O system S L H W C) →
  (radiusP cal * radiusQ cal)
    * L2.complex3NormSquared
        (R329.literalNestedOuterSlot E I O system S L H W C)
  ≤ R174.twelve
      * (C3.normSquared I (Physical.k (R329.outer C))
        * L2.complex3NormSquared
            (R329.innerPairedForcing E I O system S L H W C)
        * L2.complex3NormSquared
            (Audit.velocity system (Physical.q (R329.outer C))))
literalOuterSlotDivisionFreeLowOutputBound E I O system S L H W C cal =
  let
    rpq = radiusP cal * radiusQ cal
    defect = L2.complex3NormSquared
      (R329.outerAntiParallelDefect E I O system S L H W C)
    innerMass = L2.complex3NormSquared
      (R329.innerPairedForcing E I O system S L H W C)
    qMass = L2.complex3NormSquared
      (Audit.velocity system (Physical.q (R329.outer C)))
    outputSquare = C3.normSquared I (Physical.k (R329.outer C))

    defectNN = Separation.complex3NormSquaredNonnegative
      (R329.outerAntiParallelDefect E I O system S L H W C)
    innerNN = Separation.complex3NormSquaredNonnegative
      (R329.innerPairedForcing E I O system S L H W C)
    qNN = Separation.complex3NormSquaredNonnegative
      (Audit.velocity system (Physical.q (R329.outer C)))

    outerBound = R430.literalNestedOuterSlotAngularNormBound
      E I O system S L H W C

    scaledOuter :
      rpq * L2.complex3NormSquared
        (R329.literalNestedOuterSlot E I O system S L H W C)
      ≤ rpq * (R174.twelve * (defect * innerMass * qMass))
    scaledOuter =
      let instance rpqNNI = nonNegative (radiusProductNN cal)
      in ℚP.*-monoˡ-≤-nonNeg rpq outerBound

    defectToOutput : rpq * defect ≤ outputSquare
    defectToOutput =
      subst
        (λ upper → rpq * defect ≤ upper)
        (outputRadiusSquareMeaning cal)
        (scaledNormalizedDefectBound cal)

    outputNN : 0ℚ ≤ outputSquare
    outputNN = subst (0ℚ ≤_) (outputRadiusSquareMeaning cal) (outputSquareNN cal)

    innerScaled :
      (rpq * defect) * innerMass ≤ outputSquare * innerMass
    innerScaled =
      Rational.nonnegativeProductMonotone
        (R96.productNonnegative (radiusProductNN cal) defectNN)
        innerNN
        outputNN
        innerNN
        defectToOutput ℚP.≤-refl

    qScaled :
      ((rpq * defect) * innerMass) * qMass
      ≤ (outputSquare * innerMass) * qMass
    qScaled =
      Rational.nonnegativeProductMonotone
        (R96.productNonnegative
          (R96.productNonnegative (radiusProductNN cal) defectNN)
          innerNN)
        qNN
        (R96.productNonnegative outputNN innerNN)
        qNN
        innerScaled ℚP.≤-refl

    twelveNN : 0ℚ ≤ R174.twelve
    twelveNN =
      let
        oneNN = Rational.squareNonnegative 1ℚ
        twoNN = Rational.addNonnegative oneNN oneNN
        fourNN = Rational.addNonnegative twoNN twoNN
      in Rational.addNonnegative (Rational.addNonnegative fourNN fourNN) fourNN

    twelveScaled :
      R174.twelve * (((rpq * defect) * innerMass) * qMass)
      ≤ R174.twelve * ((outputSquare * innerMass) * qMass)
    twelveScaled =
      let instance tNNI = nonNegative twelveNN
      in ℚP.*-monoˡ-≤-nonNeg R174.twelve qScaled

    leftMeaning :
      rpq * (R174.twelve * (defect * innerMass * qMass))
      ≡ R174.twelve * (((rpq * defect) * innerMass) * qMass)
    leftMeaning = solve (rpq ∷ defect ∷ innerMass ∷ qMass ∷ R174.twelve ∷ [])

    rightMeaning :
      R174.twelve * ((outputSquare * innerMass) * qMass)
      ≡ R174.twelve * (outputSquare * innerMass * qMass)
    rightMeaning = solve (outputSquare ∷ innerMass ∷ qMass ∷ R174.twelve ∷ [])
  in
  ℚP.≤-trans scaledOuter
    (subst
      (λ lower → lower ≤ R174.twelve * (outputSquare * innerMass * qMass))
      (sym leftMeaning)
      (subst
        (λ upper →
          R174.twelve * (((rpq * defect) * innerMass) * qMass) ≤ upper)
        rightMeaning
        twelveScaled))

round431DivisionFreeOuterLowOutputCompilerClosed : Bool
round431DivisionFreeOuterLowOutputCompilerClosed = true

round431ScalarCancellationUsed : Bool
round431ScalarCancellationUsed = false

round431SquareRootUsed : Bool
round431SquareRootUsed = false

round431FibreCardinalityUsed : Bool
round431FibreCardinalityUsed = false

round431PhysicalRadiusCalibrationInhabitedForLiteralOuterCells : Bool
round431PhysicalRadiusCalibrationInhabitedForLiteralOuterCells = false

round431RowColumnAggregationClosed : Bool
round431RowColumnAggregationClosed = false

round431R423SignedCommonCrossPaid : Bool
round431R423SignedCommonCrossPaid = false

round431PackageAClosed : Bool
round431PackageAClosed = false

round431ClayPromotion : Bool
round431ClayPromotion = false

round431DivisionFreeOuterLowOutputCompilerClosedIsTrue :
  round431DivisionFreeOuterLowOutputCompilerClosed ≡ true
round431DivisionFreeOuterLowOutputCompilerClosedIsTrue = refl

round431PhysicalRadiusCalibrationInhabitedForLiteralOuterCellsIsFalse :
  round431PhysicalRadiusCalibrationInhabitedForLiteralOuterCells ≡ false
round431PhysicalRadiusCalibrationInhabitedForLiteralOuterCellsIsFalse = refl

round431R423SignedCommonCrossPaidIsFalse :
  round431R423SignedCommonCrossPaid ≡ false
round431R423SignedCommonCrossPaidIsFalse = refl
