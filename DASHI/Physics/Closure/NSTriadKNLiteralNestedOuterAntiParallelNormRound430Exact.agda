module DASHI.Physics.Closure.NSTriadKNLiteralNestedOuterAntiParallelNormRound430Exact where

------------------------------------------------------------------------
-- ROUND430 / LITERAL R329 OUTER SLOT -> ANTI-PARALLEL L2 GAIN
--
-- R329 now proves that its ACTUAL inner paired forcing is transverse to the
-- outer p leg and retains the physical outer-q velocity transversality.  Hence
-- the exact R145 anti-parallel factorization applies on the same nested cell.
-- R174 then gives, without square roots or cardinality factors,
--
--   ||G_outer||^2
--     <= 12 ||P + Q||^2 ||F_inner||^2 ||u_q||^2,
--
-- where P,Q are the literal R167 normalized directions and G_outer is exactly
-- R329.literalNestedOuterSlot.
--
-- This is a genuine physical pointwise gain, not a generic proxy.  It does not
-- yet claim the remaining geometric scalar weld
--
--   |p||q| ||P+Q||^2 <= |k|^2,
--
-- nor any row/column/heat aggregation.  Those are now the next sharply typed
-- payments rather than hidden inside an abstract Schur constant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (_≤_)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329

F : C3.RealField _
F = R329.F

literalNestedOuterSlotAngularNormBound :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  L2.complex3NormSquared
    (R329.literalNestedOuterSlot E I O system S L H W C)
  ≤ R174.twelve *
      (L2.complex3NormSquared
        (R329.outerAntiParallelDefect E I O system S L H W C)
       * L2.complex3NormSquared
          (R329.innerPairedForcing E I O system S L H W C)
       * L2.complex3NormSquared
          (Audit.velocity system (Physical.q (R329.outer C))))
literalNestedOuterSlotAngularNormBound E I O system S L H W C =
  R174.kernelNormBelowTwelveAngularProduct
    (R167.normalizedDirection E S (Physical.p (R329.outer C)))
    (R167.normalizedDirection E S (Physical.q (R329.outer C)))
    (R329.innerPairedForcing E I O system S L H W C)
    (Audit.velocity system (Physical.q (R329.outer C)))
    (R329.outerTransverseHighPair E I O system S L H W C)

round430LiteralR329OuterSlotAngularNormBoundClosed : Bool
round430LiteralR329OuterSlotAngularNormBoundClosed = true

round430UsesGenericReplacementForcing : Bool
round430UsesGenericReplacementForcing = false

round430UsesSquareRoot : Bool
round430UsesSquareRoot = false

round430UsesFibreCardinality : Bool
round430UsesFibreCardinality = false

round430NormalizedDefectScaledByOuterRadiiToOutputSquareClosed : Bool
round430NormalizedDefectScaledByOuterRadiiToOutputSquareClosed = false

round430RowColumnAggregationClosed : Bool
round430RowColumnAggregationClosed = false

round430R423SignedCommonCrossPaid : Bool
round430R423SignedCommonCrossPaid = false

round430PackageAClosed : Bool
round430PackageAClosed = false

round430ClayPromotion : Bool
round430ClayPromotion = false

round430LiteralR329OuterSlotAngularNormBoundClosedIsTrue :
  round430LiteralR329OuterSlotAngularNormBoundClosed ≡ true
round430LiteralR329OuterSlotAngularNormBoundClosedIsTrue = refl

round430NormalizedDefectScaledByOuterRadiiToOutputSquareClosedIsFalse :
  round430NormalizedDefectScaledByOuterRadiiToOutputSquareClosed ≡ false
round430NormalizedDefectScaledByOuterRadiiToOutputSquareClosedIsFalse = refl

round430R423SignedCommonCrossPaidIsFalse :
  round430R423SignedCommonCrossPaid ≡ false
round430R423SignedCommonCrossPaidIsFalse = refl
