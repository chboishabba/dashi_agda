module DASHI.Physics.Closure.NSTriadKNLiteralNestedPairwiseMassEnvelopeRound580Exact where

------------------------------------------------------------------------
-- ROUND580 / LITERAL R329 PAIR -> CONCRETE R336 LOCAL OVERLAP RECEIPT
--
-- R579 proves on the exact rational C^3 carrier
--
--   |Re <X,Y>| <= ||X||^2 + ||Y||^2.
--
-- Instantiate X,Y as the ACTUAL weighted nested R329 cells.  This constructs
-- the local R336 physical pairwise-overlap receipt without square roots,
-- row/column Schur, or a proxy kernel.
--
-- IMPORTANT BOUNDARY:
--   local overlap receipt != R29 cutoff-uniform decay certificate.
--
-- The mass envelope below may still repeat a cell once for every coherent
-- partner.  R179 already proves that mass-only same-output control cannot by
-- itself eliminate such multiplicity.  Therefore this owner advances the
-- preferred signed route only from "missing local overlap inequality" to
-- "missing shell-decaying envelope mass".
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPreTTStarAdapterRound336Exact as R336
import DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact as R579

F : C3.RealField _
F = Rational.rationalRealField

literalNestedCellMass :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  R329.StrongLowLiteralNestedCell E I O system S L H W →
  ℚ
literalNestedCellMass E I O system S L H W C =
  L2.complex3NormSquared
    (R329.literalWeightedNestedCell E I O system S L H W C)

massPairEnvelope :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  R329.StrongLowLiteralNestedCell E I O system S L H W →
  R329.StrongLowLiteralNestedCell E I O system S L H W →
  ℚ
massPairEnvelope E I O system S L H W left right =
  literalNestedCellMass E I O system S L H W left
  + literalNestedCellMass E I O system S L H W right

literalNestedMassEnvelopeBound :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (left right : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  let X = R329.literalWeightedNestedCell E I O system S L H W left
      Y = R329.literalWeightedNestedCell E I O system S L H W right
  in
  Data.Rational.Base.∣ R336.signedNestedOverlap E I O system S L H W
      (R336.heat-weighted-nested-pairwise-overlap
        left right 0 0 refl
        (massPairEnvelope E I O system S L H W left right)
        (R579.rationalRealHermitianYoung X Y)) ∣
  ≤ massPairEnvelope E I O system S L H W left right
literalNestedMassEnvelopeBound E I O system S L H W left right =
  R579.rationalRealHermitianYoung
    (R329.literalWeightedNestedCell E I O system S L H W left)
    (R329.literalWeightedNestedCell E I O system S L H W right)

-- Preferred constructor: shell labels and same-final-output identity are kept
-- exactly as consumer-visible coordinates rather than inferred from the mass
-- inequality.
literalNestedPairwiseOverlapFromMass :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (left right : R329.StrongLowLiteralNestedCell E I O system S L H W)
  (leftShell rightShell : Nat) →
  Physical.k (R329.outer left) ≡ Physical.k (R329.outer right) →
  R336.HeatWeightedNestedPairwiseOverlap E I O system S L H W
literalNestedPairwiseOverlapFromMass
    E I O system S L H W left right leftShell rightShell sameOutput =
  let
    X = R329.literalWeightedNestedCell E I O system S L H W left
    Y = R329.literalWeightedNestedCell E I O system S L H W right
  in
  R336.heat-weighted-nested-pairwise-overlap
    left right
    leftShell rightShell
    sameOutput
    (massPairEnvelope E I O system S L H W left right)
    (R579.rationalRealHermitianYoung X Y)

round580LiteralR336LocalOverlapReceiptConstructed : Bool
round580LiteralR336LocalOverlapReceiptConstructed = true

round580UsesSquareRoot : Bool
round580UsesSquareRoot = false

round580UsesRowColumnSchur : Bool
round580UsesRowColumnSchur = false

round580UsesFibreCardinality : Bool
round580UsesFibreCardinality = false

-- The new local envelope is intentionally not promoted into a decay theorem.
round580MassEnvelopeCrossShellDecayClosed : Bool
round580MassEnvelopeCrossShellDecayClosed = false

round580CutoffUniformSignedPreTTStarClosed : Bool
round580CutoffUniformSignedPreTTStarClosed = false

round580LeafAClosed : Bool
round580LeafAClosed = false

round580ClayPromotion : Bool
round580ClayPromotion = false

round580LiteralR336LocalOverlapReceiptConstructedIsTrue :
  round580LiteralR336LocalOverlapReceiptConstructed ≡ true
round580LiteralR336LocalOverlapReceiptConstructedIsTrue = refl

round580ClayPromotionIsFalse : round580ClayPromotion ≡ false
round580ClayPromotionIsFalse = refl
