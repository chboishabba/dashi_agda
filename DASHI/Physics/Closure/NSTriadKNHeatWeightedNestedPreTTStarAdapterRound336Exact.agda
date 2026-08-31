module DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPreTTStarAdapterRound336Exact where

------------------------------------------------------------------------
-- ROUND336 / THIN ADAPTER FROM THE NEW F_s CARRIER TO THE OLD PRE-TT* OWNER
--
-- R335 establishes that signed pre-TT* aggregation is already canonical.
-- What is new is only the physical cell family being paired: the literal
-- heat/resolvent-weighted nested R329 forcing cells.
--
-- For two such cells on the same final output fibre, keep the real Hermitian
-- overlap SIGNED:
--
--   Re < X_left , X_right >.
--
-- A physical pairwise theorem must provide one shell-aware local envelope for
-- that overlap.  Once it does, this file maps the receipt directly into R29's
-- existing SignedCrossShellCell.  No atomwise l1 majorization, row cardinality,
-- or new TT* abstraction is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_; ∣_∣)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNSignedCrossShellAlmostOrthogonalityRound29Exact as R29
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329

F : C3.RealField _
F = Rational.rationalRealField

record HeatWeightedNestedPairwiseOverlap
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F) : Set where
  constructor heat-weighted-nested-pairwise-overlap
  field
    left right : R329.StrongLowLiteralNestedCell E I O system S L H W
    leftShell rightShell : Nat

    sameFinalOutput :
      Physical.k (R329.outer left) ≡ Physical.k (R329.outer right)

    localEnvelope : ℚ

    signedOverlapBound :
      ∣ R179.realHermitianCross
          (R329.literalWeightedNestedCell E I O system S L H W left)
          (R329.literalWeightedNestedCell E I O system S L H W right) ∣
      ≤ localEnvelope

open HeatWeightedNestedPairwiseOverlap public

signedNestedOverlap :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  HeatWeightedNestedPairwiseOverlap E I O system S L H W → ℚ
signedNestedOverlap E I O system S L H W P =
  R179.realHermitianCross
    (R329.literalWeightedNestedCell E I O system S L H W (left P))
    (R329.literalWeightedNestedCell E I O system S L H W (right P))

asRound29SignedCrossShellCell :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  HeatWeightedNestedPairwiseOverlap E I O system S L H W →
  R29.SignedCrossShellCell
asRound29SignedCrossShellCell E I O system S L H W P =
  R29.signed-cross-shell-cell
    (leftShell P)
    (rightShell P)
    (signedNestedOverlap E I O system S L H W P)
    (localEnvelope P)
    (signedOverlapBound P)

round336LiteralR329PairingAdapterClosed : Bool
round336LiteralR329PairingAdapterClosed = true

round336ReusesExistingR29PreTTStarOwner : Bool
round336ReusesExistingR29PreTTStarOwner = true

round336SameFinalOutputRetained : Bool
round336SameFinalOutputRetained = true

round336AtomwiseL1MajorizationUsed : Bool
round336AtomwiseL1MajorizationUsed = false

round336PhysicalPairwiseOverlapEnvelopeClosed : Bool
round336PhysicalPairwiseOverlapEnvelopeClosed = false

round336CutoffUniformCotlarSteinClosed : Bool
round336CutoffUniformCotlarSteinClosed = false

round336SpacetimeFsPaid : Bool
round336SpacetimeFsPaid = false

round336PackageAClosed : Bool
round336PackageAClosed = false

round336ClayPromotion : Bool
round336ClayPromotion = false

round336AtomwiseL1MajorizationUsedIsFalse :
  round336AtomwiseL1MajorizationUsed ≡ false
round336AtomwiseL1MajorizationUsedIsFalse = refl

round336PackageAClosedIsFalse : round336PackageAClosed ≡ false
round336PackageAClosedIsFalse = refl

round336ClayPromotionIsFalse : round336ClayPromotion ≡ false
round336ClayPromotionIsFalse = refl
