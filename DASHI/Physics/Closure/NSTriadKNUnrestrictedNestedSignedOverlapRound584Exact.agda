module DASHI.Physics.Closure.NSTriadKNUnrestrictedNestedSignedOverlapRound584Exact where

------------------------------------------------------------------------
-- ROUND584 / PREFERRED SIGNED OVERLAP ON THE UNRESTRICTED R573 CARRIER
--
-- R329/R336 were useful historical adapters but carry two avoidable defects for
-- the modern direct route:
--
--   * R329 is a strongly-low subcone and stores an uncalibrated R321 scale tag;
--   * R336 stores free Nat shell labels unrelated to its physical cells.
--
-- R571--R573 have since removed the raw-helical/strong-low packaging from the
-- exact weighted commutator representation.  R573.nestedWeightedCompanionCell
-- is the literal weighted R438/R294 object, with the COMPLETE inner fibre
-- already expanded componentwise and p=0 handled exactly.
--
-- Therefore the preferred signed pairwise carrier can live directly on two
-- outer physical incidences.  Shell labels are derived, never supplied.
-- The only remaining semantic choice is WHICH outer coordinate indexes the
-- operator family: forcing leg p, partner leg q, or final output k.
--
-- No cross-shell decay or summability theorem is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (∣_-_∣)
open import Data.Rational.Base using (ℚ; _+_; _≤_; ∣_∣)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNSignedCrossShellAlmostOrthogonalityRound29Exact as R29
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact as R579
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell

F : C3.RealField _
F = Rational.rationalRealField

data OuterOperatorShellCoordinate584 : Set where
  outerForcing584 : OuterOperatorShellCoordinate584
  outerPartner584 : OuterOperatorShellCoordinate584
  finalOutput584 : OuterOperatorShellCoordinate584

modeAtOuterCoordinate584 :
  OuterOperatorShellCoordinate584 →
  Physical.PhysicalTriadIncidence → Z3.FourierMode
modeAtOuterCoordinate584 outerForcing584 tau = Physical.p tau
modeAtOuterCoordinate584 outerPartner584 tau = Physical.q tau
modeAtOuterCoordinate584 finalOutput584 tau = Physical.k tau

shellAtOuterCoordinate584 :
  OuterOperatorShellCoordinate584 →
  Physical.PhysicalTriadIncidence → Nat
shellAtOuterCoordinate584 coordinate tau =
  Shell.shellIndex (modeAtOuterCoordinate584 coordinate tau)

module UnrestrictedNested584
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Nested = R573.WeightedNested W S L H system velocityTransverse

  literalNestedCell584 :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  literalNestedCell584 = Nested.nestedWeightedCompanionCell

  signedOverlap584 :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  signedOverlap584 left right =
    R179.realHermitianCross
      (literalNestedCell584 left)
      (literalNestedCell584 right)

  localMassEnvelope584 :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  localMassEnvelope584 left right =
    L2.complex3NormSquared (literalNestedCell584 left)
    + L2.complex3NormSquared (literalNestedCell584 right)

  localMassEnvelopeBoundsSignedOverlap584 :
    (left right : Physical.PhysicalTriadIncidence) →
    ∣ signedOverlap584 left right ∣ ≤ localMassEnvelope584 left right
  localMassEnvelopeBoundsSignedOverlap584 left right =
    R579.rationalRealHermitianYoung
      (literalNestedCell584 left)
      (literalNestedCell584 right)

  record SameOutputNestedPair584 : Set where
    constructor same-output-nested-pair584
    field
      left584 right584 : Physical.PhysicalTriadIncidence
      sameFinalOutput584 : Physical.k left584 ≡ Physical.k right584

  open SameOutputNestedPair584 public

  leftShell584 :
    OuterOperatorShellCoordinate584 → SameOutputNestedPair584 → Nat
  leftShell584 coordinate pair =
    shellAtOuterCoordinate584 coordinate (left584 pair)

  rightShell584 :
    OuterOperatorShellCoordinate584 → SameOutputNestedPair584 → Nat
  rightShell584 coordinate pair =
    shellAtOuterCoordinate584 coordinate (right584 pair)

  shellSeparation584 :
    OuterOperatorShellCoordinate584 → SameOutputNestedPair584 → Nat
  shellSeparation584 coordinate pair =
    ∣ leftShell584 coordinate pair - rightShell584 coordinate pair ∣

  asRound29SignedCrossShellCell584 :
    (coordinate : OuterOperatorShellCoordinate584) →
    SameOutputNestedPair584 →
    R29.SignedCrossShellCell
  asRound29SignedCrossShellCell584 coordinate pair =
    R29.signed-cross-shell-cell
      (leftShell584 coordinate pair)
      (rightShell584 coordinate pair)
      (signedOverlap584 (left584 pair) (right584 pair))
      (localMassEnvelope584 (left584 pair) (right584 pair))
      (localMassEnvelopeBoundsSignedOverlap584
        (left584 pair) (right584 pair))

  record SeparationIndexedEnvelope584
      (coordinate : OuterOperatorShellCoordinate584)
      (pair : SameOutputNestedPair584) : Set where
    constructor separation-indexed-envelope584
    field
      separationProfile584 : Nat → ℚ
      profilePaysLocalEnvelope584 :
        localMassEnvelope584 (left584 pair) (right584 pair)
        ≤ separationProfile584 (shellSeparation584 coordinate pair)

  open SeparationIndexedEnvelope584 public

------------------------------------------------------------------------
-- Proof-search correction.
------------------------------------------------------------------------

data UnrestrictedNestedResidual584 : Set where
  missingOuterOperatorShellSemantics584 : UnrestrictedNestedResidual584
  missingSeparationIndexedOverlapDecay584 : UnrestrictedNestedResidual584
  missingCutoffUniformSeparationSummation584 : UnrestrictedNestedResidual584

currentResidual584 : UnrestrictedNestedResidual584
currentResidual584 = missingOuterOperatorShellSemantics584

round584LiteralWeightedR294NestedSameObject : Bool
round584LiteralWeightedR294NestedSameObject =
  R573.round573R438WeightedCommutatorNestedSameObjectWeldClosed

round584StrongLowReceiptRequired : Bool
round584StrongLowReceiptRequired = false

round584RawVelocitySingleHelicityRequired : Bool
round584RawVelocitySingleHelicityRequired = false

round584FreeShellLabelsAccepted : Bool
round584FreeShellLabelsAccepted = false

round584LocalSignedOverlapEnvelopeClosed : Bool
round584LocalSignedOverlapEnvelopeClosed = true

round584OuterOperatorShellCoordinateSelected : Bool
round584OuterOperatorShellCoordinateSelected = false

round584SeparationIndexedDecayClosed : Bool
round584SeparationIndexedDecayClosed = false

round584CutoffUniformSeparationSummationClosed : Bool
round584CutoffUniformSeparationSummationClosed = false

round584LeafAClosed : Bool
round584LeafAClosed = false

round584ClayPromotion : Bool
round584ClayPromotion = false

round584LiteralWeightedR294NestedSameObjectIsTrue :
  round584LiteralWeightedR294NestedSameObject ≡ true
round584LiteralWeightedR294NestedSameObjectIsTrue =
  R573.round573R438WeightedCommutatorNestedSameObjectWeldClosedIsTrue

round584StrongLowReceiptRequiredIsFalse :
  round584StrongLowReceiptRequired ≡ false
round584StrongLowReceiptRequiredIsFalse = refl

round584LocalSignedOverlapEnvelopeClosedIsTrue :
  round584LocalSignedOverlapEnvelopeClosed ≡ true
round584LocalSignedOverlapEnvelopeClosedIsTrue = refl

round584ClayPromotionIsFalse : round584ClayPromotion ≡ false
round584ClayPromotionIsFalse = refl
