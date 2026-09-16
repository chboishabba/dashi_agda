module DASHI.Physics.Closure.NSTriadKNLiteralSpectatorResolventOverlapRound587Exact where

------------------------------------------------------------------------
-- ROUND587 / LEAST-PRIVILEGE WEIGHT SPECIALIZATION FOR THE SIGNED OVERLAP
--
-- R584/R586 deliberately accept an arbitrary R294 swap-invariant cell weight.
-- That is useful as an abstract compiler surface, but it is stronger than the
-- actual R406 leaf-A consumer.  The live forcing square uses, for each fixed
-- spectator beta,
--
--   W_beta(alpha) = K(alpha,beta)
--                 = 1 / (lambda_alpha + lambda_beta),
--
-- exactly as proved by R541.
--
-- A cutoff-uniform overlap theorem for EVERY swap-invariant W would erase the
-- physical denominator structure and is not a least-privilege prerequisite.
-- This file therefore specializes the unrestricted R573/R584 nested carrier to
-- the literal spectator-resolvent weight.  It keeps the same-final-output
-- overlap and local Hermitian envelope, while exposing the exact R406 weight
-- meaning at every cell.
--
-- No shell decay, summability, norm estimate, or spacetime theorem is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _≤_; ∣_∣)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact as R579
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell

F : C3.RealField _
F = Rational.rationalRealField

module LiteralSpectatorOverlap587
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (O : Leray.RationalInverseNormOrder
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem))
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocityAt (Field30.finiteSystem physicalSystem) mode)) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem

  module Spec = R541.Spectator physicalSystem S
  module Swap = R538.PairSwap physicalSystem S

  literalWeight587 :
    Physical.PhysicalTriadIncidence → R294.SwapInvariantCellWeight F
  literalWeight587 = Spec.spectatorWeight

  literalWeightMeaning587 :
    (beta alpha : Physical.PhysicalTriadIncidence) →
    R294.weight (literalWeight587 beta) alpha
    ≡ C3.realEmbed F (Swap.pairResolvent alpha beta)
  literalWeightMeaning587 = Spec.spectatorWeightMeaning

  literalNestedCell587 :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    C3.Complex3 F
  literalNestedCell587 beta alpha =
    let
      module N = R573.WeightedNested
        (literalWeight587 beta) S L H system velocityTransverse
    in
    N.nestedWeightedCompanionCell alpha

  signedOverlap587 :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  signedOverlap587 beta left right =
    R179.realHermitianCross
      (literalNestedCell587 beta left)
      (literalNestedCell587 beta right)

  localMassEnvelope587 :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  localMassEnvelope587 beta left right =
    L2.complex3NormSquared (literalNestedCell587 beta left)
    + L2.complex3NormSquared (literalNestedCell587 beta right)

  localMassEnvelopeBoundsSignedOverlap587 :
    (beta left right : Physical.PhysicalTriadIncidence) →
    ∣ signedOverlap587 beta left right ∣
    ≤ localMassEnvelope587 beta left right
  localMassEnvelopeBoundsSignedOverlap587 beta left right =
    R579.rationalRealHermitianYoung
      (literalNestedCell587 beta left)
      (literalNestedCell587 beta right)

  record SameOutputSpectatorPair587 : Set where
    constructor same-output-spectator-pair587
    field
      spectator587 : Physical.PhysicalTriadIncidence
      left587 right587 : Physical.PhysicalTriadIncidence
      sameFinalOutput587 : Physical.k left587 ≡ Physical.k right587

  open SameOutputSpectatorPair587 public

  leftOperatorShell587 : SameOutputSpectatorPair587 → Nat
  leftOperatorShell587 P = Shell.shellIndex (Physical.p (left587 P))

  rightOperatorShell587 : SameOutputSpectatorPair587 → Nat
  rightOperatorShell587 P = Shell.shellIndex (Physical.p (right587 P))

  pairOverlap587 : SameOutputSpectatorPair587 → ℚ
  pairOverlap587 P =
    signedOverlap587 (spectator587 P) (left587 P) (right587 P)

  pairEnvelope587 : SameOutputSpectatorPair587 → ℚ
  pairEnvelope587 P =
    localMassEnvelope587 (spectator587 P) (left587 P) (right587 P)

  pairEnvelopePaysOverlap587 :
    (P : SameOutputSpectatorPair587) →
    ∣ pairOverlap587 P ∣ ≤ pairEnvelope587 P
  pairEnvelopePaysOverlap587 P =
    localMassEnvelopeBoundsSignedOverlap587
      (spectator587 P) (left587 P) (right587 P)

------------------------------------------------------------------------
-- Frontier correction.
------------------------------------------------------------------------

data SpectatorOverlapResidual587 : Set where
  missingPhysicalRadiusSquareCalibration587 : SpectatorOverlapResidual587
  missingLiteralResolventShellEnvelope587 : SpectatorOverlapResidual587
  missingCutoffUniformSpectatorEnvelopeMass587 : SpectatorOverlapResidual587
  missingSpacetimeTransport587 : SpectatorOverlapResidual587

currentResidual587 : SpectatorOverlapResidual587
currentResidual587 = missingPhysicalRadiusSquareCalibration587

round587ArbitrarySwapInvariantWeightMandatory : Bool
round587ArbitrarySwapInvariantWeightMandatory = false

round587LiteralSpectatorResolventWeightSelected : Bool
round587LiteralSpectatorResolventWeightSelected =
  R541.round541SpectatorWeightIsLiteralPairResolvent

round587UnrestrictedNestedCarrierRetained : Bool
round587UnrestrictedNestedCarrierRetained =
  R573.round573R438WeightedCommutatorNestedSameObjectWeldClosed

round587LocalOverlapEnvelopeClosed : Bool
round587LocalOverlapEnvelopeClosed = true

round587PhysicalRadiusSquareCalibrationClosed : Bool
round587PhysicalRadiusSquareCalibrationClosed = false

round587ResolventShellEnvelopeClosed : Bool
round587ResolventShellEnvelopeClosed = false

round587CutoffUniformSpectatorEnvelopeMassClosed : Bool
round587CutoffUniformSpectatorEnvelopeMassClosed = false

round587LeafAClosed : Bool
round587LeafAClosed = false

round587ClayPromotion : Bool
round587ClayPromotion = false

round587ArbitrarySwapInvariantWeightMandatoryIsFalse :
  round587ArbitrarySwapInvariantWeightMandatory ≡ false
round587ArbitrarySwapInvariantWeightMandatoryIsFalse = refl

round587LiteralSpectatorResolventWeightSelectedIsTrue :
  round587LiteralSpectatorResolventWeightSelected ≡ true
round587LiteralSpectatorResolventWeightSelectedIsTrue =
  R541.round541SpectatorWeightIsLiteralPairResolventIsTrue

round587LocalOverlapEnvelopeClosedIsTrue :
  round587LocalOverlapEnvelopeClosed ≡ true
round587LocalOverlapEnvelopeClosedIsTrue = refl

round587ClayPromotionIsFalse : round587ClayPromotion ≡ false
round587ClayPromotionIsFalse = refl
