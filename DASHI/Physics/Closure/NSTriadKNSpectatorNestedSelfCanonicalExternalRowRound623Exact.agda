{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNSpectatorNestedSelfCanonicalExternalRowRound623Exact where

------------------------------------------------------------------------
-- ROUND623 / SIGNED SPECTATOR NESTED ROW = SELF + CANONICAL EXTERNAL
--
-- The live R568 nested Leaf-A route consumes, for fixed output k and spectator
-- beta,
--
--   Re < sum_alpha Nested_beta(alpha) , DoubleCell(beta) >.
--
-- R614 already splits the SAME R573 nested vector fold into self + external.
-- R291 makes the Hermitian scalar additive in that first vector slot.
-- R622 rewrites the complete external vector fold onto the canonical
-- orbit-resolved finite carrier, with fixed-orbit multiplicity corrections
-- retained.
--
-- Hence the exact signed scalar row itself is now
--
--   NestedRow = SelfNestedRow + CanonicalExternalNestedRow.
--
-- This is the scalar immediately upstream of the live R568 output/time
-- aggregation.  No norm, absolute value, estimate, or cancellation is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedForcingSquareBidiExact as NestedFixed
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNR573ExternalResidualNestedCarrierRound614Exact as R614Nested
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedExternalNestedFoldRound622Exact as R622

F : C3.RealField _
F = Rational.rationalRealField

module SignedRowSplit
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  system = Field30.finiteSystem physicalSystem

  module Spec = R541.Spectator physicalSystem S
  module Row = R545.Row physicalSystem S
  module Weld = NestedFixed.Weld
    physicalSystem S L H velocityTransverse

  module Split (beta : Physical.PhysicalTriadIncidence) =
    R613.NestedNetworkSplit
      (Spec.spectatorWeight beta) S L H system velocityTransverse

  module FoldSplit (beta : Physical.PhysicalTriadIncidence) =
    R614Nested.ExternalNestedResidual
      (Spec.spectatorWeight beta) S L H system velocityTransverse

  module CanonicalExternal (beta : Physical.PhysicalTriadIncidence) =
    R622.CanonicalExternalNested
      (Spec.spectatorWeight beta) S L H system velocityTransverse

  selfNestedForcingRow :
    Z3.FourierMode →
    Physical.PhysicalTriadIncidence → ℚ
  selfNestedForcingRow output beta =
    let
      module N = Split beta
      items = Output.physicalOutputFiber (Audit.cutoff system) output
    in
    R179.realHermitianCross
      (R224.foldVector N.selfNestedWeightedCompanionCell items)
      (Row.doubleCell beta)

  canonicalExternalNestedForcingRow :
    Z3.FourierMode →
    Physical.PhysicalTriadIncidence → ℚ
  canonicalExternalNestedForcingRow output beta =
    let
      module C = CanonicalExternal beta
    in
    R179.realHermitianCross
      (C.canonicalExternalNestedFold output)
      (Row.doubleCell beta)

  nestedForcingRowSplitsSelfCanonicalExternal :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    Weld.nestedForcingRow output beta
    ≡
    selfNestedForcingRow output beta
      + canonicalExternalNestedForcingRow output beta
  nestedForcingRowSplitsSelfCanonicalExternal output beta =
    let
      module N = Split beta
      module FS = FoldSplit beta
      module C = CanonicalExternal beta

      items = Output.physicalOutputFiber (Audit.cutoff system) output
      fullFold =
        R224.foldVector N.Nested.nestedWeightedCompanionCell items
      selfFold =
        R224.foldVector N.selfNestedWeightedCompanionCell items
      externalFold =
        R224.foldVector N.externalNestedWeightedCompanionCell items
      test = Row.doubleCell beta

      splitVector :
        fullFold ≡ C3.complex3Add selfFold externalFold
      splitVector = FS.fixedOutputNestedFoldSplitsSelfExternal output

      externalCanonical :
        externalFold ≡ C.canonicalExternalNestedFold output
      externalCanonical = C.fixedOutputExternalNestedFoldIsCanonical output
    in
    trans
      (cong
        (λ value → R179.realHermitianCross value test)
        splitVector)
      (trans
        (R291.realCrossAddLeft selfFold externalFold test)
        (cong
          (selfNestedForcingRow output beta +_)
          (cong
            (λ value → R179.realHermitianCross value test)
            externalCanonical)))

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round623SignedNestedRowSelfExternalSplitClosed : Bool
round623SignedNestedRowSelfExternalSplitClosed = true

round623ExternalRowOnCanonicalOrbitResolvedCarrier : Bool
round623ExternalRowOnCanonicalOrbitResolvedCarrier = true

round623FixedOrbitCorrectionPreservedBeforeHermitianPairing : Bool
round623FixedOrbitCorrectionPreservedBeforeHermitianPairing = true

round623IntroducesNormOrAbsoluteValue : Bool
round623IntroducesNormOrAbsoluteValue = false

round623IntroducesEstimate : Bool
round623IntroducesEstimate = false

round623SelfSignedPaymentClosed : Bool
round623SelfSignedPaymentClosed = false

round623ExternalSignedPaymentClosed : Bool
round623ExternalSignedPaymentClosed = false

round623SignedNestedRowSelfExternalSplitClosedIsTrue :
  round623SignedNestedRowSelfExternalSplitClosed ≡ true
round623SignedNestedRowSelfExternalSplitClosedIsTrue = refl

round623ExternalRowOnCanonicalOrbitResolvedCarrierIsTrue :
  round623ExternalRowOnCanonicalOrbitResolvedCarrier ≡ true
round623ExternalRowOnCanonicalOrbitResolvedCarrierIsTrue = refl

round623FixedOrbitCorrectionPreservedBeforeHermitianPairingIsTrue :
  round623FixedOrbitCorrectionPreservedBeforeHermitianPairing ≡ true
round623FixedOrbitCorrectionPreservedBeforeHermitianPairingIsTrue = refl

round623IntroducesNormOrAbsoluteValueIsFalse :
  round623IntroducesNormOrAbsoluteValue ≡ false
round623IntroducesNormOrAbsoluteValueIsFalse = refl

round623IntroducesEstimateIsFalse :
  round623IntroducesEstimate ≡ false
round623IntroducesEstimateIsFalse = refl
