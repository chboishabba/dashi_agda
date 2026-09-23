{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCanonicalExternalTotalCommutatorScalarRound631Exact where

------------------------------------------------------------------------
-- ROUND631 / CANONICAL ORBIT-RESOLVED EXTERNAL SCALAR ON TOTAL COMMUTATOR
--
-- R622 proves that the complete fixed-output external R573 fold is the
-- canonical orbit-resolved external fold.
--
-- R630 proves pointwise, including the p = 0 branch, that the SAME external
-- R573 nested cell is the total weighted doubled external commutator cell.
--
-- Therefore the canonical external fold is exactly the complete fold of the
-- total external commutator carrier.  Pushing that vector equality through
-- the unchanged Hermitian test gives the scalar consumer used downstream.
--
-- No norm, absolute value, estimate, shell decomposition, spacetime
-- integration, or PDE inequality is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedExternalNestedFoldRound622Exact as R622
import DASHI.Physics.Closure.NSTriadKNExternalWeightedSlotCommutatorTotalRound630Exact as R630

module CanonicalExternalTotalCommutator631
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Canonical =
    R622.CanonicalExternalNested W S L H system velocityTransverse

  module Total =
    R630.TotalExternalCommutator630 W S L H system velocityTransverse

  fibre :
    Z3.FourierMode →
    List Physical.PhysicalTriadIncidence
  fibre = Canonical.fibre

  totalExternalCommutatorFold :
    Z3.FourierMode → C3.Complex3 F
  totalExternalCommutatorFold output =
    R224.foldVector
      Total.totalExternalNestedCommutator
      (fibre output)

  externalFoldIsTotalCommutatorFold :
    (output : Z3.FourierMode) →
    R224.foldVector
      Canonical.Split.externalNestedWeightedCompanionCell
      (fibre output)
    ≡ totalExternalCommutatorFold output
  externalFoldIsTotalCommutatorFold output =
    foldPointwise
      (fibre output)
    where
    foldPointwise :
      (items : List Physical.PhysicalTriadIncidence) →
      R224.foldVector
        Canonical.Split.externalNestedWeightedCompanionCell
        items
      ≡
      R224.foldVector
        Total.totalExternalNestedCommutator
        items
    foldPointwise [] = refl
    foldPointwise (tau ∷ rest) =
      cong₂ C3.complex3Add
        (Total.externalNestedWeightedCompanionIsTotalCommutator tau)
        (foldPointwise rest)

  canonicalExternalFoldIsTotalCommutator :
    (output : Z3.FourierMode) →
    Canonical.canonicalExternalNestedFold output
    ≡ totalExternalCommutatorFold output
  canonicalExternalFoldIsTotalCommutator output =
    trans
      (sym (Canonical.fixedOutputExternalNestedFoldIsCanonical output))
      (externalFoldIsTotalCommutatorFold output)

  canonicalExternalScalar :
    Z3.FourierMode →
    C3.Complex3 F → ℚ
  canonicalExternalScalar output test =
    R179.realHermitianCross
      (Canonical.canonicalExternalNestedFold output)
      test

  totalExternalCommutatorScalar :
    Z3.FourierMode →
    C3.Complex3 F → ℚ
  totalExternalCommutatorScalar output test =
    R179.realHermitianCross
      (totalExternalCommutatorFold output)
      test

  canonicalExternalScalarIsTotalCommutatorScalar :
    (output : Z3.FourierMode) →
    (test : C3.Complex3 F) →
    canonicalExternalScalar output test
    ≡ totalExternalCommutatorScalar output test
  canonicalExternalScalarIsTotalCommutatorScalar output test =
    cong
      (λ force → R179.realHermitianCross force test)
      (canonicalExternalFoldIsTotalCommutator output)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round631CanonicalExternalFoldOnTotalCommutatorClosed : Bool
round631CanonicalExternalFoldOnTotalCommutatorClosed = true

round631CanonicalExternalScalarOnTotalCommutatorClosed : Bool
round631CanonicalExternalScalarOnTotalCommutatorClosed = true

round631ZeroPBranchIncluded : Bool
round631ZeroPBranchIncluded = true

round631RequiresLegacyR112WitnessFamily : Bool
round631RequiresLegacyR112WitnessFamily = false

round631IntroducesEstimate : Bool
round631IntroducesEstimate = false

round631ExternalSignedPaymentClosed : Bool
round631ExternalSignedPaymentClosed = false

round631CanonicalExternalFoldOnTotalCommutatorClosedIsTrue :
  round631CanonicalExternalFoldOnTotalCommutatorClosed ≡ true
round631CanonicalExternalFoldOnTotalCommutatorClosedIsTrue = refl

round631CanonicalExternalScalarOnTotalCommutatorClosedIsTrue :
  round631CanonicalExternalScalarOnTotalCommutatorClosed ≡ true
round631CanonicalExternalScalarOnTotalCommutatorClosedIsTrue = refl

round631ZeroPBranchIncludedIsTrue :
  round631ZeroPBranchIncluded ≡ true
round631ZeroPBranchIncludedIsTrue = refl

round631RequiresLegacyR112WitnessFamilyIsFalse :
  round631RequiresLegacyR112WitnessFamily ≡ false
round631RequiresLegacyR112WitnessFamilyIsFalse = refl

round631IntroducesEstimateIsFalse :
  round631IntroducesEstimate ≡ false
round631IntroducesEstimateIsFalse = refl

round631ExternalSignedPaymentClosedIsFalse :
  round631ExternalSignedPaymentClosed ≡ false
round631ExternalSignedPaymentClosedIsFalse = refl
