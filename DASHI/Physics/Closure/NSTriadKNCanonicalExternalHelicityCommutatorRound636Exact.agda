{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCanonicalExternalHelicityCommutatorRound636Exact where

------------------------------------------------------------------------
-- ROUND636 / CANONICAL EXTERNAL SCALAR = TOTAL HELICITY COMMUTATOR SCALAR
--
-- R629/R630 place the total external R573 nested cell on the doubled external
-- R230 commutator carrier, including the p = 0 branch.
--
-- R306 proves, on the SAME forcing/velocity slots,
--
--   doubleR230Cell
--     = helicityCommutatorCell
--
-- where the right side is the literal normalized-helicity commutator
--
--   (H N_p^ext) x u_q - N_p^ext x (H u_q)
--
-- in projector coordinates.
--
-- This owner composes those same-object identities and lifts them through the
-- complete fixed-output fold and R631's canonical Hermitian scalar consumer.
-- No norm, absolute value, estimate, shell split, spacetime integration, or
-- PDE inequality is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNForcingHelicityCommutatorRound306Exact as R306
import DASHI.Physics.Closure.NSTriadKNExternalWeightedSlotCommutatorRound629Exact as R629
import DASHI.Physics.Closure.NSTriadKNExternalWeightedSlotCommutatorTotalRound630Exact as R630
import DASHI.Physics.Closure.NSTriadKNCanonicalExternalTotalCommutatorScalarRound631Exact as R631

F : C3.RealField _
F = Rational.rationalRealField

module CanonicalExternalHelicity636
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Comm =
    R629.ExternalSlotCommutator629 W S L H system velocityTransverse

  module Total =
    R630.TotalExternalCommutator630 W S L H system velocityTransverse

  module Canonical =
    R631.CanonicalExternalTotalCommutator631
      E I W S L H system velocityTransverse

  velocity = Audit.velocity system

  totalExternalHelicityExhaustive :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  totalExternalHelicityExhaustive tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false =
    C3.complex3Scale (R294.weight W tau)
      (R306.helicityCommutatorCell
        S velocity (Comm.externalForcingFunction tau) tau)

  totalExternalExhaustiveIsHelicityCommutator :
    (tau : Physical.PhysicalTriadIncidence) →
    Total.totalExternalExhaustiveCommutator tau
    ≡ totalExternalHelicityExhaustive tau
  totalExternalExhaustiveIsHelicityCommutator tau
      with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = refl
  ... | false =
    trans
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (sym (Comm.externalDoubleCommutatorIsDoubleExternalCell tau)))
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (R306.doubleR230CellIsHelicityCommutator
          S velocity (Comm.externalForcingFunction tau) tau))

  totalExternalHelicityNested :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  totalExternalHelicityNested tau =
    C3.complex3Add
      (totalExternalHelicityExhaustive tau)
      (totalExternalHelicityExhaustive tau)

  totalExternalNestedIsHelicityCommutator :
    (tau : Physical.PhysicalTriadIncidence) →
    Total.totalExternalNestedCommutator tau
    ≡ totalExternalHelicityNested tau
  totalExternalNestedIsHelicityCommutator tau =
    cong₂ C3.complex3Add
      (totalExternalExhaustiveIsHelicityCommutator tau)
      (totalExternalExhaustiveIsHelicityCommutator tau)

  fibre :
    Z3.FourierMode → List Physical.PhysicalTriadIncidence
  fibre output =
    Output.physicalOutputFiber (Audit.cutoff system) output

  totalExternalHelicityFold :
    Z3.FourierMode → C3.Complex3 F
  totalExternalHelicityFold output =
    R224.foldVector totalExternalHelicityNested (fibre output)

  totalExternalCommutatorFoldIsHelicityFold :
    (output : Z3.FourierMode) →
    Canonical.totalExternalCommutatorFold output
    ≡ totalExternalHelicityFold output
  totalExternalCommutatorFoldIsHelicityFold output =
    foldPointwise (fibre output)
    where
    foldPointwise :
      (items : List Physical.PhysicalTriadIncidence) →
      R224.foldVector Total.totalExternalNestedCommutator items
      ≡ R224.foldVector totalExternalHelicityNested items
    foldPointwise [] = refl
    foldPointwise (tau ∷ rest) =
      cong₂ C3.complex3Add
        (totalExternalNestedIsHelicityCommutator tau)
        (foldPointwise rest)

  canonicalExternalFoldIsHelicityCommutator :
    (output : Z3.FourierMode) →
    Canonical.Canonical.canonicalExternalNestedFold output
    ≡ totalExternalHelicityFold output
  canonicalExternalFoldIsHelicityCommutator output =
    trans
      (Canonical.canonicalExternalFoldIsTotalCommutator output)
      (totalExternalCommutatorFoldIsHelicityFold output)

  totalExternalHelicityScalar :
    Z3.FourierMode → C3.Complex3 F → ℚ
  totalExternalHelicityScalar output test =
    R179.realHermitianCross
      (totalExternalHelicityFold output)
      test

  canonicalExternalScalarIsHelicityCommutatorScalar :
    (output : Z3.FourierMode) →
    (test : C3.Complex3 F) →
    Canonical.canonicalExternalScalar output test
    ≡ totalExternalHelicityScalar output test
  canonicalExternalScalarIsHelicityCommutatorScalar output test =
    cong
      (λ force → R179.realHermitianCross force test)
      (canonicalExternalFoldIsHelicityCommutator output)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round636ExternalCellOnLiteralHelicityCommutatorClosed : Bool
round636ExternalCellOnLiteralHelicityCommutatorClosed = true

round636CanonicalExternalFoldOnHelicityCommutatorClosed : Bool
round636CanonicalExternalFoldOnHelicityCommutatorClosed = true

round636CanonicalExternalScalarOnHelicityCommutatorClosed : Bool
round636CanonicalExternalScalarOnHelicityCommutatorClosed = true

round636ZeroPBranchPreserved : Bool
round636ZeroPBranchPreserved = true

round636IntroducesEstimate : Bool
round636IntroducesEstimate = false

round636ExternalHelicityCommutatorPaymentClosed : Bool
round636ExternalHelicityCommutatorPaymentClosed = false

round636ExternalCellOnLiteralHelicityCommutatorClosedIsTrue :
  round636ExternalCellOnLiteralHelicityCommutatorClosed ≡ true
round636ExternalCellOnLiteralHelicityCommutatorClosedIsTrue = refl

round636CanonicalExternalFoldOnHelicityCommutatorClosedIsTrue :
  round636CanonicalExternalFoldOnHelicityCommutatorClosed ≡ true
round636CanonicalExternalFoldOnHelicityCommutatorClosedIsTrue = refl

round636CanonicalExternalScalarOnHelicityCommutatorClosedIsTrue :
  round636CanonicalExternalScalarOnHelicityCommutatorClosed ≡ true
round636CanonicalExternalScalarOnHelicityCommutatorClosedIsTrue = refl

round636ZeroPBranchPreservedIsTrue :
  round636ZeroPBranchPreserved ≡ true
round636ZeroPBranchPreservedIsTrue = refl

round636IntroducesEstimateIsFalse :
  round636IntroducesEstimate ≡ false
round636IntroducesEstimateIsFalse = refl

round636ExternalHelicityCommutatorPaymentClosedIsFalse :
  round636ExternalHelicityCommutatorPaymentClosed ≡ false
round636ExternalHelicityCommutatorPaymentClosedIsFalse = refl
