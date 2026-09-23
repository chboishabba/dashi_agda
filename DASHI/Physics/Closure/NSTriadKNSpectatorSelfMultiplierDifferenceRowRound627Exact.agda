{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNSpectatorSelfMultiplierDifferenceRowRound627Exact where

------------------------------------------------------------------------
-- ROUND627 / SIGNED SPECTATOR SELF ROW ON THE MULTIPLIER-DIFFERENCE FOLD
--
-- R626 rewrites the complete fixed-output self R573 vector fold onto the
-- doubled four-helicity multiplier-difference carrier.  Pairing that equality
-- against the SAME R545 spectator double cell gives the exact signed self row
-- consumed by R623/R624.
--
-- No norm, absolute value, estimate, positivity, or change of test functional
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNSpectatorNestedSelfCanonicalExternalRowRound623Exact as R623
import DASHI.Physics.Closure.NSTriadKNR573SelfMultiplierDifferenceFoldRound626Exact as R626

F = Rational.rationalRealField

module SpectatorSelfMultiplierRow
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
  module SignedRows =
    R623.SignedRowSplit physicalSystem S L H velocityTransverse

  module MultiplierFold (beta : Physical.PhysicalTriadIncidence) =
    R626.SelfMultiplierFold
      (Spec.spectatorWeight beta) S L H system velocityTransverse

  selfMultiplierNestedForcingRow :
    Z3.FourierMode →
    Physical.PhysicalTriadIncidence → ℚ
  selfMultiplierNestedForcingRow output beta =
    let module M = MultiplierFold beta in
    R179.realHermitianCross
      (M.selfMultiplierNestedFold output)
      (Row.doubleCell beta)

  selfNestedForcingRowIsMultiplierDifference :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    SignedRows.selfNestedForcingRow output beta
    ≡ selfMultiplierNestedForcingRow output beta
  selfNestedForcingRowIsMultiplierDifference output beta =
    let module M = MultiplierFold beta in
    cong
      (λ value →
        R179.realHermitianCross value (Row.doubleCell beta))
      (M.fixedOutputSelfNestedFoldIsMultiplierDifference output)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round627SignedSelfSpectatorRowMultiplierDifferenceWeldClosed : Bool
round627SignedSelfSpectatorRowMultiplierDifferenceWeldClosed = true

round627SameHermitianTestPreserved : Bool
round627SameHermitianTestPreserved = true

round627IntroducesEstimate : Bool
round627IntroducesEstimate = false

round627SelfSignedPaymentClosed : Bool
round627SelfSignedPaymentClosed = false

round627SignedSelfSpectatorRowMultiplierDifferenceWeldClosedIsTrue :
  round627SignedSelfSpectatorRowMultiplierDifferenceWeldClosed ≡ true
round627SignedSelfSpectatorRowMultiplierDifferenceWeldClosedIsTrue = refl

round627SameHermitianTestPreservedIsTrue :
  round627SameHermitianTestPreserved ≡ true
round627SameHermitianTestPreservedIsTrue = refl

round627IntroducesEstimateIsFalse :
  round627IntroducesEstimate ≡ false
round627IntroducesEstimateIsFalse = refl

round627SelfSignedPaymentClosedIsFalse :
  round627SelfSignedPaymentClosed ≡ false
round627SelfSignedPaymentClosedIsFalse = refl
