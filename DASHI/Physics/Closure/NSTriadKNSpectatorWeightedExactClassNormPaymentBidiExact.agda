module DASHI.Physics.Closure.NSTriadKNSpectatorWeightedExactClassNormPaymentBidiExact where

------------------------------------------------------------------------
-- COMPILE EXACT SELF-BUDGETS INTO THE LIVE R541 x R584 SPECTATOR CARRIER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedNestedBonyClassNormBidiExact as SpectatorBony
import DASHI.Physics.Closure.NSTriadKNExactBonyClassNormSelfBudgetBidiExact as SelfBudget

F : C3.RealField _
F = Rational.rationalRealField

module LiveExactClassPayments
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

  module SB = SpectatorBony.SpectatorWeightedNestedBony
    physicalSystem S L H velocityTransverse

  module AtSpectator (beta : Physical.PhysicalTriadIncidence) where
    module Live = SB.Live beta

    exactNestedSlotClassNormPayment :
      (tau : Physical.PhysicalTriadIncidence) →
      Live.NestedSlotClassNormPayment584 tau
    exactNestedSlotClassNormPayment tau =
      Live.nested-slot-class-norm-payment-584
        (SelfBudget.exactFourBonyClassSelfBudgets
          (Live.nestedSlotCells584 tau))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

liveR584ClassNormPaymentExistenceClosed : Bool
liveR584ClassNormPaymentExistenceClosed = true

uniformUpperOnExactClassNormEnvelopeClosed : Bool
uniformUpperOnExactClassNormEnvelopeClosed = false

spacetimeTransportOfExactClassNormEnvelopeClosed : Bool
spacetimeTransportOfExactClassNormEnvelopeClosed = false

r503ClosedHere : Bool
r503ClosedHere = false

liveR584ClassNormPaymentExistenceClosedIsTrue :
  liveR584ClassNormPaymentExistenceClosed ≡ true
liveR584ClassNormPaymentExistenceClosedIsTrue = refl

uniformUpperOnExactClassNormEnvelopeClosedIsFalse :
  uniformUpperOnExactClassNormEnvelopeClosed ≡ false
uniformUpperOnExactClassNormEnvelopeClosedIsFalse = refl

r503ClosedHereIsFalse : r503ClosedHere ≡ false
r503ClosedHereIsFalse = refl
