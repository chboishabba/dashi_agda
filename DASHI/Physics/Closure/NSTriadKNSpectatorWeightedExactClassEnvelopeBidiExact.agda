module DASHI.Physics.Closure.NSTriadKNSpectatorWeightedExactClassEnvelopeBidiExact where

------------------------------------------------------------------------
-- EXACT LIVE SPECTATOR-WEIGHTED FOUR-CLASS ENVELOPE
--
-- The R582 budget existence layer is compiler-owned: exact self ceilings always
-- inhabit it.  Therefore expose the actual finite object whose useful uniform
-- control is the remaining analytic task.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_; _*_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNDirectBonyClassNormCompilerRound583Exact as R583
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedNestedBonyClassNormBidiExact as SpectatorBony
import DASHI.Physics.Closure.NSTriadKNExactBonyClassNormSelfBudgetBidiExact as SelfBudget

F : C3.RealField _
F = Rational.rationalRealField

module ExactEnvelope
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

    exactClassBudgets :
      (tau : Physical.PhysicalTriadIncidence) →
      Live.NestedSlotClassNormPayment584 tau
    exactClassBudgets tau =
      Live.nested-slot-class-norm-payment-584
        (SelfBudget.exactFourBonyClassSelfBudgets
          (Live.nestedSlotCells584 tau))

    exactFourClassEnvelope :
      Physical.PhysicalTriadIncidence → ℚ
    exactFourClassEnvelope tau =
      R583.fourClassNormEnvelope583
        (Live.nestedSlotCells584 tau)
        (Live.budgets584 (exactClassBudgets tau))

    nestedSlotBelowExactFourClassEnvelope :
      (tau : Physical.PhysicalTriadIncidence) →
      L2.complex3NormSquared (Live.Weighted.nestedSlotFold tau)
      ≤ R576.four * exactFourClassEnvelope tau
    nestedSlotBelowExactFourClassEnvelope tau =
      Live.nestedSlotFoldBelowClassNorms584 tau (exactClassBudgets tau)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

exactSpectatorFourClassEnvelopeExposed : Bool
exactSpectatorFourClassEnvelopeExposed = true

arbitraryClassBudgetChoiceStillOnCriticalPath : Bool
arbitraryClassBudgetChoiceStillOnCriticalPath = false

cutoffUniformUpperForExactEnvelopeClosed : Bool
cutoffUniformUpperForExactEnvelopeClosed = false

spacetimeUpperForExactEnvelopeClosed : Bool
spacetimeUpperForExactEnvelopeClosed = false

r503ClosedHere : Bool
r503ClosedHere = false

exactSpectatorFourClassEnvelopeExposedIsTrue :
  exactSpectatorFourClassEnvelopeExposed ≡ true
exactSpectatorFourClassEnvelopeExposedIsTrue = refl

arbitraryClassBudgetChoiceStillOnCriticalPathIsFalse :
  arbitraryClassBudgetChoiceStillOnCriticalPath ≡ false
arbitraryClassBudgetChoiceStillOnCriticalPathIsFalse = refl

r503ClosedHereIsFalse : r503ClosedHere ≡ false
r503ClosedHereIsFalse = refl
