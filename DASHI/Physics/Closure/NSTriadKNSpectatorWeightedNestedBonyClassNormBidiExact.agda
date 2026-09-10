module DASHI.Physics.Closure.NSTriadKNSpectatorWeightedNestedBonyClassNormBidiExact where

------------------------------------------------------------------------
-- SPECTATOR RESOLVENT x R584 LIVE NESTED BONY CLASS-NORM BIDI
--
-- R584 is generic in an R294 swap-invariant outer weight and already places
-- the remaining class-norm payments on R573's actual nested slot-transformed
-- cells.  R541 supplies the literal fixed-spectator Cauchy resolvent weight
--
--   W_beta(alpha) = 1 / (lambda_alpha + lambda_beta).
--
-- This module performs only that missing specialization.  It introduces no
-- estimate and no new norm architecture.  Consequently the remaining analytic
-- debt is no longer "instantiate the outer weight"; it is the genuinely
-- quantitative cutoff-uniform spectator-weighted class-norm / spacetime bound
-- needed downstream by R503.
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
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact as R584

F : C3.RealField _
F = Rational.rationalRealField

module SpectatorWeightedNestedBony
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

  module Spec = R541.Spectator physicalSystem S

  system = Field30.finiteSystem physicalSystem

  -- The complete R584 live nested-slot class-norm carrier, now instantiated
  -- with the literal R541 spectator resolvent weight.
  module Live (beta : Physical.PhysicalTriadIncidence) =
    R584.LiveNestedSlot584
      {E = Field30.physicalEmbedding physicalSystem}
      {I = Field30.physicalInverseSquare physicalSystem}
      (Spec.spectatorWeight beta)
      S L H system velocityTransverse

  -- Preserve the same-object meaning of the instantiated outer weight.
  spectatorOuterWeightIsLiteralResolvent :
    (beta alpha : Physical.PhysicalTriadIncidence) →
    R294.weight (Spec.spectatorWeight beta) alpha
    ≡ C3.realEmbed F (Spec.Swap.pairResolvent alpha beta)
  spectatorOuterWeightIsLiteralResolvent beta alpha =
    Spec.spectatorWeightMeaning beta alpha

------------------------------------------------------------------------
-- Status / firewall.
------------------------------------------------------------------------

spectatorOuterWeightInstantiatedIntoLiveR584 : Bool
spectatorOuterWeightInstantiatedIntoLiveR584 = true

spectatorWeightStillAbstractAfterThisWeld : Bool
spectatorWeightStillAbstractAfterThisWeld = false

spectatorWeightedClassNormPaymentsConstructed : Bool
spectatorWeightedClassNormPaymentsConstructed = false

cutoffUniformSpectatorWeightedSpacetimeEnvelopeClosed : Bool
cutoffUniformSpectatorWeightedSpacetimeEnvelopeClosed = false

r503PaidByThisStructuralWeldAlone : Bool
r503PaidByThisStructuralWeldAlone = false

clayPromotion : Bool
clayPromotion = false

spectatorOuterWeightInstantiatedIntoLiveR584IsTrue :
  spectatorOuterWeightInstantiatedIntoLiveR584 ≡ true
spectatorOuterWeightInstantiatedIntoLiveR584IsTrue = refl

cutoffUniformSpectatorWeightedSpacetimeEnvelopeClosedIsFalse :
  cutoffUniformSpectatorWeightedSpacetimeEnvelopeClosed ≡ false
cutoffUniformSpectatorWeightedSpacetimeEnvelopeClosedIsFalse = refl

r503PaidByThisStructuralWeldAloneIsFalse :
  r503PaidByThisStructuralWeldAlone ≡ false
r503PaidByThisStructuralWeldAloneIsFalse = refl
