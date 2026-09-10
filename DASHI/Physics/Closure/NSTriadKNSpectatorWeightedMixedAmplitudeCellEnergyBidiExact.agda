module DASHI.Physics.Closure.NSTriadKNSpectatorWeightedMixedAmplitudeCellEnergyBidiExact where

------------------------------------------------------------------------
-- SPECTATOR-WEIGHTED MIXED AMPLITUDE CELL -> WEIGHT^2 * MODAL ENERGY PRODUCT
--
-- This is a same-object specialization of the existing R440/R544 amplitude
-- carrier.  Reuse:
--   * MixedHelicityCellEnergyProductBidiExact for
--       ||u_p+ x u_q-||^2 <= ||u_p||^2 ||u_q||^2;
--   * R174 scalar norm scaling;
--   * R455 |realEmbed w|^2 = w^2;
--   * R541 literal spectator resolvent meaning.
--
-- No finite-fibre aggregation or cutoff-uniform estimate is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base using (ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleCellAmplitudeFoldRound544Exact as R544
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as R455
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCellEnergyProductBidiExact as Mixed

F : C3.RealField _
F = Rational.rationalRealField

module SpectatorWeightedAmplitudeCell
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocity system

  module Spec = R541.Spectator physicalSystem S
  module Amp (beta : Physical.PhysicalTriadIncidence) =
    R544.Fold physicalSystem S (Spec.spectatorWeight beta)

  weightedMixedAmplitudeCellBelowEnergy :
    (beta alpha : Physical.PhysicalTriadIncidence) →
    L2.complex3NormSquared (Amp.amplitude beta alpha)
    ≤
    (Spec.Swap.pairResolvent alpha beta * Spec.Swap.pairResolvent alpha beta)
      * (L2.complex3NormSquared (velocity (Physical.p alpha))
        * L2.complex3NormSquared (velocity (Physical.q alpha)))
  weightedMixedAmplitudeCellBelowEnergy beta alpha =
    let
      w = Spec.Swap.pairResolvent alpha beta
      mixed = Amp.D.Pair.mixedCell alpha
      cellBound =
        Mixed.mixedPlusMinusCellBelowEnergyProduct
          E I S L velocity velocityTransverse alpha
      scaleMeaning = R174.normScale (C3.realEmbed F w) mixed
      modulusMeaning = R455.realEmbedModulusSquared w
      exactScale :
        L2.complex3NormSquared
          (C3.complex3Scale (C3.realEmbed F w) mixed)
        ≡ (w * w) * L2.complex3NormSquared mixed
      exactScale =
        trans scaleMeaning
          (cong (_* L2.complex3NormSquared mixed) modulusMeaning)
      wSquareNN = Rational.squareNonnegative w
      scaled =
        let instance wNN = nonNegative wSquareNN
        in ℚP.*-monoˡ-≤-nonNeg (w * w) cellBound
      weightSameObject = Spec.spectatorWeightMeaning beta alpha
    in
    subst
      (λ selectedWeight →
        L2.complex3NormSquared
          (C3.complex3Scale selectedWeight mixed)
        ≤ (w * w)
            * (L2.complex3NormSquared (velocity (Physical.p alpha))
              * L2.complex3NormSquared (velocity (Physical.q alpha))))
      (sym weightSameObject)
      (subst
        (λ lower → lower ≤
          (w * w)
            * (L2.complex3NormSquared (velocity (Physical.p alpha))
              * L2.complex3NormSquared (velocity (Physical.q alpha))))
        (sym exactScale)
        scaled)

spectatorWeightedMixedAmplitudeCellBoundClosed : Bool
spectatorWeightedMixedAmplitudeCellBoundClosed = true

spectatorWeightedMixedAmplitudeAggregateUniformityClosed : Bool
spectatorWeightedMixedAmplitudeAggregateUniformityClosed = false

clayPromotion : Bool
clayPromotion = false
