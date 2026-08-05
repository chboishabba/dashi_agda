module DASHI.Physics.YangMills.BalabanClayCoupledRGInvariantConeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Mir Faizal and Arshid Shabir,
-- "Reflection-Positive Construction of a Four-Dimensional SU(N) Yang-Mills
-- Theory with Mass Gap and Confinement", arXiv:2606.19362v1, 2026.
-- No DOI identified in version 1.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Prove the scalar invariant-cone mechanism for a genuinely coupled RG step.
-- The cone is
--
--   K <= eta g^2.
--
-- The polymer step may contain its own quadratic term,
--
--   K' <= theta K + c1 g^2 + cK K^2,
--
-- while the coupling step contains gK and K^2 remainders through the imported
-- coupled-flow theorem.  If g' retains at least alpha g and
--
--   theta eta + c1 + cK eta^2 g^2 <= eta alpha^2,
--
-- then exact ordered-field algebra proves
--
--   K' <= eta (g')^2.
--
-- Thus the separation of the polymer and coupling equations is not a hidden
-- decoupling assumption: the mixed terms are controlled by one explicit cone
-- and one auditable scalar budget.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCoupledPolymerFlowRemainderExact as Flow

productNonnegative : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
productNonnegative left right leftNonnegative rightNonnegative =
  let
    instance
      leftNN : NonNegative left
      leftNN = ℚ.nonNegative leftNonnegative
      rightNN : NonNegative right
      rightNN = ℚ.nonNegative rightNonnegative
  in ℚP.nonNegative⁻¹ (left * right)

squareMonotoneNonnegative : ∀ lower upper →
  0ℚ ≤ lower →
  lower ≤ upper →
  lower * lower ≤ upper * upper
squareMonotoneNonnegative lower upper lowerNonnegative lower≤upper =
  let
    upperNonnegative = ℚP.≤-trans lowerNonnegative lower≤upper
    first =
      let
        instance
          lowerNN : NonNegative lower
          lowerNN = ℚ.nonNegative lowerNonnegative
      in ℚP.*-monoʳ-≤-nonNeg lower lower≤upper
    second =
      let
        instance
          upperNN : NonNegative upper
          upperNN = ℚ.nonNegative upperNonnegative
      in ℚP.*-monoˡ-≤-nonNeg upper lower≤upper
  in ℚP.≤-trans first second

record CoupledRGInvariantConeStep : Set₁ where
  field
    flow : Flow.CoupledPolymerFlowStep

    nextPolymerNorm theta polymerSource polymerQuadratic retention : ℚ

    nextPolymerNonnegative : 0ℚ ≤ nextPolymerNorm
    thetaNonnegative : 0ℚ ≤ theta
    polymerSourceNonnegative : 0ℚ ≤ polymerSource
    polymerQuadraticNonnegative : 0ℚ ≤ polymerQuadratic
    retentionNonnegative : 0ℚ ≤ retention

    polymerStepUpper :
      nextPolymerNorm
      ≤ theta * Flow.polymerNorm flow
        + (polymerSource * Flow.square (Flow.coupling flow)
          + polymerQuadratic * Flow.square (Flow.polymerNorm flow))

    retentionBelowOneLoopLowerFactor :
      retention
      ≤ (+ 1 / 1)
        - (+ 3 / 2) * Flow.beta flow
          * Flow.square (Flow.coupling flow)

    coneBudget :
      theta * Flow.coneSlope flow
      + (polymerSource
        + polymerQuadratic * Flow.square (Flow.coneSlope flow)
          * Flow.square (Flow.coupling flow))
      ≤ Flow.coneSlope flow * Flow.square retention

open CoupledRGInvariantConeStep public

retainedCoupling : CoupledRGInvariantConeStep → ℚ
retainedCoupling dataSet =
  retention dataSet * Flow.coupling (flow dataSet)

retainedCouplingNonnegative :
  (dataSet : CoupledRGInvariantConeStep) →
  0ℚ ≤ retainedCoupling dataSet
retainedCouplingNonnegative dataSet =
  productNonnegative
    (retention dataSet)
    (Flow.coupling (flow dataSet))
    (retentionNonnegative dataSet)
    (Flow.couplingNonnegative (flow dataSet))

coupledLowerEnvelopeBelowNext :
  (dataSet : CoupledRGInvariantConeStep) →
  Flow.coupledLowerEnvelope (flow dataSet)
  ≤ Flow.nextCoupling (flow dataSet)
coupledLowerEnvelopeBelowNext dataSet =
  subst
    (λ right →
      Flow.coupledLowerEnvelope (flow dataSet) ≤ right)
    (sym (Flow.flowEquation (flow dataSet)))
    (subst
      (λ lower → lower
        ≤ Flow.coupling (flow dataSet)
          - Flow.beta (flow dataSet)
            * Flow.cube (Flow.coupling (flow dataSet))
          + Flow.remainder (flow dataSet))
      (sym (Flow.coupledLowerEnvelopeExpansion (flow dataSet)))
      (ℚP.+-monoˡ-≤
        (Flow.coupling (flow dataSet)
          - Flow.beta (flow dataSet)
            * Flow.cube (Flow.coupling (flow dataSet)))
        (Flow.minusHalfBetaCubeBelowRemainder (flow dataSet))))

retainedCouplingBelowLowerEnvelope :
  (dataSet : CoupledRGInvariantConeStep) →
  retainedCoupling dataSet
  ≤ Flow.coupledLowerEnvelope (flow dataSet)
retainedCouplingBelowLowerEnvelope dataSet =
  let
    instance
      couplingNN : NonNegative (Flow.coupling (flow dataSet))
      couplingNN = ℚ.nonNegative
        (Flow.couplingNonnegative (flow dataSet))
  in
  subst
    (λ upper → retainedCoupling dataSet ≤ upper)
    (ℚRing.solve-∀
      (Flow.coupling (flow dataSet))
      (Flow.beta (flow dataSet)))
    (ℚP.*-monoʳ-≤-nonNeg
      (Flow.coupling (flow dataSet))
      (retentionBelowOneLoopLowerFactor dataSet))

retainedCouplingBelowNext :
  (dataSet : CoupledRGInvariantConeStep) →
  retainedCoupling dataSet
  ≤ Flow.nextCoupling (flow dataSet)
retainedCouplingBelowNext dataSet =
  ℚP.≤-trans
    (retainedCouplingBelowLowerEnvelope dataSet)
    (coupledLowerEnvelopeBelowNext dataSet)

retainedSquareBelowNextSquare :
  (dataSet : CoupledRGInvariantConeStep) →
  Flow.square (retainedCoupling dataSet)
  ≤ Flow.square (Flow.nextCoupling (flow dataSet))
retainedSquareBelowNextSquare dataSet =
  squareMonotoneNonnegative
    (retainedCoupling dataSet)
    (Flow.nextCoupling (flow dataSet))
    (retainedCouplingNonnegative dataSet)
    (retainedCouplingBelowNext dataSet)

polymerLinearBelowCone :
  (dataSet : CoupledRGInvariantConeStep) →
  theta dataSet * Flow.polymerNorm (flow dataSet)
  ≤ (theta dataSet * Flow.coneSlope (flow dataSet))
    * Flow.square (Flow.coupling (flow dataSet))
polymerLinearBelowCone dataSet =
  let
    instance
      thetaNN : NonNegative (theta dataSet)
      thetaNN = ℚ.nonNegative (thetaNonnegative dataSet)
  in
  subst
    (λ upper →
      theta dataSet * Flow.polymerNorm (flow dataSet) ≤ upper)
    (ℚRing.solve-∀
      (theta dataSet)
      (Flow.coneSlope (flow dataSet))
      (Flow.coupling (flow dataSet)))
    (ℚP.*-monoˡ-≤-nonNeg
      (theta dataSet) (Flow.polymerCone (flow dataSet)))

polymerQuadraticBelowCone :
  (dataSet : CoupledRGInvariantConeStep) →
  polymerQuadratic dataSet
    * Flow.square (Flow.polymerNorm (flow dataSet))
  ≤ (polymerQuadratic dataSet
      * Flow.square (Flow.coneSlope (flow dataSet))
      * Flow.square (Flow.coupling (flow dataSet)))
    * Flow.square (Flow.coupling (flow dataSet))
polymerQuadraticBelowCone dataSet =
  let
    instance
      coefficientNN : NonNegative (polymerQuadratic dataSet)
      coefficientNN = ℚ.nonNegative
        (polymerQuadraticNonnegative dataSet)
  in
  subst
    (λ upper →
      polymerQuadratic dataSet
        * Flow.square (Flow.polymerNorm (flow dataSet))
      ≤ upper)
    (ℚRing.solve-∀
      (polymerQuadratic dataSet)
      (Flow.coneSlope (flow dataSet))
      (Flow.coupling (flow dataSet)))
    (ℚP.*-monoˡ-≤-nonNeg
      (polymerQuadratic dataSet)
      (Flow.polymerSquareBelowConeFourth (flow dataSet)))

nextPolymerBelowConeCoefficient :
  (dataSet : CoupledRGInvariantConeStep) →
  nextPolymerNorm dataSet
  ≤ (theta dataSet * Flow.coneSlope (flow dataSet)
      + (polymerSource dataSet
        + polymerQuadratic dataSet
          * Flow.square (Flow.coneSlope (flow dataSet))
          * Flow.square (Flow.coupling (flow dataSet))))
    * Flow.square (Flow.coupling (flow dataSet))
nextPolymerBelowConeCoefficient dataSet =
  ℚP.≤-trans
    (polymerStepUpper dataSet)
    (subst
      (λ upper →
        theta dataSet * Flow.polymerNorm (flow dataSet)
        + (polymerSource dataSet
            * Flow.square (Flow.coupling (flow dataSet))
          + polymerQuadratic dataSet
            * Flow.square (Flow.polymerNorm (flow dataSet)))
        ≤ upper)
      (ℚRing.solve-∀
        (theta dataSet)
        (polymerSource dataSet)
        (polymerQuadratic dataSet)
        (Flow.coneSlope (flow dataSet))
        (Flow.coupling (flow dataSet)))
      (ℚP.+-mono-≤
        (polymerLinearBelowCone dataSet)
        (ℚP.+-mono-≤
          ℚP.≤-refl
          (polymerQuadraticBelowCone dataSet))))

nextPolymerBelowRetainedCone :
  (dataSet : CoupledRGInvariantConeStep) →
  nextPolymerNorm dataSet
  ≤ Flow.coneSlope (flow dataSet)
    * Flow.square (retainedCoupling dataSet)
nextPolymerBelowRetainedCone dataSet =
  ℚP.≤-trans
    (nextPolymerBelowConeCoefficient dataSet)
    (let
      instance
        couplingSquareNN : NonNegative
          (Flow.square (Flow.coupling (flow dataSet)))
        couplingSquareNN = ℚ.nonNegative
          (Flow.squareNonnegative
            (Flow.coupling (flow dataSet))
            (Flow.couplingNonnegative (flow dataSet)))
     in
     subst
       (λ upper →
         (theta dataSet * Flow.coneSlope (flow dataSet)
          + (polymerSource dataSet
            + polymerQuadratic dataSet
              * Flow.square (Flow.coneSlope (flow dataSet))
              * Flow.square (Flow.coupling (flow dataSet))))
         * Flow.square (Flow.coupling (flow dataSet))
         ≤ upper)
       (ℚRing.solve-∀
         (Flow.coneSlope (flow dataSet))
         (retention dataSet)
         (Flow.coupling (flow dataSet)))
       (ℚP.*-monoʳ-≤-nonNeg
         (Flow.square (Flow.coupling (flow dataSet)))
         (coneBudget dataSet)))

coupledInvariantConePreserved :
  (dataSet : CoupledRGInvariantConeStep) →
  nextPolymerNorm dataSet
  ≤ Flow.coneSlope (flow dataSet)
    * Flow.square (Flow.nextCoupling (flow dataSet))
coupledInvariantConePreserved dataSet =
  ℚP.≤-trans
    (nextPolymerBelowRetainedCone dataSet)
    (let
      instance
        coneSlopeNN : NonNegative (Flow.coneSlope (flow dataSet))
        coneSlopeNN = ℚ.nonNegative
          (Flow.coneSlopeNonnegative (flow dataSet))
     in ℚP.*-monoˡ-≤-nonNeg
          (Flow.coneSlope (flow dataSet))
          (retainedSquareBelowNextSquare dataSet))

coupledRGRetentionLevel : ProofLevel
coupledRGRetentionLevel = machineChecked

coupledPolymerConeReductionLevel : ProofLevel
coupledPolymerConeReductionLevel = machineChecked

coupledInvariantConeClosureLevel : ProofLevel
coupledInvariantConeClosureLevel = machineChecked

physicalCoupledMacrostepProducerLevel : ProofLevel
physicalCoupledMacrostepProducerLevel = conditional
