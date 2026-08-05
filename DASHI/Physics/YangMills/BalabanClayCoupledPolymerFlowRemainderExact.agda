module DASHI.Physics.YangMills.BalabanClayCoupledPolymerFlowRemainderExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Mir Faizal and Arshid Shabir,
-- "Reflection-Positive Construction of a Four-Dimensional SU(N) Yang-Mills
-- Theory with Mass Gap and Confinement", arXiv:2606.19362v1, 2026.
-- No DOI identified in version 1.
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories", Physical Review
-- Letters 30 (1973), 1343--1346. DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?", Physical Review
-- Letters 30 (1973), 1346--1349. DOI: 10.1103/PhysRevLett.30.1346.
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
-- Remove the implicit decoupling between the running coupling g and the
-- irrelevant polymer norm K.  The one-step remainder is allowed to have the
-- structurally natural form
--
--   |R(g,K)| <= c5 g^5 + cgK g K + cK2 K^2.
--
-- On the invariant-cone hypothesis K <= eta g^2, exact ordered-field algebra
-- reduces this to
--
--   |R(g,K)|
--     <= (c5 g^2 + cgK eta + cK2 eta^2 g) g^3.
--
-- Consequently, one scalar coefficient condition makes the full coupled
-- remainder no larger than (beta/2)g^3.  The usual ultraviolet one-loop
-- monotonicity and positivity then follow without assuming that K is absent
-- from the coupling flow.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

square cube fourth fifth : ℚ → ℚ
square value = value * value
cube value = square value * value
fourth value = square value * square value
fifth value = fourth value * value

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

squareNonnegative : ∀ value → 0ℚ ≤ value → 0ℚ ≤ square value
squareNonnegative value valueNonnegative =
  productNonnegative value value valueNonnegative valueNonnegative

cubeNonnegative : ∀ value → 0ℚ ≤ value → 0ℚ ≤ cube value
cubeNonnegative value valueNonnegative =
  productNonnegative
    (square value) value
    (squareNonnegative value valueNonnegative)
    valueNonnegative

record CoupledPolymerFlowStep : Set₁ where
  field
    coupling polymerNorm nextCoupling remainder : ℚ
    beta c5 cgK cK2 coneSlope : ℚ

    couplingNonnegative : 0ℚ ≤ coupling
    polymerNormNonnegative : 0ℚ ≤ polymerNorm
    betaNonnegative : 0ℚ ≤ beta
    c5Nonnegative : 0ℚ ≤ c5
    cgKNonnegative : 0ℚ ≤ cgK
    cK2Nonnegative : 0ℚ ≤ cK2
    coneSlopeNonnegative : 0ℚ ≤ coneSlope

    polymerCone : polymerNorm ≤ coneSlope * square coupling

    flowEquation :
      nextCoupling ≡ coupling - beta * cube coupling + remainder

    remainderLower :
      - (c5 * fifth coupling
        + (cgK * coupling * polymerNorm
          + cK2 * square polymerNorm))
      ≤ remainder

    remainderUpper :
      remainder
      ≤ c5 * fifth coupling
        + (cgK * coupling * polymerNorm
          + cK2 * square polymerNorm)

    coupledCoefficientSmall :
      c5 * square coupling
      + (cgK * coneSlope
        + cK2 * square coneSlope * coupling)
      ≤ (+ 1 / 2) * beta

    oneLoopSmall :
      (+ 3 / 2) * beta * square coupling ≤ 1ℚ

open CoupledPolymerFlowStep public

rawCoupledRemainderBudget : CoupledPolymerFlowStep → ℚ
rawCoupledRemainderBudget dataSet =
  c5 dataSet * fifth (coupling dataSet)
  + (cgK dataSet * coupling dataSet * polymerNorm dataSet
    + cK2 dataSet * square (polymerNorm dataSet))

reducedCoupledCoefficient : CoupledPolymerFlowStep → ℚ
reducedCoupledCoefficient dataSet =
  c5 dataSet * square (coupling dataSet)
  + (cgK dataSet * coneSlope dataSet
    + cK2 dataSet * square (coneSlope dataSet) * coupling dataSet)

couplingTimesPolymerBelowConeCube :
  (dataSet : CoupledPolymerFlowStep) →
  coupling dataSet * polymerNorm dataSet
  ≤ coneSlope dataSet * cube (coupling dataSet)
couplingTimesPolymerBelowConeCube dataSet =
  let
    instance
      couplingNN : NonNegative (coupling dataSet)
      couplingNN = ℚ.nonNegative (couplingNonnegative dataSet)
  in
  subst
    (λ upper →
      coupling dataSet * polymerNorm dataSet ≤ upper)
    (ℚRing.solve-∀
      (coneSlope dataSet) (coupling dataSet))
    (ℚP.*-monoˡ-≤-nonNeg
      (coupling dataSet) (polymerCone dataSet))

polymerSquareBelowConeFourth :
  (dataSet : CoupledPolymerFlowStep) →
  square (polymerNorm dataSet)
  ≤ square (coneSlope dataSet) * fourth (coupling dataSet)
polymerSquareBelowConeFourth dataSet =
  let
    coneUpper = coneSlope dataSet * square (coupling dataSet)
    coneUpperNonnegative =
      productNonnegative
        (coneSlope dataSet) (square (coupling dataSet))
        (coneSlopeNonnegative dataSet)
        (squareNonnegative
          (coupling dataSet) (couplingNonnegative dataSet))
    first =
      let
        instance
          polymerNN : NonNegative (polymerNorm dataSet)
          polymerNN = ℚ.nonNegative (polymerNormNonnegative dataSet)
      in ℚP.*-monoʳ-≤-nonNeg
          (polymerNorm dataSet) (polymerCone dataSet)
    second =
      let
        instance
          coneUpperNN : NonNegative coneUpper
          coneUpperNN = ℚ.nonNegative coneUpperNonnegative
      in ℚP.*-monoˡ-≤-nonNeg coneUpper (polymerCone dataSet)
  in
  subst
    (λ upper → square (polymerNorm dataSet) ≤ upper)
    (ℚRing.solve-∀
      (coneSlope dataSet) (coupling dataSet))
    (ℚP.≤-trans first second)

scaledCouplingPolymerBound :
  (dataSet : CoupledPolymerFlowStep) →
  cgK dataSet * coupling dataSet * polymerNorm dataSet
  ≤ (cgK dataSet * coneSlope dataSet) * cube (coupling dataSet)
scaledCouplingPolymerBound dataSet =
  let
    instance
      coefficientNN : NonNegative (cgK dataSet)
      coefficientNN = ℚ.nonNegative (cgKNonnegative dataSet)
  in
  subst
    (λ upper →
      cgK dataSet * coupling dataSet * polymerNorm dataSet ≤ upper)
    (ℚRing.solve-∀
      (cgK dataSet) (coneSlope dataSet) (coupling dataSet))
    (subst
      (λ lower → lower
        ≤ cgK dataSet
          * (coneSlope dataSet * cube (coupling dataSet)))
      (ℚRing.solve-∀
        (cgK dataSet) (coupling dataSet) (polymerNorm dataSet))
      (ℚP.*-monoˡ-≤-nonNeg
        (cgK dataSet)
        (couplingTimesPolymerBelowConeCube dataSet)))

scaledPolymerSquareBound :
  (dataSet : CoupledPolymerFlowStep) →
  cK2 dataSet * square (polymerNorm dataSet)
  ≤ (cK2 dataSet * square (coneSlope dataSet) * coupling dataSet)
      * cube (coupling dataSet)
scaledPolymerSquareBound dataSet =
  let
    instance
      coefficientNN : NonNegative (cK2 dataSet)
      coefficientNN = ℚ.nonNegative (cK2Nonnegative dataSet)
  in
  subst
    (λ upper →
      cK2 dataSet * square (polymerNorm dataSet) ≤ upper)
    (ℚRing.solve-∀
      (cK2 dataSet) (coneSlope dataSet) (coupling dataSet))
    (ℚP.*-monoˡ-≤-nonNeg
      (cK2 dataSet)
      (polymerSquareBelowConeFourth dataSet))

rawBudgetExpansion :
  (dataSet : CoupledPolymerFlowStep) →
  rawCoupledRemainderBudget dataSet
  ≡ (c5 dataSet * square (coupling dataSet))
      * cube (coupling dataSet)
    + (cgK dataSet * coupling dataSet * polymerNorm dataSet
      + cK2 dataSet * square (polymerNorm dataSet))
rawBudgetExpansion dataSet =
  ℚRing.solve-∀
    (c5 dataSet) (cgK dataSet) (cK2 dataSet)
    (coupling dataSet) (polymerNorm dataSet)

reducedCoefficientCubeExpansion :
  (dataSet : CoupledPolymerFlowStep) →
  reducedCoupledCoefficient dataSet * cube (coupling dataSet)
  ≡ (c5 dataSet * square (coupling dataSet))
      * cube (coupling dataSet)
    + ((cgK dataSet * coneSlope dataSet)
        * cube (coupling dataSet)
      + (cK2 dataSet * square (coneSlope dataSet)
          * coupling dataSet)
        * cube (coupling dataSet))
reducedCoefficientCubeExpansion dataSet =
  ℚRing.solve-∀
    (c5 dataSet) (cgK dataSet) (cK2 dataSet)
    (coneSlope dataSet) (coupling dataSet)

rawBudgetBelowReducedCoefficientCube :
  (dataSet : CoupledPolymerFlowStep) →
  rawCoupledRemainderBudget dataSet
  ≤ reducedCoupledCoefficient dataSet * cube (coupling dataSet)
rawBudgetBelowReducedCoefficientCube dataSet =
  subst
    (λ lower →
      lower ≤ reducedCoupledCoefficient dataSet * cube (coupling dataSet))
    (sym (rawBudgetExpansion dataSet))
    (subst
      (λ upper →
        (c5 dataSet * square (coupling dataSet))
          * cube (coupling dataSet)
        + (cgK dataSet * coupling dataSet * polymerNorm dataSet
          + cK2 dataSet * square (polymerNorm dataSet))
        ≤ upper)
      (sym (reducedCoefficientCubeExpansion dataSet))
      (ℚP.+-mono-≤
        ℚP.≤-refl
        (ℚP.+-mono-≤
          (scaledCouplingPolymerBound dataSet)
          (scaledPolymerSquareBound dataSet))))

rawBudgetBelowHalfBetaCube :
  (dataSet : CoupledPolymerFlowStep) →
  rawCoupledRemainderBudget dataSet
  ≤ (+ 1 / 2) * beta dataSet * cube (coupling dataSet)
rawBudgetBelowHalfBetaCube dataSet =
  ℚP.≤-trans
    (rawBudgetBelowReducedCoefficientCube dataSet)
    (let
      instance
        cubeNN : NonNegative (cube (coupling dataSet))
        cubeNN = ℚ.nonNegative
          (cubeNonnegative
            (coupling dataSet) (couplingNonnegative dataSet))
     in ℚP.*-monoʳ-≤-nonNeg
          (cube (coupling dataSet))
          (coupledCoefficientSmall dataSet))

remainderBelowHalfBetaCube :
  (dataSet : CoupledPolymerFlowStep) →
  remainder dataSet
  ≤ (+ 1 / 2) * beta dataSet * cube (coupling dataSet)
remainderBelowHalfBetaCube dataSet =
  ℚP.≤-trans
    (remainderUpper dataSet)
    (rawBudgetBelowHalfBetaCube dataSet)

minusHalfBetaCubeBelowRemainder :
  (dataSet : CoupledPolymerFlowStep) →
  - ((+ 1 / 2) * beta dataSet * cube (coupling dataSet))
  ≤ remainder dataSet
minusHalfBetaCubeBelowRemainder dataSet =
  ℚP.≤-trans
    (ℚP.neg-mono-≤ (rawBudgetBelowHalfBetaCube dataSet))
    (remainderLower dataSet)

halfBetaCubeNonnegative :
  (dataSet : CoupledPolymerFlowStep) →
  0ℚ ≤ (+ 1 / 2) * beta dataSet * cube (coupling dataSet)
halfBetaCubeNonnegative dataSet =
  productNonnegative
    ((+ 1 / 2) * beta dataSet)
    (cube (coupling dataSet))
    (productNonnegative
      (+ 1 / 2) (beta dataSet)
      (ℚP.nonNegative⁻¹ (+ 1 / 2))
      (betaNonnegative dataSet))
    (cubeNonnegative
      (coupling dataSet) (couplingNonnegative dataSet))

subtractNonnegativeBelow : ∀ value loss →
  0ℚ ≤ loss → value - loss ≤ value
subtractNonnegativeBelow value loss lossNonnegative =
  subst
    (λ upper → value + (- loss) ≤ upper)
    (ℚRing.solve-∀ value)
    (ℚP.+-mono-≤
      ℚP.≤-refl
      (subst
        (λ upper → - loss ≤ upper)
        (ℚRing.solve [])
        (ℚP.neg-mono-≤ lossNonnegative)))

nextCouplingBelowCurrent :
  (dataSet : CoupledPolymerFlowStep) →
  nextCoupling dataSet ≤ coupling dataSet
nextCouplingBelowCurrent dataSet =
  subst
    (λ left → left ≤ coupling dataSet)
    (sym (flowEquation dataSet))
    (ℚP.≤-trans
      (ℚP.≤-trans
        (ℚP.+-monoˡ-≤
          (coupling dataSet - beta dataSet * cube (coupling dataSet))
          (remainderBelowHalfBetaCube dataSet))
        (subst
          (λ left → left
            ≤ coupling dataSet
              - ((+ 1 / 2) * beta dataSet
                * cube (coupling dataSet)))
          (ℚRing.solve-∀
            (coupling dataSet)
            (beta dataSet)
            (cube (coupling dataSet)))
          ℚP.≤-refl))
      (subtractNonnegativeBelow
        (coupling dataSet)
        ((+ 1 / 2) * beta dataSet * cube (coupling dataSet))
        (halfBetaCubeNonnegative dataSet)))

oneMinusThreeHalvesBetaSquareNonnegative :
  (dataSet : CoupledPolymerFlowStep) →
  0ℚ ≤ 1ℚ - (+ 3 / 2) * beta dataSet * square (coupling dataSet)
oneMinusThreeHalvesBetaSquareNonnegative dataSet =
  ℚP.p≤q⇒0≤q-p (oneLoopSmall dataSet)

coupledLowerEnvelope : CoupledPolymerFlowStep → ℚ
coupledLowerEnvelope dataSet =
  coupling dataSet
  * (1ℚ - (+ 3 / 2) * beta dataSet * square (coupling dataSet))

coupledLowerEnvelopeNonnegative :
  (dataSet : CoupledPolymerFlowStep) →
  0ℚ ≤ coupledLowerEnvelope dataSet
coupledLowerEnvelopeNonnegative dataSet =
  productNonnegative
    (coupling dataSet)
    (1ℚ - (+ 3 / 2) * beta dataSet * square (coupling dataSet))
    (couplingNonnegative dataSet)
    (oneMinusThreeHalvesBetaSquareNonnegative dataSet)

coupledLowerEnvelopeExpansion :
  (dataSet : CoupledPolymerFlowStep) →
  coupledLowerEnvelope dataSet
  ≡ coupling dataSet - beta dataSet * cube (coupling dataSet)
      + (- ((+ 1 / 2) * beta dataSet * cube (coupling dataSet)))
coupledLowerEnvelopeExpansion dataSet =
  ℚRing.solve-∀ (coupling dataSet) (beta dataSet)

nextCouplingNonnegative :
  (dataSet : CoupledPolymerFlowStep) →
  0ℚ ≤ nextCoupling dataSet
nextCouplingNonnegative dataSet =
  subst
    (λ right → 0ℚ ≤ right)
    (sym (flowEquation dataSet))
    (ℚP.≤-trans
      (coupledLowerEnvelopeNonnegative dataSet)
      (subst
        (λ lower → lower
          ≤ coupling dataSet - beta dataSet * cube (coupling dataSet)
            + remainder dataSet)
        (sym (coupledLowerEnvelopeExpansion dataSet))
        (ℚP.+-monoˡ-≤
          (coupling dataSet - beta dataSet * cube (coupling dataSet))
          (minusHalfBetaCubeBelowRemainder dataSet))))

coupledRemainderConeReductionLevel : ProofLevel
coupledRemainderConeReductionLevel = machineChecked

coupledOneLoopMonotonicityLevel : ProofLevel
coupledOneLoopMonotonicityLevel = machineChecked

coupledOneLoopPositivityLevel : ProofLevel
coupledOneLoopPositivityLevel = machineChecked

physicalCoupledRemainderProducerLevel : ProofLevel
physicalCoupledRemainderProducerLevel = conditional
