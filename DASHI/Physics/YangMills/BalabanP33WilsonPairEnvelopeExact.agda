module DASHI.Physics.YangMills.BalabanP33WilsonPairEnvelopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong
-- Coupling". DOI: 10.1007/s00220-022-04609-1.
--
-- DASHI CONTRIBUTION
--
-- Prove the square-root-free lower bound for the six quadratic subset terms
-- of one ordered four-factor Wilson defect.  Under the same selected-factor
-- envelope used by the cubic--quartic theorem, every pair term costs
-- epsilon^2 times the placement Young charge.  The exact six-term sum is
-- therefore bounded below by
--
--   -6 epsilon^2 (leftCharge + rightCharge)/2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonCorrelatedDeepPartitionExact as Split
import DASHI.Physics.YangMills.BalabanP33QuaternionScaledYoungLowerExact as Scaled
import DASHI.Physics.YangMills.BalabanP33WilsonDeepRemainderEnvelopeExact as Envelope

pairUpperExact : ∀ epsilon w0 w1 w2 w3 left right →
  w0 * w1 * w2 * w3 ≡ left * right →
  (Envelope.epsilonSquare epsilon * w0)
    * (Envelope.epsilonSquare epsilon * w1) * w2 * w3
  ≡ (Envelope.epsilonSquare epsilon * left)
      * (Envelope.epsilonSquare epsilon * right)
pairUpperExact epsilon w0 w1 w2 w3 left right weights =
  trans
    (ℚRing.solve-∀ epsilon w0 w1 w2 w3)
    (trans
      (cong
        ((Envelope.epsilonSquare epsilon
          * Envelope.epsilonSquare epsilon) *_)
        weights)
      (ℚRing.solve-∀ epsilon left right))

pairTermNormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (env : Envelope.FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right)
    f0 f1 f2 f3 u0 u1 u2 u3 →
  Norm.normSq f0 ≤ u0 → Norm.normSq f1 ≤ u1 →
  Norm.normSq f2 ≤ u2 → Norm.normSq f3 ≤ u3 →
  0ℚ ≤ u0 → 0ℚ ≤ u1 → 0ℚ ≤ u2 → 0ℚ ≤ u3 →
  u0 * u1 * u2 * u3
    ≡ (Envelope.epsilonSquare epsilon * left)
      * (Envelope.epsilonSquare epsilon * right) →
  Norm.normSq (Telescope.orderedProduct4 f0 f1 f2 f3)
  ≤ (Envelope.epsilonSquare epsilon * left)
      * (Envelope.epsilonSquare epsilon * right)
pairTermNormUpper env f0 f1 f2 f3 u0 u1 u2 u3
    b0 b1 b2 b3 n0 n1 n2 n3 exact =
  subst
    (λ upper →
      Norm.normSq (Telescope.orderedProduct4 f0 f1 f2 f3) ≤ upper)
    exact
    (Envelope.product4NormUpper f0 f1 f2 f3 u0 u1 u2 u3
      b0 b1 b2 b3 n0 n1 n2 n3)

pair01ActualNormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (env : Envelope.FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq (Telescope.orderedProduct4
    (Partition.factorDefect a0 b0) (Partition.factorDefect a1 b1) b2 b3)
  ≤ (Envelope.epsilonSquare epsilon * left)
      * (Envelope.epsilonSquare epsilon * right)
pair01ActualNormUpper {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} env =
  pairTermNormUpper env
    (Partition.factorDefect a0 b0) (Partition.factorDefect a1 b1) b2 b3
    (Envelope.epsilonSquare epsilon * Envelope.w0 env)
    (Envelope.epsilonSquare epsilon * Envelope.w1 env)
    (Envelope.w2 env) (Envelope.w3 env)
    (Envelope.defectNorm0 env) (Envelope.defectNorm1 env)
    (Envelope.baseNormBelow (Envelope.baseNorm2 env))
    (Envelope.baseNormBelow (Envelope.baseNorm3 env))
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w0 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w0Nonnegative env))
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w1 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w1Nonnegative env))
    (Envelope.w2Nonnegative env) (Envelope.w3Nonnegative env)
    (pairUpperExact epsilon
      (Envelope.w0 env) (Envelope.w1 env)
      (Envelope.w2 env) (Envelope.w3 env) left right
      (Envelope.weightProductExact env))

pair02ActualNormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (env : Envelope.FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq (Telescope.orderedProduct4
    (Partition.factorDefect a0 b0) b1 (Partition.factorDefect a2 b2) b3)
  ≤ (Envelope.epsilonSquare epsilon * left)
      * (Envelope.epsilonSquare epsilon * right)
pair02ActualNormUpper {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} env =
  pairTermNormUpper env
    (Partition.factorDefect a0 b0) b1 (Partition.factorDefect a2 b2) b3
    (Envelope.epsilonSquare epsilon * Envelope.w0 env)
    (Envelope.w1 env)
    (Envelope.epsilonSquare epsilon * Envelope.w2 env)
    (Envelope.w3 env)
    (Envelope.defectNorm0 env)
    (Envelope.baseNormBelow (Envelope.baseNorm1 env))
    (Envelope.defectNorm2 env)
    (Envelope.baseNormBelow (Envelope.baseNorm3 env))
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w0 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w0Nonnegative env))
    (Envelope.w1Nonnegative env)
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w2 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w2Nonnegative env))
    (Envelope.w3Nonnegative env)
    (trans
      (ℚRing.solve-∀ epsilon
        (Envelope.w0 env) (Envelope.w1 env)
        (Envelope.w2 env) (Envelope.w3 env))
      (trans
        (cong ((Envelope.epsilonSquare epsilon
          * Envelope.epsilonSquare epsilon) *_)
          (Envelope.weightProductExact env))
        (ℚRing.solve-∀ epsilon left right)))

pair03ActualNormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (env : Envelope.FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq (Telescope.orderedProduct4
    (Partition.factorDefect a0 b0) b1 b2 (Partition.factorDefect a3 b3))
  ≤ (Envelope.epsilonSquare epsilon * left)
      * (Envelope.epsilonSquare epsilon * right)
pair03ActualNormUpper {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} env =
  pairTermNormUpper env
    (Partition.factorDefect a0 b0) b1 b2 (Partition.factorDefect a3 b3)
    (Envelope.epsilonSquare epsilon * Envelope.w0 env)
    (Envelope.w1 env) (Envelope.w2 env)
    (Envelope.epsilonSquare epsilon * Envelope.w3 env)
    (Envelope.defectNorm0 env)
    (Envelope.baseNormBelow (Envelope.baseNorm1 env))
    (Envelope.baseNormBelow (Envelope.baseNorm2 env))
    (Envelope.defectNorm3 env)
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w0 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w0Nonnegative env))
    (Envelope.w1Nonnegative env) (Envelope.w2Nonnegative env)
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w3 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w3Nonnegative env))
    (trans
      (ℚRing.solve-∀ epsilon
        (Envelope.w0 env) (Envelope.w1 env)
        (Envelope.w2 env) (Envelope.w3 env))
      (trans
        (cong ((Envelope.epsilonSquare epsilon
          * Envelope.epsilonSquare epsilon) *_)
          (Envelope.weightProductExact env))
        (ℚRing.solve-∀ epsilon left right)))

pair12ActualNormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (env : Envelope.FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq (Telescope.orderedProduct4
    b0 (Partition.factorDefect a1 b1) (Partition.factorDefect a2 b2) b3)
  ≤ (Envelope.epsilonSquare epsilon * left)
      * (Envelope.epsilonSquare epsilon * right)
pair12ActualNormUpper {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} env =
  pairTermNormUpper env
    b0 (Partition.factorDefect a1 b1) (Partition.factorDefect a2 b2) b3
    (Envelope.w0 env)
    (Envelope.epsilonSquare epsilon * Envelope.w1 env)
    (Envelope.epsilonSquare epsilon * Envelope.w2 env)
    (Envelope.w3 env)
    (Envelope.baseNormBelow (Envelope.baseNorm0 env))
    (Envelope.defectNorm1 env) (Envelope.defectNorm2 env)
    (Envelope.baseNormBelow (Envelope.baseNorm3 env))
    (Envelope.w0Nonnegative env)
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w1 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w1Nonnegative env))
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w2 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w2Nonnegative env))
    (Envelope.w3Nonnegative env)
    (trans
      (ℚRing.solve-∀ epsilon
        (Envelope.w0 env) (Envelope.w1 env)
        (Envelope.w2 env) (Envelope.w3 env))
      (trans
        (cong ((Envelope.epsilonSquare epsilon
          * Envelope.epsilonSquare epsilon) *_)
          (Envelope.weightProductExact env))
        (ℚRing.solve-∀ epsilon left right)))

pair13ActualNormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (env : Envelope.FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq (Telescope.orderedProduct4
    b0 (Partition.factorDefect a1 b1) b2 (Partition.factorDefect a3 b3))
  ≤ (Envelope.epsilonSquare epsilon * left)
      * (Envelope.epsilonSquare epsilon * right)
pair13ActualNormUpper {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} env =
  pairTermNormUpper env
    b0 (Partition.factorDefect a1 b1) b2 (Partition.factorDefect a3 b3)
    (Envelope.w0 env)
    (Envelope.epsilonSquare epsilon * Envelope.w1 env)
    (Envelope.w2 env)
    (Envelope.epsilonSquare epsilon * Envelope.w3 env)
    (Envelope.baseNormBelow (Envelope.baseNorm0 env))
    (Envelope.defectNorm1 env)
    (Envelope.baseNormBelow (Envelope.baseNorm2 env))
    (Envelope.defectNorm3 env)
    (Envelope.w0Nonnegative env)
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w1 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w1Nonnegative env))
    (Envelope.w2Nonnegative env)
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w3 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w3Nonnegative env))
    (trans
      (ℚRing.solve-∀ epsilon
        (Envelope.w0 env) (Envelope.w1 env)
        (Envelope.w2 env) (Envelope.w3 env))
      (trans
        (cong ((Envelope.epsilonSquare epsilon
          * Envelope.epsilonSquare epsilon) *_)
          (Envelope.weightProductExact env))
        (ℚRing.solve-∀ epsilon left right)))

pair23ActualNormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (env : Envelope.FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq (Telescope.orderedProduct4
    b0 b1 (Partition.factorDefect a2 b2) (Partition.factorDefect a3 b3))
  ≤ (Envelope.epsilonSquare epsilon * left)
      * (Envelope.epsilonSquare epsilon * right)
pair23ActualNormUpper {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} env =
  pairTermNormUpper env
    b0 b1 (Partition.factorDefect a2 b2) (Partition.factorDefect a3 b3)
    (Envelope.w0 env) (Envelope.w1 env)
    (Envelope.epsilonSquare epsilon * Envelope.w2 env)
    (Envelope.epsilonSquare epsilon * Envelope.w3 env)
    (Envelope.baseNormBelow (Envelope.baseNorm0 env))
    (Envelope.baseNormBelow (Envelope.baseNorm1 env))
    (Envelope.defectNorm2 env) (Envelope.defectNorm3 env)
    (Envelope.w0Nonnegative env) (Envelope.w1Nonnegative env)
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w2 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w2Nonnegative env))
    (Envelope.scaledWeightNonnegative
      (Envelope.epsilonSquare epsilon) (Envelope.w3 env)
      (Envelope.epsilonSquareNonnegative env) (Envelope.w3Nonnegative env))
    (trans
      (ℚRing.solve-∀ epsilon
        (Envelope.w0 env) (Envelope.w1 env)
        (Envelope.w2 env) (Envelope.w3 env))
      (trans
        (cong ((Envelope.epsilonSquare epsilon
          * Envelope.epsilonSquare epsilon) *_)
          (Envelope.weightProductExact env))
        (ℚRing.solve-∀ epsilon left right)))

pairWilsonScalarSumExact : ∀ t01 t02 t03 t12 t13 t23 →
  Telescope.wilsonScalar
    (Q.sumQuaternion (t01 ∷ t02 ∷ t03 ∷ t12 ∷ t13 ∷ t23 ∷ []))
  ≡ Telescope.wilsonScalar t01
    + (Telescope.wilsonScalar t02
    + (Telescope.wilsonScalar t03
    + (Telescope.wilsonScalar t12
    + (Telescope.wilsonScalar t13
    + Telescope.wilsonScalar t23))))
pairWilsonScalarSumExact
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)
    (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3)
    (Q.quat e0 e1 e2 e3) (Q.quat f0 f1 f2 f3) =
  ℚRing.solve-∀ a0 b0 c0 d0 e0 f0

pairRemainderLower :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (env : Envelope.FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  - ((+ 6 / 1) * Envelope.epsilonSquare epsilon)
      * ((+ 1 / 2) * (left + right))
  ≤ Telescope.wilsonScalar
      (Split.fourFactorPairPart a0 a1 a2 a3 b0 b1 b2 b3)
pairRemainderLower
    {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} env =
  let
    d0 = Partition.factorDefect a0 b0
    d1 = Partition.factorDefect a1 b1
    d2 = Partition.factorDefect a2 b2
    d3 = Partition.factorDefect a3 b3
    t01 = Telescope.orderedProduct4 d0 d1 b2 b3
    t02 = Telescope.orderedProduct4 d0 b1 d2 b3
    t03 = Telescope.orderedProduct4 d0 b1 b2 d3
    t12 = Telescope.orderedProduct4 b0 d1 d2 b3
    t13 = Telescope.orderedProduct4 b0 d1 b2 d3
    t23 = Telescope.orderedProduct4 b0 b1 d2 d3
    scale = Envelope.epsilonSquare epsilon

    l01 = Scaled.scaledYoungLowerFromNorm t01 scale left right
      (Envelope.epsilonSquareNonnegative env)
      (Envelope.leftChargeNonnegative env) (Envelope.rightChargeNonnegative env)
      (pair01ActualNormUpper env)
    l02 = Scaled.scaledYoungLowerFromNorm t02 scale left right
      (Envelope.epsilonSquareNonnegative env)
      (Envelope.leftChargeNonnegative env) (Envelope.rightChargeNonnegative env)
      (pair02ActualNormUpper env)
    l03 = Scaled.scaledYoungLowerFromNorm t03 scale left right
      (Envelope.epsilonSquareNonnegative env)
      (Envelope.leftChargeNonnegative env) (Envelope.rightChargeNonnegative env)
      (pair03ActualNormUpper env)
    l12 = Scaled.scaledYoungLowerFromNorm t12 scale left right
      (Envelope.epsilonSquareNonnegative env)
      (Envelope.leftChargeNonnegative env) (Envelope.rightChargeNonnegative env)
      (pair12ActualNormUpper env)
    l13 = Scaled.scaledYoungLowerFromNorm t13 scale left right
      (Envelope.epsilonSquareNonnegative env)
      (Envelope.leftChargeNonnegative env) (Envelope.rightChargeNonnegative env)
      (pair13ActualNormUpper env)
    l23 = Scaled.scaledYoungLowerFromNorm t23 scale left right
      (Envelope.epsilonSquareNonnegative env)
      (Envelope.leftChargeNonnegative env) (Envelope.rightChargeNonnegative env)
      (pair23ActualNormUpper env)

    summed = ℚP.+-mono-≤ l01
      (ℚP.+-mono-≤ l02
        (ℚP.+-mono-≤ l03
          (ℚP.+-mono-≤ l12
            (ℚP.+-mono-≤ l13 l23))))

    lowerExact :
      - Scaled.scaledYoungBudget scale left right
      + (- Scaled.scaledYoungBudget scale left right
      + (- Scaled.scaledYoungBudget scale left right
      + (- Scaled.scaledYoungBudget scale left right
      + (- Scaled.scaledYoungBudget scale left right
      + - Scaled.scaledYoungBudget scale left right))))
      ≡ - ((+ 6 / 1) * scale) * ((+ 1 / 2) * (left + right))
    lowerExact = ℚRing.solve-∀ scale left right
  in
  subst
    (λ lower → lower ≤ Telescope.wilsonScalar
      (Split.fourFactorPairPart a0 a1 a2 a3 b0 b1 b2 b3))
    lowerExact
    (subst
      (λ upper →
        - Scaled.scaledYoungBudget scale left right
        + (- Scaled.scaledYoungBudget scale left right
        + (- Scaled.scaledYoungBudget scale left right
        + (- Scaled.scaledYoungBudget scale left right
        + (- Scaled.scaledYoungBudget scale left right
        + - Scaled.scaledYoungBudget scale left right)))) ≤ upper)
      (sym (pairWilsonScalarSumExact t01 t02 t03 t12 t13 t23))
      summed)

wilsonPairEnvelopeLevel : ProofLevel
wilsonPairEnvelopeLevel = machineChecked
