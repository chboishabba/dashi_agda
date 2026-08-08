module DASHI.Physics.YangMills.BalabanP33WilsonDeepRemainderEnvelopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Prove the complete finite algebra behind the grouped deep Wilson remainder.
-- If each selected factor defect satisfies
--
--   N(D_i) <= epsilon^2 w_i,
--
-- each identity factor has N(B_i)=w_i, and
--
--   w0 w1 w2 w3 = leftCharge * rightCharge,
--
-- then every cubic subset term is bounded below by epsilon^3 times the
-- square-root-free Young charge, and the quartic term by epsilon^4.  Summing
-- the four cubic terms and one quartic term gives
--
--   -(4 epsilon^3 + epsilon^4) Young(left,right)
--     <= WilsonScalar(deepRemainder).
--
-- The theorem is entirely over exact rationals and ordered quaternion
-- multiplication.  No commutativity of quaternion factors or square root is
-- used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonCorrelatedDeepPartitionExact as Deep
import DASHI.Physics.YangMills.BalabanP33QuaternionScaledYoungLowerExact as Scaled
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionScalarBudgetExact as Strong

multiplyMonotoneNonnegative :
  ∀ a aUpper b bUpper →
  0ℚ ≤ aUpper → 0ℚ ≤ b →
  a ≤ aUpper → b ≤ bUpper →
  a * b ≤ aUpper * bUpper
multiplyMonotoneNonnegative
    a aUpper b bUpper aUpperNN bNN aBelow bBelow =
  let
    first : a * b ≤ aUpper * b
    first =
      subst
        (λ lower → lower ≤ aUpper * b)
        (ℚRing.solve-∀ a b)
        (subst
          (λ upper → b * a ≤ upper)
          (ℚRing.solve-∀ aUpper b)
          (Norm.scaleNonnegative b bNN aBelow))

    second : aUpper * b ≤ aUpper * bUpper
    second = Norm.scaleNonnegative aUpper aUpperNN bBelow
  in
  ℚP.≤-trans first second

product4NormUpper :
  ∀ f0 f1 f2 f3 u0 u1 u2 u3 →
  Norm.normSq f0 ≤ u0 → Norm.normSq f1 ≤ u1 →
  Norm.normSq f2 ≤ u2 → Norm.normSq f3 ≤ u3 →
  0ℚ ≤ u0 → 0ℚ ≤ u1 → 0ℚ ≤ u2 → 0ℚ ≤ u3 →
  Norm.normSq (Telescope.orderedProduct4 f0 f1 f2 f3)
  ≤ u0 * u1 * u2 * u3
product4NormUpper
    f0 f1 f2 f3 u0 u1 u2 u3
    bound0 bound1 bound2 bound3
    u0NN u1NN u2NN u3NN =
  let
    n0 = Norm.normSq f0
    n1 = Norm.normSq f1
    n2 = Norm.normSq f2
    n3 = Norm.normSq f3

    n1NN = Norm.normSqNonnegative f1
    n2NN = Norm.normSqNonnegative f2
    n3NN = Norm.normSqNonnegative f3

    u01NN = Strong.multiplyNonnegative u0 u1 u0NN u1NN
    u012NN = Strong.multiplyNonnegative (u0 * u1) u2 u01NN u2NN

    pairBound : n0 * n1 ≤ u0 * u1
    pairBound =
      multiplyMonotoneNonnegative
        n0 u0 n1 u1 u0NN n1NN bound0 bound1

    tripleBound : n0 * n1 * n2 ≤ u0 * u1 * u2
    tripleBound =
      multiplyMonotoneNonnegative
        (n0 * n1) (u0 * u1) n2 u2
        u01NN n2NN pairBound bound2

    quadrupleBound :
      n0 * n1 * n2 * n3 ≤ u0 * u1 * u2 * u3
    quadrupleBound =
      multiplyMonotoneNonnegative
        (n0 * n1 * n2) (u0 * u1 * u2) n3 u3
        u012NN n3NN tripleBound bound3
  in
  subst
    (λ lower → lower ≤ u0 * u1 * u2 * u3)
    (sym
      (trans
        (Norm.normSqMultiplyExact f0
          (f1 Q.*q (f2 Q.*q (f3 Q.*q Q.oneQ))))
        (trans
          (cong (n0 *_)
            (Norm.normSqMultiplyExact f1
              (f2 Q.*q (f3 Q.*q Q.oneQ))))
          (trans
            (cong
              (λ selected → n0 * (n1 * selected))
              (Norm.normSqMultiplyExact f2 (f3 Q.*q Q.oneQ)))
            (trans
              (cong
                (λ selected → n0 * (n1 * (n2 * selected)))
                (Norm.normSqMultiplyExact f3 Q.oneQ))
              (ℚRing.solve-∀ n0 n1 n2 n3)))))
    quadrupleBound

record FourFactorDeepEnvelope
    (a0 a1 a2 a3 b0 b1 b2 b3 : Q.RationalQuaternion)
    (epsilon leftCharge rightCharge : ℚ) : Set where
  field
    w0 w1 w2 w3 : ℚ

    epsilonNonnegative : 0ℚ ≤ epsilon
    leftChargeNonnegative : 0ℚ ≤ leftCharge
    rightChargeNonnegative : 0ℚ ≤ rightCharge
    w0Nonnegative : 0ℚ ≤ w0
    w1Nonnegative : 0ℚ ≤ w1
    w2Nonnegative : 0ℚ ≤ w2
    w3Nonnegative : 0ℚ ≤ w3

    baseNorm0 : Norm.normSq b0 ≡ w0
    baseNorm1 : Norm.normSq b1 ≡ w1
    baseNorm2 : Norm.normSq b2 ≡ w2
    baseNorm3 : Norm.normSq b3 ≡ w3

    defectNorm0 :
      Norm.normSq (Partition.factorDefect a0 b0)
      ≤ (epsilon * epsilon) * w0
    defectNorm1 :
      Norm.normSq (Partition.factorDefect a1 b1)
      ≤ (epsilon * epsilon) * w1
    defectNorm2 :
      Norm.normSq (Partition.factorDefect a2 b2)
      ≤ (epsilon * epsilon) * w2
    defectNorm3 :
      Norm.normSq (Partition.factorDefect a3 b3)
      ≤ (epsilon * epsilon) * w3

    weightProductExact :
      w0 * w1 * w2 * w3 ≡ leftCharge * rightCharge

open FourFactorDeepEnvelope public

epsilonSquareNonnegative :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  0ℚ ≤ epsilon * epsilon
epsilonSquareNonnegative envelope =
  Strong.multiplyNonnegative
    _ _ (epsilonNonnegative envelope) (epsilonNonnegative envelope)

epsilonCube : ℚ → ℚ
epsilonCube epsilon = epsilon * epsilon * epsilon

epsilonFourth : ℚ → ℚ
epsilonFourth epsilon = epsilon * epsilon * epsilon * epsilon

epsilonCubeNonnegative :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  0ℚ ≤ epsilonCube epsilon
epsilonCubeNonnegative envelope =
  Strong.multiplyNonnegative
    (_ * _) _
    (epsilonSquareNonnegative envelope)
    (epsilonNonnegative envelope)

epsilonFourthNonnegative :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  0ℚ ≤ epsilonFourth epsilon
epsilonFourthNonnegative envelope =
  Strong.multiplyNonnegative
    (_ * _ * _) _
    (epsilonCubeNonnegative envelope)
    (epsilonNonnegative envelope)

baseNormBelow : ∀ {value weight} →
  Norm.normSq value ≡ weight → Norm.normSq value ≤ weight
baseNormBelow refl = ℚP.≤-refl

triple012NormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq
    (Telescope.orderedProduct4
      (Partition.factorDefect a0 b0)
      (Partition.factorDefect a1 b1)
      (Partition.factorDefect a2 b2) b3)
  ≤ (epsilonCube epsilon * left) * (epsilonCube epsilon * right)
triple012NormUpper {epsilon = epsilon} {left} {right} envelope =
  let
    e2 = epsilon * epsilon
    raw = product4NormUpper
      (Partition.factorDefect _ _) (Partition.factorDefect _ _)
      (Partition.factorDefect _ _) _
      (e2 * w0 envelope) (e2 * w1 envelope)
      (e2 * w2 envelope) (w3 envelope)
      (defectNorm0 envelope) (defectNorm1 envelope)
      (defectNorm2 envelope) (baseNormBelow (baseNorm3 envelope))
      (Strong.multiplyNonnegative e2 (w0 envelope)
        (epsilonSquareNonnegative envelope) (w0Nonnegative envelope))
      (Strong.multiplyNonnegative e2 (w1 envelope)
        (epsilonSquareNonnegative envelope) (w1Nonnegative envelope))
      (Strong.multiplyNonnegative e2 (w2 envelope)
        (epsilonSquareNonnegative envelope) (w2Nonnegative envelope))
      (w3Nonnegative envelope)
  in
  subst
    (λ upper →
      Norm.normSq
        (Telescope.orderedProduct4
          (Partition.factorDefect _ _)
          (Partition.factorDefect _ _)
          (Partition.factorDefect _ _) _)
      ≤ upper)
    (trans
      (cong
        (λ weight →
          (epsilonCube epsilon * left)
            * (epsilonCube epsilon * right)
          ≡ (epsilonCube epsilon * epsilonCube epsilon) * weight)
        (sym (weightProductExact envelope)))
      (ℚRing.solve-∀ epsilon (w0 envelope) (w1 envelope)
        (w2 envelope) (w3 envelope) left right))
    raw

-- The other three cubic placements and the quartic placement differ only in
-- which base factor remains.  Exact rational normalization keeps their common
-- epsilon^3/epsilon^4 charge visible.

triple013NormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq
    (Telescope.orderedProduct4
      (Partition.factorDefect a0 b0)
      (Partition.factorDefect a1 b1) b2
      (Partition.factorDefect a3 b3))
  ≤ (epsilonCube epsilon * left) * (epsilonCube epsilon * right)
triple013NormUpper {epsilon = epsilon} {left} {right} envelope =
  let e2 = epsilon * epsilon
      raw = product4NormUpper
        (Partition.factorDefect _ _) (Partition.factorDefect _ _) _
        (Partition.factorDefect _ _)
        (e2 * w0 envelope) (e2 * w1 envelope)
        (w2 envelope) (e2 * w3 envelope)
        (defectNorm0 envelope) (defectNorm1 envelope)
        (baseNormBelow (baseNorm2 envelope)) (defectNorm3 envelope)
        (Strong.multiplyNonnegative e2 (w0 envelope)
          (epsilonSquareNonnegative envelope) (w0Nonnegative envelope))
        (Strong.multiplyNonnegative e2 (w1 envelope)
          (epsilonSquareNonnegative envelope) (w1Nonnegative envelope))
        (w2Nonnegative envelope)
        (Strong.multiplyNonnegative e2 (w3 envelope)
          (epsilonSquareNonnegative envelope) (w3Nonnegative envelope))
  in
  subst (λ upper → _ ≤ upper)
    (trans
      (cong
        (λ weight →
          (epsilonCube epsilon * left)
            * (epsilonCube epsilon * right)
          ≡ (epsilonCube epsilon * epsilonCube epsilon) * weight)
        (sym (weightProductExact envelope)))
      (ℚRing.solve-∀ epsilon (w0 envelope) (w1 envelope)
        (w2 envelope) (w3 envelope) left right))
    raw

triple023NormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq
    (Telescope.orderedProduct4
      (Partition.factorDefect a0 b0) b1
      (Partition.factorDefect a2 b2)
      (Partition.factorDefect a3 b3))
  ≤ (epsilonCube epsilon * left) * (epsilonCube epsilon * right)
triple023NormUpper {epsilon = epsilon} {left} {right} envelope =
  let e2 = epsilon * epsilon
      raw = product4NormUpper
        (Partition.factorDefect _ _) _ (Partition.factorDefect _ _)
        (Partition.factorDefect _ _)
        (e2 * w0 envelope) (w1 envelope)
        (e2 * w2 envelope) (e2 * w3 envelope)
        (defectNorm0 envelope) (baseNormBelow (baseNorm1 envelope))
        (defectNorm2 envelope) (defectNorm3 envelope)
        (Strong.multiplyNonnegative e2 (w0 envelope)
          (epsilonSquareNonnegative envelope) (w0Nonnegative envelope))
        (w1Nonnegative envelope)
        (Strong.multiplyNonnegative e2 (w2 envelope)
          (epsilonSquareNonnegative envelope) (w2Nonnegative envelope))
        (Strong.multiplyNonnegative e2 (w3 envelope)
          (epsilonSquareNonnegative envelope) (w3Nonnegative envelope))
  in
  subst (λ upper → _ ≤ upper)
    (trans
      (cong
        (λ weight →
          (epsilonCube epsilon * left)
            * (epsilonCube epsilon * right)
          ≡ (epsilonCube epsilon * epsilonCube epsilon) * weight)
        (sym (weightProductExact envelope)))
      (ℚRing.solve-∀ epsilon (w0 envelope) (w1 envelope)
        (w2 envelope) (w3 envelope) left right))
    raw

triple123NormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq
    (Telescope.orderedProduct4 b0
      (Partition.factorDefect a1 b1)
      (Partition.factorDefect a2 b2)
      (Partition.factorDefect a3 b3))
  ≤ (epsilonCube epsilon * left) * (epsilonCube epsilon * right)
triple123NormUpper {epsilon = epsilon} {left} {right} envelope =
  let e2 = epsilon * epsilon
      raw = product4NormUpper
        _ (Partition.factorDefect _ _) (Partition.factorDefect _ _)
        (Partition.factorDefect _ _)
        (w0 envelope) (e2 * w1 envelope)
        (e2 * w2 envelope) (e2 * w3 envelope)
        (baseNormBelow (baseNorm0 envelope)) (defectNorm1 envelope)
        (defectNorm2 envelope) (defectNorm3 envelope)
        (w0Nonnegative envelope)
        (Strong.multiplyNonnegative e2 (w1 envelope)
          (epsilonSquareNonnegative envelope) (w1Nonnegative envelope))
        (Strong.multiplyNonnegative e2 (w2 envelope)
          (epsilonSquareNonnegative envelope) (w2Nonnegative envelope))
        (Strong.multiplyNonnegative e2 (w3 envelope)
          (epsilonSquareNonnegative envelope) (w3Nonnegative envelope))
  in
  subst (λ upper → _ ≤ upper)
    (trans
      (cong
        (λ weight →
          (epsilonCube epsilon * left)
            * (epsilonCube epsilon * right)
          ≡ (epsilonCube epsilon * epsilonCube epsilon) * weight)
        (sym (weightProductExact envelope)))
      (ℚRing.solve-∀ epsilon (w0 envelope) (w1 envelope)
        (w2 envelope) (w3 envelope) left right))
    raw

quarticNormUpper :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  Norm.normSq
    (Telescope.orderedProduct4
      (Partition.factorDefect a0 b0)
      (Partition.factorDefect a1 b1)
      (Partition.factorDefect a2 b2)
      (Partition.factorDefect a3 b3))
  ≤ (epsilonFourth epsilon * left) * (epsilonFourth epsilon * right)
quarticNormUpper {epsilon = epsilon} {left} {right} envelope =
  let e2 = epsilon * epsilon
      raw = product4NormUpper
        (Partition.factorDefect _ _) (Partition.factorDefect _ _)
        (Partition.factorDefect _ _) (Partition.factorDefect _ _)
        (e2 * w0 envelope) (e2 * w1 envelope)
        (e2 * w2 envelope) (e2 * w3 envelope)
        (defectNorm0 envelope) (defectNorm1 envelope)
        (defectNorm2 envelope) (defectNorm3 envelope)
        (Strong.multiplyNonnegative e2 (w0 envelope)
          (epsilonSquareNonnegative envelope) (w0Nonnegative envelope))
        (Strong.multiplyNonnegative e2 (w1 envelope)
          (epsilonSquareNonnegative envelope) (w1Nonnegative envelope))
        (Strong.multiplyNonnegative e2 (w2 envelope)
          (epsilonSquareNonnegative envelope) (w2Nonnegative envelope))
        (Strong.multiplyNonnegative e2 (w3 envelope)
          (epsilonSquareNonnegative envelope) (w3Nonnegative envelope))
  in
  subst (λ upper → _ ≤ upper)
    (trans
      (cong
        (λ weight →
          (epsilonFourth epsilon * left)
            * (epsilonFourth epsilon * right)
          ≡ (epsilonFourth epsilon * epsilonFourth epsilon) * weight)
        (sym (weightProductExact envelope)))
      (ℚRing.solve-∀ epsilon (w0 envelope) (w1 envelope)
        (w2 envelope) (w3 envelope) left right))
    raw

deepWilsonScalarSumExact :
  ∀ t0 t1 t2 t3 t4 →
  Telescope.wilsonScalar
    (Q.sumQuaternion (t0 ∷ t1 ∷ t2 ∷ t3 ∷ t4 ∷ []))
  ≡ Telescope.wilsonScalar t0
    + (Telescope.wilsonScalar t1
    + (Telescope.wilsonScalar t2
    + (Telescope.wilsonScalar t3
    + Telescope.wilsonScalar t4)))
deepWilsonScalarSumExact
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)
    (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3)
    (Q.quat e0 e1 e2 e3) =
  ℚRing.solve-∀ a0 b0 c0 d0 e0

deepRemainderLower :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  - ((+ 4 / 1) * epsilonCube epsilon + epsilonFourth epsilon)
      * ((+ 1 / 2) * (left + right))
  ≤ Telescope.wilsonScalar
      (Deep.fourFactorDeepRemainder
        a0 a1 a2 a3 b0 b1 b2 b3)
deepRemainderLower {epsilon = epsilon} {left} {right} envelope =
  let
    d0 = Partition.factorDefect _ _
    d1 = Partition.factorDefect _ _
    d2 = Partition.factorDefect _ _
    d3 = Partition.factorDefect _ _

    t012 = Telescope.orderedProduct4 d0 d1 d2 _
    t013 = Telescope.orderedProduct4 d0 d1 _ d3
    t023 = Telescope.orderedProduct4 d0 _ d2 d3
    t123 = Telescope.orderedProduct4 _ d1 d2 d3
    t0123 = Telescope.orderedProduct4 d0 d1 d2 d3

    cubeLower0 = Scaled.scaledYoungLowerFromNorm
      t012 (epsilonCube epsilon) left right
      (epsilonCubeNonnegative envelope)
      (leftChargeNonnegative envelope) (rightChargeNonnegative envelope)
      (triple012NormUpper envelope)
    cubeLower1 = Scaled.scaledYoungLowerFromNorm
      t013 (epsilonCube epsilon) left right
      (epsilonCubeNonnegative envelope)
      (leftChargeNonnegative envelope) (rightChargeNonnegative envelope)
      (triple013NormUpper envelope)
    cubeLower2 = Scaled.scaledYoungLowerFromNorm
      t023 (epsilonCube epsilon) left right
      (epsilonCubeNonnegative envelope)
      (leftChargeNonnegative envelope) (rightChargeNonnegative envelope)
      (triple023NormUpper envelope)
    cubeLower3 = Scaled.scaledYoungLowerFromNorm
      t123 (epsilonCube epsilon) left right
      (epsilonCubeNonnegative envelope)
      (leftChargeNonnegative envelope) (rightChargeNonnegative envelope)
      (triple123NormUpper envelope)
    fourthLower = Scaled.scaledYoungLowerFromNorm
      t0123 (epsilonFourth epsilon) left right
      (epsilonFourthNonnegative envelope)
      (leftChargeNonnegative envelope) (rightChargeNonnegative envelope)
      (quarticNormUpper envelope)

    summed = ℚP.+-mono-≤ cubeLower0
      (ℚP.+-mono-≤ cubeLower1
        (ℚP.+-mono-≤ cubeLower2
          (ℚP.+-mono-≤ cubeLower3 fourthLower)))
  in
  subst
    (λ lower →
      lower
      ≤ Telescope.wilsonScalar
          (Deep.fourFactorDeepRemainder
            _ _ _ _ _ _ _ _))
    (ℚRing.solve-∀ epsilon left right)
    (subst
      (λ upper →
        - Scaled.scaledYoungBudget (epsilonCube epsilon) left right
        + (- Scaled.scaledYoungBudget (epsilonCube epsilon) left right
        + (- Scaled.scaledYoungBudget (epsilonCube epsilon) left right
        + (- Scaled.scaledYoungBudget (epsilonCube epsilon) left right
        + - Scaled.scaledYoungBudget (epsilonFourth epsilon) left right)))
        ≤ upper)
      (sym (deepWilsonScalarSumExact t012 t013 t023 t123 t0123))
      summed)

wilsonDeepRemainderEnvelopeLevel : ProofLevel
wilsonDeepRemainderEnvelopeLevel = machineChecked
