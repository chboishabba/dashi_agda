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
-- If every selected-factor defect satisfies
--
--   N(D_i) <= epsilon^2 w_i,
--
-- every identity factor has N(B_i)=w_i, and
--
--   w0 w1 w2 w3 = leftCharge * rightCharge,
--
-- then every cubic subset term is bounded below by epsilon^3 times the
-- square-root-free Young charge, and the quartic term by epsilon^4.  Summing
-- the four cubic terms and one quartic term gives
--
--   -(4 epsilon^3 + epsilon^4) (leftCharge+rightCharge)/2
--     <= WilsonScalar(deepRemainder).
--
-- Every upper-bound transport below is an explicit equality of rational
-- scalars.  No unresolved factor placeholder, square root, commutativity of
-- quaternion multiplication, or analytic norm receipt is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
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

orderedProduct4NormSqExact : ∀ f0 f1 f2 f3 →
  Norm.normSq (Telescope.orderedProduct4 f0 f1 f2 f3)
  ≡ Norm.normSq f0 * Norm.normSq f1
      * Norm.normSq f2 * Norm.normSq f3
orderedProduct4NormSqExact f0 f1 f2 f3 =
  let
    n0 = Norm.normSq f0
    n1 = Norm.normSq f1
    n2 = Norm.normSq f2
    n3 = Norm.normSq f3
  in
  trans
    (Norm.normSqMultiplyExact f0
      (f1 Q.*q (f2 Q.*q (f3 Q.*q Q.oneQ))))
    (trans
      (cong (n0 *_)
        (Norm.normSqMultiplyExact f1
          (f2 Q.*q (f3 Q.*q Q.oneQ))))
      (trans
        (cong (λ selected → n0 * (n1 * selected))
          (Norm.normSqMultiplyExact f2 (f3 Q.*q Q.oneQ)))
        (trans
          (cong (λ selected → n0 * (n1 * (n2 * selected)))
            (Norm.normSqMultiplyExact f3 Q.oneQ))
          (ℚRing.solve-∀ n0 n1 n2 n3)))

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
    pairBound = multiplyMonotoneNonnegative
      n0 u0 n1 u1 u0NN n1NN bound0 bound1

    tripleBound : n0 * n1 * n2 ≤ u0 * u1 * u2
    tripleBound = multiplyMonotoneNonnegative
      (n0 * n1) (u0 * u1) n2 u2
      u01NN n2NN pairBound bound2

    quadrupleBound :
      n0 * n1 * n2 * n3 ≤ u0 * u1 * u2 * u3
    quadrupleBound = multiplyMonotoneNonnegative
      (n0 * n1 * n2) (u0 * u1 * u2) n3 u3
      u012NN n3NN tripleBound bound3
  in
  subst
    (λ lower → lower ≤ u0 * u1 * u2 * u3)
    (sym (orderedProduct4NormSqExact f0 f1 f2 f3))
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

epsilonSquare : ℚ → ℚ
epsilonSquare epsilon = epsilon * epsilon

epsilonCube : ℚ → ℚ
epsilonCube epsilon = epsilon * epsilon * epsilon

epsilonFourth : ℚ → ℚ
epsilonFourth epsilon = epsilon * epsilon * epsilon * epsilon

epsilonSquareNonnegative :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  0ℚ ≤ epsilonSquare epsilon
epsilonSquareNonnegative {epsilon = epsilon} envelope =
  Strong.multiplyNonnegative epsilon epsilon
    (epsilonNonnegative envelope) (epsilonNonnegative envelope)

epsilonCubeNonnegative :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  0ℚ ≤ epsilonCube epsilon
epsilonCubeNonnegative {epsilon = epsilon} envelope =
  Strong.multiplyNonnegative
    (epsilonSquare epsilon) epsilon
    (epsilonSquareNonnegative envelope)
    (epsilonNonnegative envelope)

epsilonFourthNonnegative :
  ∀ {a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right}
    (envelope : FourFactorDeepEnvelope
      a0 a1 a2 a3 b0 b1 b2 b3 epsilon left right) →
  0ℚ ≤ epsilonFourth epsilon
epsilonFourthNonnegative {epsilon = epsilon} envelope =
  Strong.multiplyNonnegative
    (epsilonCube epsilon) epsilon
    (epsilonCubeNonnegative envelope)
    (epsilonNonnegative envelope)

baseNormBelow : ∀ {value weight} →
  Norm.normSq value ≡ weight → Norm.normSq value ≤ weight
baseNormBelow refl = ℚP.≤-refl

scaledWeightNonnegative : ∀ scale weight →
  0ℚ ≤ scale → 0ℚ ≤ weight → 0ℚ ≤ scale * weight
scaledWeightNonnegative = Strong.multiplyNonnegative

triple012UpperExact : ∀ epsilon w0 w1 w2 w3 left right →
  w0 * w1 * w2 * w3 ≡ left * right →
  (epsilonSquare epsilon * w0)
    * (epsilonSquare epsilon * w1)
    * (epsilonSquare epsilon * w2) * w3
  ≡ (epsilonCube epsilon * left) * (epsilonCube epsilon * right)
triple012UpperExact epsilon w0 w1 w2 w3 left right weights =
  trans
    (ℚRing.solve-∀ epsilon w0 w1 w2 w3)
    (trans
      (cong ((epsilonCube epsilon * epsilonCube epsilon) *_) weights)
      (ℚRing.solve-∀ epsilon left right))

triple013UpperExact : ∀ epsilon w0 w1 w2 w3 left right →
  w0 * w1 * w2 * w3 ≡ left * right →
  (epsilonSquare epsilon * w0)
    * (epsilonSquare epsilon * w1)
    * w2 * (epsilonSquare epsilon * w3)
  ≡ (epsilonCube epsilon * left) * (epsilonCube epsilon * right)
triple013UpperExact epsilon w0 w1 w2 w3 left right weights =
  trans
    (ℚRing.solve-∀ epsilon w0 w1 w2 w3)
    (trans
      (cong ((epsilonCube epsilon * epsilonCube epsilon) *_) weights)
      (ℚRing.solve-∀ epsilon left right))

triple023UpperExact : ∀ epsilon w0 w1 w2 w3 left right →
  w0 * w1 * w2 * w3 ≡ left * right →
  (epsilonSquare epsilon * w0)
    * w1 * (epsilonSquare epsilon * w2)
    * (epsilonSquare epsilon * w3)
  ≡ (epsilonCube epsilon * left) * (epsilonCube epsilon * right)
triple023UpperExact epsilon w0 w1 w2 w3 left right weights =
  trans
    (ℚRing.solve-∀ epsilon w0 w1 w2 w3)
    (trans
      (cong ((epsilonCube epsilon * epsilonCube epsilon) *_) weights)
      (ℚRing.solve-∀ epsilon left right))

triple123UpperExact : ∀ epsilon w0 w1 w2 w3 left right →
  w0 * w1 * w2 * w3 ≡ left * right →
  w0 * (epsilonSquare epsilon * w1)
    * (epsilonSquare epsilon * w2)
    * (epsilonSquare epsilon * w3)
  ≡ (epsilonCube epsilon * left) * (epsilonCube epsilon * right)
triple123UpperExact epsilon w0 w1 w2 w3 left right weights =
  trans
    (ℚRing.solve-∀ epsilon w0 w1 w2 w3)
    (trans
      (cong ((epsilonCube epsilon * epsilonCube epsilon) *_) weights)
      (ℚRing.solve-∀ epsilon left right))

quarticUpperExact : ∀ epsilon w0 w1 w2 w3 left right →
  w0 * w1 * w2 * w3 ≡ left * right →
  (epsilonSquare epsilon * w0)
    * (epsilonSquare epsilon * w1)
    * (epsilonSquare epsilon * w2)
    * (epsilonSquare epsilon * w3)
  ≡ (epsilonFourth epsilon * left)
      * (epsilonFourth epsilon * right)
quarticUpperExact epsilon w0 w1 w2 w3 left right weights =
  trans
    (ℚRing.solve-∀ epsilon w0 w1 w2 w3)
    (trans
      (cong ((epsilonFourth epsilon * epsilonFourth epsilon) *_) weights)
      (ℚRing.solve-∀ epsilon left right))

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
triple012NormUpper
    {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} envelope =
  let
    e2 = epsilonSquare epsilon
    f0 = Partition.factorDefect a0 b0
    f1 = Partition.factorDefect a1 b1
    f2 = Partition.factorDefect a2 b2

    raw = product4NormUpper f0 f1 f2 b3
      (e2 * w0 envelope) (e2 * w1 envelope)
      (e2 * w2 envelope) (w3 envelope)
      (defectNorm0 envelope) (defectNorm1 envelope)
      (defectNorm2 envelope) (baseNormBelow (baseNorm3 envelope))
      (scaledWeightNonnegative e2 (w0 envelope)
        (epsilonSquareNonnegative envelope) (w0Nonnegative envelope))
      (scaledWeightNonnegative e2 (w1 envelope)
        (epsilonSquareNonnegative envelope) (w1Nonnegative envelope))
      (scaledWeightNonnegative e2 (w2 envelope)
        (epsilonSquareNonnegative envelope) (w2Nonnegative envelope))
      (w3Nonnegative envelope)

    upperExact = triple012UpperExact epsilon
      (w0 envelope) (w1 envelope) (w2 envelope) (w3 envelope)
      left right (weightProductExact envelope)
  in
  subst
    (λ upper → Norm.normSq
      (Telescope.orderedProduct4 f0 f1 f2 b3) ≤ upper)
    upperExact raw

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
triple013NormUpper
    {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} envelope =
  let
    e2 = epsilonSquare epsilon
    f0 = Partition.factorDefect a0 b0
    f1 = Partition.factorDefect a1 b1
    f3 = Partition.factorDefect a3 b3

    raw = product4NormUpper f0 f1 b2 f3
      (e2 * w0 envelope) (e2 * w1 envelope)
      (w2 envelope) (e2 * w3 envelope)
      (defectNorm0 envelope) (defectNorm1 envelope)
      (baseNormBelow (baseNorm2 envelope)) (defectNorm3 envelope)
      (scaledWeightNonnegative e2 (w0 envelope)
        (epsilonSquareNonnegative envelope) (w0Nonnegative envelope))
      (scaledWeightNonnegative e2 (w1 envelope)
        (epsilonSquareNonnegative envelope) (w1Nonnegative envelope))
      (w2Nonnegative envelope)
      (scaledWeightNonnegative e2 (w3 envelope)
        (epsilonSquareNonnegative envelope) (w3Nonnegative envelope))

    upperExact = triple013UpperExact epsilon
      (w0 envelope) (w1 envelope) (w2 envelope) (w3 envelope)
      left right (weightProductExact envelope)
  in
  subst
    (λ upper → Norm.normSq
      (Telescope.orderedProduct4 f0 f1 b2 f3) ≤ upper)
    upperExact raw

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
triple023NormUpper
    {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} envelope =
  let
    e2 = epsilonSquare epsilon
    f0 = Partition.factorDefect a0 b0
    f2 = Partition.factorDefect a2 b2
    f3 = Partition.factorDefect a3 b3

    raw = product4NormUpper f0 b1 f2 f3
      (e2 * w0 envelope) (w1 envelope)
      (e2 * w2 envelope) (e2 * w3 envelope)
      (defectNorm0 envelope) (baseNormBelow (baseNorm1 envelope))
      (defectNorm2 envelope) (defectNorm3 envelope)
      (scaledWeightNonnegative e2 (w0 envelope)
        (epsilonSquareNonnegative envelope) (w0Nonnegative envelope))
      (w1Nonnegative envelope)
      (scaledWeightNonnegative e2 (w2 envelope)
        (epsilonSquareNonnegative envelope) (w2Nonnegative envelope))
      (scaledWeightNonnegative e2 (w3 envelope)
        (epsilonSquareNonnegative envelope) (w3Nonnegative envelope))

    upperExact = triple023UpperExact epsilon
      (w0 envelope) (w1 envelope) (w2 envelope) (w3 envelope)
      left right (weightProductExact envelope)
  in
  subst
    (λ upper → Norm.normSq
      (Telescope.orderedProduct4 f0 b1 f2 f3) ≤ upper)
    upperExact raw

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
triple123NormUpper
    {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} envelope =
  let
    e2 = epsilonSquare epsilon
    f1 = Partition.factorDefect a1 b1
    f2 = Partition.factorDefect a2 b2
    f3 = Partition.factorDefect a3 b3

    raw = product4NormUpper b0 f1 f2 f3
      (w0 envelope) (e2 * w1 envelope)
      (e2 * w2 envelope) (e2 * w3 envelope)
      (baseNormBelow (baseNorm0 envelope)) (defectNorm1 envelope)
      (defectNorm2 envelope) (defectNorm3 envelope)
      (w0Nonnegative envelope)
      (scaledWeightNonnegative e2 (w1 envelope)
        (epsilonSquareNonnegative envelope) (w1Nonnegative envelope))
      (scaledWeightNonnegative e2 (w2 envelope)
        (epsilonSquareNonnegative envelope) (w2Nonnegative envelope))
      (scaledWeightNonnegative e2 (w3 envelope)
        (epsilonSquareNonnegative envelope) (w3Nonnegative envelope))

    upperExact = triple123UpperExact epsilon
      (w0 envelope) (w1 envelope) (w2 envelope) (w3 envelope)
      left right (weightProductExact envelope)
  in
  subst
    (λ upper → Norm.normSq
      (Telescope.orderedProduct4 b0 f1 f2 f3) ≤ upper)
    upperExact raw

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
  ≤ (epsilonFourth epsilon * left)
      * (epsilonFourth epsilon * right)
quarticNormUpper
    {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} envelope =
  let
    e2 = epsilonSquare epsilon
    f0 = Partition.factorDefect a0 b0
    f1 = Partition.factorDefect a1 b1
    f2 = Partition.factorDefect a2 b2
    f3 = Partition.factorDefect a3 b3

    raw = product4NormUpper f0 f1 f2 f3
      (e2 * w0 envelope) (e2 * w1 envelope)
      (e2 * w2 envelope) (e2 * w3 envelope)
      (defectNorm0 envelope) (defectNorm1 envelope)
      (defectNorm2 envelope) (defectNorm3 envelope)
      (scaledWeightNonnegative e2 (w0 envelope)
        (epsilonSquareNonnegative envelope) (w0Nonnegative envelope))
      (scaledWeightNonnegative e2 (w1 envelope)
        (epsilonSquareNonnegative envelope) (w1Nonnegative envelope))
      (scaledWeightNonnegative e2 (w2 envelope)
        (epsilonSquareNonnegative envelope) (w2Nonnegative envelope))
      (scaledWeightNonnegative e2 (w3 envelope)
        (epsilonSquareNonnegative envelope) (w3Nonnegative envelope))

    upperExact = quarticUpperExact epsilon
      (w0 envelope) (w1 envelope) (w2 envelope) (w3 envelope)
      left right (weightProductExact envelope)
  in
  subst
    (λ upper → Norm.normSq
      (Telescope.orderedProduct4 f0 f1 f2 f3) ≤ upper)
    upperExact raw

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
deepRemainderLower
    {a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3}
    {epsilon} {left} {right} envelope =
  let
    d0 = Partition.factorDefect a0 b0
    d1 = Partition.factorDefect a1 b1
    d2 = Partition.factorDefect a2 b2
    d3 = Partition.factorDefect a3 b3

    t012 = Telescope.orderedProduct4 d0 d1 d2 b3
    t013 = Telescope.orderedProduct4 d0 d1 b2 d3
    t023 = Telescope.orderedProduct4 d0 b1 d2 d3
    t123 = Telescope.orderedProduct4 b0 d1 d2 d3
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

    rawLower =
      - Scaled.scaledYoungBudget (epsilonCube epsilon) left right
      + (- Scaled.scaledYoungBudget (epsilonCube epsilon) left right
      + (- Scaled.scaledYoungBudget (epsilonCube epsilon) left right
      + (- Scaled.scaledYoungBudget (epsilonCube epsilon) left right
      + - Scaled.scaledYoungBudget (epsilonFourth epsilon) left right)))

    targetLower =
      - ((+ 4 / 1) * epsilonCube epsilon + epsilonFourth epsilon)
        * ((+ 1 / 2) * (left + right))

    rawLowerExact : rawLower ≡ targetLower
    rawLowerExact = ℚRing.solve-∀ epsilon left right

    upperExact :
      Telescope.wilsonScalar
        (Deep.fourFactorDeepRemainder
          a0 a1 a2 a3 b0 b1 b2 b3)
      ≡ Telescope.wilsonScalar t012
        + (Telescope.wilsonScalar t013
        + (Telescope.wilsonScalar t023
        + (Telescope.wilsonScalar t123
        + Telescope.wilsonScalar t0123)))
    upperExact = deepWilsonScalarSumExact t012 t013 t023 t123 t0123
  in
  subst
    (λ upper → targetLower ≤ upper)
    (sym upperExact)
    (subst
      (λ lower → lower
        ≤ Telescope.wilsonScalar t012
          + (Telescope.wilsonScalar t013
          + (Telescope.wilsonScalar t023
          + (Telescope.wilsonScalar t123
          + Telescope.wilsonScalar t0123))))
      rawLowerExact
      summed)

wilsonDeepRemainderEnvelopeLevel : ProofLevel
wilsonDeepRemainderEnvelopeLevel = machineChecked
