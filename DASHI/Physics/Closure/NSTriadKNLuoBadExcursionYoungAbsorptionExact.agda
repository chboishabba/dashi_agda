module DASHI.Physics.Closure.NSTriadKNLuoBadExcursionYoungAbsorptionExact where

------------------------------------------------------------------------
-- PRIMARY CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- Author: Runlong Yu.
-- Title: "A Structural Audit of Navier-Stokes Obstruction Calculus".
-- DOI: 10.48550/arXiv.2606.25341.
--
-- DASHI CONTRIBUTION
--
-- This module closes the exact K9--K10 coefficient algebra.  The scaled Young
-- inequality is proved from the polynomial factorization
--
--   epsilon x^2 + q y^2 - x y
--     = q (2 epsilon x-y)^2,
--
-- under the division-free normalization 4 epsilon q = 1.  A bad-transfer
-- product bound, a defect-square diffusion budget, and an amplitude-square
-- diffusion budget then imply an explicit strict bad-lane coefficient:
--
--   T_bad
--     <= (epsilon c_A + c_M) V
--        + epsilon R_A + R_M + R_0.
--
-- The theorem does not assume that a small bad-set measure alone controls the
-- transfer.  Both defect and amplitude factors must be taxed.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

addSameRight :
  ∀ {left upper} right →
  left ≤ upper →
  left + right ≤ upper + right
addSameRight {left} {upper} right inequality =
  let
    raw : right + left ≤ right + upper
    raw = ℚₚ.+-monoʳ-≤ right inequality
  in
  subst
    (λ normalizedLeft → normalizedLeft ≤ upper + right)
    (solve (right ∷ left ∷ []))
    (subst
      (λ normalizedRight → right + left ≤ normalizedRight)
      (solve (right ∷ upper ∷ []))
      raw)

record QuarterYoungParameter : Set where
  constructor quarterYoungParameter
  field
    epsilon quarterInverse : ℚ
    epsilonNonnegative : 0ℚ ≤ epsilon
    quarterInverseNonnegative : 0ℚ ≤ quarterInverse
    quarterInverseLaw :
      4 * epsilon * quarterInverse ≡ 1ℚ

open QuarterYoungParameter public

youngDefect : QuarterYoungParameter → ℚ → ℚ → ℚ
youngDefect parameter x y =
  quarterInverse parameter
  * L2.square (2 * epsilon parameter * x - y)

scaledYoungIdentity :
  ∀ parameter x y →
  epsilon parameter * L2.square x
    + quarterInverse parameter * L2.square y
  ≡ x * y + youngDefect parameter x y
scaledYoungIdentity parameter x y =
  let
    raw :
      epsilon parameter * L2.square x
        + quarterInverse parameter * L2.square y
      ≡
      x * y
      + quarterInverse parameter
        * L2.square (2 * epsilon parameter * x - y)
      +
      (1ℚ - 4 * epsilon parameter * quarterInverse parameter)
        * x * (epsilon parameter * x - y)
    raw =
      solve
        ( epsilon parameter
        ∷ quarterInverse parameter
        ∷ x ∷ y ∷ [])

    normalization :
      1ℚ - 4 * epsilon parameter * quarterInverse parameter ≡ 0ℚ
    normalization
      rewrite quarterInverseLaw parameter =
      solve []

    withZero :
      epsilon parameter * L2.square x
        + quarterInverse parameter * L2.square y
      ≡
      x * y + youngDefect parameter x y
        + 0ℚ * x * (epsilon parameter * x - y)
    withZero =
      subst
        (λ zeroTerm →
          epsilon parameter * L2.square x
            + quarterInverse parameter * L2.square y
          ≡ x * y + youngDefect parameter x y
            + zeroTerm * x * (epsilon parameter * x - y))
        normalization
        raw
  in
  trans
    withZero
    (solve
      ( x ∷ y ∷ epsilon parameter
      ∷ youngDefect parameter x y ∷ []))

scaledYoungProductBound :
  ∀ parameter x y →
  x * y
  ≤ epsilon parameter * L2.square x
    + quarterInverse parameter * L2.square y
scaledYoungProductBound parameter x y =
  let
    defectNonnegative :
      0ℚ ≤ youngDefect parameter x y
    defectNonnegative =
      let
        instance
          inverseNN =
            nonNegative (quarterInverseNonnegative parameter)
          squareNN =
            nonNegative
              (L2.squareNonnegative
                (2 * epsilon parameter * x - y))
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (quarterInverse parameter)
              (L2.square (2 * epsilon parameter * x - y))
      in
      ℚₚ.nonNegative⁻¹ (youngDefect parameter x y)

    addDefect : x * y + 0ℚ ≤ x * y + youngDefect parameter x y
    addDefect = ℚₚ.+-monoʳ-≤ (x * y) defectNonnegative

    leftClosed : x * y + 0ℚ ≡ x * y
    leftClosed = solve (x ∷ y ∷ [])

    normalized :
      x * y ≤ x * y + youngDefect parameter x y
    normalized =
      subst
        (λ left → left ≤ x * y + youngDefect parameter x y)
        leftClosed
        addDefect
  in
  subst
    (λ upper → x * y ≤ upper)
    (sym (scaledYoungIdentity parameter x y))
    normalized

record BadExcursionAmplitudeBudget
    (parameter : QuarterYoungParameter) : Set where
  constructor badExcursionAmplitudeBudget
  field
    defectFactor amplitudeFactor transfer viscosity : ℚ
    transferResidual defectResidual amplitudeResidual : ℚ
    defectCoefficient amplitudeCoefficient : ℚ

    defectFactorNonnegative : 0ℚ ≤ defectFactor
    amplitudeFactorNonnegative : 0ℚ ≤ amplitudeFactor
    transferNonnegative : 0ℚ ≤ transfer
    viscosityNonnegative : 0ℚ ≤ viscosity
    transferResidualNonnegative : 0ℚ ≤ transferResidual
    defectResidualNonnegative : 0ℚ ≤ defectResidual
    amplitudeResidualNonnegative : 0ℚ ≤ amplitudeResidual
    defectCoefficientNonnegative : 0ℚ ≤ defectCoefficient
    amplitudeCoefficientNonnegative : 0ℚ ≤ amplitudeCoefficient

    badTransferProductBound :
      transfer ≤ defectFactor * amplitudeFactor + transferResidual

    defectSquareBudget :
      L2.square defectFactor
      ≤ defectCoefficient * viscosity + defectResidual

    amplitudeSquareBudget :
      quarterInverse parameter * L2.square amplitudeFactor
      ≤ amplitudeCoefficient * viscosity + amplitudeResidual

open BadExcursionAmplitudeBudget public

badAbsorptionCoefficient :
  ∀ {parameter} →
  BadExcursionAmplitudeBudget parameter → ℚ
badAbsorptionCoefficient {parameter} budget =
  epsilon parameter * defectCoefficient budget
  + amplitudeCoefficient budget

badAbsorptionResidual :
  ∀ {parameter} →
  BadExcursionAmplitudeBudget parameter → ℚ
badAbsorptionResidual {parameter} budget =
  epsilon parameter * defectResidual budget
  + amplitudeResidual budget
  + transferResidual budget

defectBudgetAfterEpsilon :
  ∀ {parameter}
    (budget : BadExcursionAmplitudeBudget parameter) →
  epsilon parameter * L2.square (defectFactor budget)
  ≤
  epsilon parameter
    * (defectCoefficient budget * viscosity budget
      + defectResidual budget)
defectBudgetAfterEpsilon {parameter} budget =
  L2.nonnegativeProductMonotone
    (epsilonNonnegative parameter)
    (L2.squareNonnegative (defectFactor budget))
    (epsilonNonnegative parameter)
    upperNonnegative
    ℚₚ.≤-refl
    (defectSquareBudget budget)
  where
  upperNonnegative :
    0ℚ ≤ defectCoefficient budget * viscosity budget
      + defectResidual budget
  upperNonnegative =
    L2.addNonnegative productNonnegative (defectResidualNonnegative budget)
    where
    productNonnegative :
      0ℚ ≤ defectCoefficient budget * viscosity budget
    productNonnegative =
      let
        instance
          coefficientNN =
            nonNegative (defectCoefficientNonnegative budget)
          viscosityNN = nonNegative (viscosityNonnegative budget)
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (defectCoefficient budget) (viscosity budget)
      in
      ℚₚ.nonNegative⁻¹
        (defectCoefficient budget * viscosity budget)

badExcursionAmplitudeAbsorption :
  ∀ {parameter}
    (budget : BadExcursionAmplitudeBudget parameter) →
  transfer budget
  ≤ badAbsorptionCoefficient budget * viscosity budget
    + badAbsorptionResidual budget
badExcursionAmplitudeAbsorption {parameter} budget =
  let
    young =
      scaledYoungProductBound
        parameter
        (defectFactor budget)
        (amplitudeFactor budget)

    youngPlusResidual :
      defectFactor budget * amplitudeFactor budget
        + transferResidual budget
      ≤
      (epsilon parameter * L2.square (defectFactor budget)
        + quarterInverse parameter * L2.square (amplitudeFactor budget))
      + transferResidual budget
    youngPlusResidual = addSameRight (transferResidual budget) young

    transferToYoung :
      transfer budget
      ≤
      (epsilon parameter * L2.square (defectFactor budget)
        + quarterInverse parameter * L2.square (amplitudeFactor budget))
      + transferResidual budget
    transferToYoung =
      ℚₚ.≤-trans
        (badTransferProductBound budget)
        youngPlusResidual

    defectScaled = defectBudgetAfterEpsilon budget
    amplitudeScaled = amplitudeSquareBudget budget

    budgetsCombined :
      epsilon parameter * L2.square (defectFactor budget)
        + quarterInverse parameter * L2.square (amplitudeFactor budget)
      ≤
      epsilon parameter
        * (defectCoefficient budget * viscosity budget
          + defectResidual budget)
      +
      (amplitudeCoefficient budget * viscosity budget
        + amplitudeResidual budget)
    budgetsCombined = ℚₚ.+-mono-≤ defectScaled amplitudeScaled

    withTransferResidual :
      (epsilon parameter * L2.square (defectFactor budget)
        + quarterInverse parameter * L2.square (amplitudeFactor budget))
      + transferResidual budget
      ≤
      (epsilon parameter
        * (defectCoefficient budget * viscosity budget
          + defectResidual budget)
        +
        (amplitudeCoefficient budget * viscosity budget
          + amplitudeResidual budget))
      + transferResidual budget
    withTransferResidual = addSameRight (transferResidual budget) budgetsCombined

    targetMeaning :
      (epsilon parameter
        * (defectCoefficient budget * viscosity budget
          + defectResidual budget)
        +
        (amplitudeCoefficient budget * viscosity budget
          + amplitudeResidual budget))
      + transferResidual budget
      ≡
      badAbsorptionCoefficient budget * viscosity budget
        + badAbsorptionResidual budget
    targetMeaning =
      solve
        ( epsilon parameter
        ∷ defectCoefficient budget
        ∷ amplitudeCoefficient budget
        ∷ viscosity budget
        ∷ defectResidual budget
        ∷ amplitudeResidual budget
        ∷ transferResidual budget
        ∷ [])
  in
  ℚₚ.≤-trans
    transferToYoung
    (subst
      (λ upper →
        (epsilon parameter * L2.square (defectFactor budget)
          + quarterInverse parameter * L2.square (amplitudeFactor budget))
        + transferResidual budget
        ≤ upper)
      targetMeaning
      withTransferResidual)

record BadExcursionAbsorptionAuthorityBoundary : Set where
  constructor badExcursionAbsorptionAuthorityBoundary
  field
    scaledYoungFactorizationProved : Set
    twoFactorBadAbsorptionAlgebraProved : Set
    physicalDefectSquareBudgetProduced : Set
    physicalAmplitudeSquareBudgetProduced : Set

canonicalBadExcursionAbsorptionAuthorityBoundary :
  BadExcursionAbsorptionAuthorityBoundary
canonicalBadExcursionAbsorptionAuthorityBoundary =
  badExcursionAbsorptionAuthorityBoundary ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
