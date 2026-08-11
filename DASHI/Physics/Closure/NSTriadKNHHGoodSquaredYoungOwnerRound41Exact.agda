module DASHI.Physics.Closure.NSTriadKNHHGoodSquaredYoungOwnerRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 40 reduced the HH-good shell estimate to the exact squared form
--
--   P^2 <= C_strain delta W.
--
-- The attached continuation suggested that if the physical local mass has the
-- critical factorization W <= X D, then Young should close the owner.  This
-- file proves that implication *without introducing square roots*.
--
-- For every positive epsilon with exact inverse epsilon^-1,
--
--   P^2 <= K X D,
--   K = C_strain delta,
--
-- implies
--
--   P <= epsilon D + (K / (4 epsilon)) X.
--
-- The key square-root-free identity is
--
--   K X D <= (epsilon D + K X/(4 epsilon))^2,
--
-- followed by exact reflection of square order on rational scalars.  Thus the
-- formerly vague `physicalHHGoodTimeDissipationAbsorption` is not a separate
-- analytic theorem once W <= X D is established.  The remaining physical
-- HH-good seams are the literal annular strain-kernel realization, sample-mass
-- identification, and this local-mass factorization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; _≤_
  ; NonNegative; NonZero; Positive; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≡?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact as Good
import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact as Periodized

quarter four : ℚ
quarter = Int.+ 1 / 4
four = Int.+ 4 / 1

multiplyNonnegative : ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
multiplyNonnegative {left} {right} leftNN rightNN =
  let
    instance
      leftNNI = nonNegative leftNN
      rightNNI = nonNegative rightNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚP.nonNegative⁻¹ (left * right)

nonnegativeSquareReflectsOrder :
  ∀ x bound →
  0ℚ ≤ x → 0ℚ ≤ bound →
  x * x ≤ bound * bound →
  x ≤ bound
nonnegativeSquareReflectsOrder x bound xNN boundNN squares
  with ℚP.≤-total x bound
... | inj₁ x≤bound = x≤bound
... | inj₂ bound≤x with x ≡? 0ℚ
...   | yes xZero =
  subst (λ selected → selected ≤ bound) (sym xZero) boundNN
...   | no xNonzero =
  let
    instance
      xNonnegative : NonNegative x
      xNonnegative = ℚ.nonNegative xNN

      boundNonnegative : NonNegative bound
      boundNonnegative = ℚ.nonNegative boundNN

      xNonZero : NonZero x
      xNonZero = ℚ.≢-nonZero xNonzero

      xPositive : Positive x
      xPositive = ℚP.nonNeg∧nonZero⇒pos x

    boundSquareBelowBoundX : bound * bound ≤ bound * x
    boundSquareBelowBoundX =
      ℚP.*-monoˡ-≤-nonNeg bound bound≤x

    xSquareBelowBoundX : x * x ≤ bound * x
    xSquareBelowBoundX =
      ℚP.≤-trans squares boundSquareBelowBoundX
  in
  ℚP.*-cancelʳ-≤-pos x xSquareBelowBoundX

squareBoundWithNonnegativeUpperImpliesUpper :
  ∀ scalar bound →
  0ℚ ≤ bound →
  scalar * scalar ≤ bound * bound →
  scalar ≤ bound
squareBoundWithNonnegativeUpperImpliesUpper scalar bound boundNN squareBound
  with ℚP.≤-total scalar 0ℚ
... | inj₁ scalar≤zero = ℚP.≤-trans scalar≤zero boundNN
... | inj₂ zero≤scalar =
  nonnegativeSquareReflectsOrder
    scalar bound zero≤scalar boundNN squareBound

fourProductBelowSquareSum : ∀ left right →
  four * left * right ≤ L2.square (left + right)
fourProductBelowSquareSum left right =
  let
    gapNN = L2.squareNonnegative (left - right)
    base :
      four * left * right + 0ℚ
      ≤ four * left * right + L2.square (left - right)
    base = ℚP.+-monoʳ-≤ (four * left * right) gapNN

    leftMeaning :
      four * left * right + 0ℚ ≡ four * left * right
    leftMeaning = solve (left ∷ right ∷ [])

    rightMeaning :
      four * left * right + L2.square (left - right)
      ≡ L2.square (left + right)
    rightMeaning = solve (left ∷ right ∷ [])
  in
  subst
    (λ lower → lower ≤ L2.square (left + right))
    leftMeaning
    (subst
      (λ upper → four * left * right + 0ℚ ≤ upper)
      rightMeaning
      base)

kernelThresholdFactor :
  ℚ → Threshold.PositiveThreshold → ℚ
kernelThresholdFactor kernelConstant parameter =
  kernelConstant * Threshold.threshold parameter

youngCriticalCoefficient :
  Threshold.PositiveThreshold → ℚ → Threshold.PositiveThreshold → ℚ
youngCriticalCoefficient viscositySplit kernelConstant parameter =
  quarter
  * Threshold.thresholdInverse viscositySplit
  * kernelThresholdFactor kernelConstant parameter

youngUpper :
  Threshold.PositiveThreshold → ℚ → Threshold.PositiveThreshold →
  ℚ → ℚ → ℚ
youngUpper viscositySplit kernelConstant parameter critical dissipation =
  Threshold.threshold viscositySplit * dissipation
  + youngCriticalCoefficient viscositySplit kernelConstant parameter * critical

youngUpperNonnegative :
  ∀ viscositySplit kernelConstant parameter critical dissipation →
  0ℚ ≤ kernelConstant →
  0ℚ ≤ critical →
  0ℚ ≤ dissipation →
  0ℚ ≤ youngUpper
      viscositySplit kernelConstant parameter critical dissipation
youngUpperNonnegative viscositySplit kernelConstant parameter
    critical dissipation kernelNN criticalNN dissNN =
  let
    epsilonNN = Threshold.thresholdNonnegative viscositySplit
    epsilonInvNN = Threshold.thresholdInverseNonnegative viscositySplit
    deltaNN = Threshold.thresholdNonnegative parameter
    quarterNN : 0ℚ ≤ quarter
    quarterNN = ℚP.nonNegative⁻¹ quarter

    kNN = multiplyNonnegative kernelNN deltaNN
    coeffNN = multiplyNonnegative
      (multiplyNonnegative quarterNN epsilonInvNN) kNN
  in
  L2.addNonnegative
    (multiplyNonnegative epsilonNN dissNN)
    (multiplyNonnegative coeffNN criticalNN)

youngFactorProductExact :
  ∀ viscositySplit kernelConstant parameter critical dissipation →
  four
    * (Threshold.threshold viscositySplit * dissipation)
    * (youngCriticalCoefficient viscositySplit kernelConstant parameter
        * critical)
  ≡ kernelThresholdFactor kernelConstant parameter
      * critical * dissipation
youngFactorProductExact viscositySplit kernelConstant parameter
    critical dissipation =
  let
    epsilon = Threshold.threshold viscositySplit
    epsilonInv = Threshold.thresholdInverse viscositySplit
    K = kernelThresholdFactor kernelConstant parameter

    regroup :
      four * (epsilon * dissipation)
        * ((quarter * epsilonInv * K) * critical)
      ≡ (epsilonInv * epsilon) * K * critical * dissipation
    regroup = solve
      (epsilon ∷ epsilonInv ∷ K ∷ critical ∷ dissipation ∷ [])
  in
  trans regroup
    (trans
      (cong (λ reciprocal → reciprocal * K * critical * dissipation)
        (Threshold.inverseMeaning viscositySplit))
      (solve (K ∷ critical ∷ dissipation ∷ [])))

kernelCriticalDissipationBelowYoungSquare :
  ∀ viscositySplit kernelConstant parameter critical dissipation →
  kernelThresholdFactor kernelConstant parameter * critical * dissipation
  ≤ L2.square
      (youngUpper viscositySplit kernelConstant parameter critical dissipation)
kernelCriticalDissipationBelowYoungSquare viscositySplit kernelConstant
    parameter critical dissipation =
  let
    left = Threshold.threshold viscositySplit * dissipation
    right = youngCriticalCoefficient viscositySplit kernelConstant parameter
      * critical
    generic = fourProductBelowSquareSum left right
  in
  subst
    (λ lower →
      lower
      ≤ L2.square
          (youngUpper viscositySplit kernelConstant parameter
            critical dissipation))
    (sym (youngFactorProductExact viscositySplit kernelConstant parameter
      critical dissipation))
    generic

record HHGoodSquaredYoungInput
    (environment : Owner.TaxEnvironment)
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    positiveProduction : ℚ
    kernelConstant : ℚ
    weightedLocalMass : ℚ
    viscositySplit : Threshold.PositiveThreshold

    kernelConstantNonnegative : 0ℚ ≤ kernelConstant
    weightedLocalMassNonnegative : 0ℚ ≤ weightedLocalMass
    criticalNonnegative : 0ℚ ≤ Owner.integralCritical environment
    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment

    squaredProductionBound :
      L2.square positiveProduction
      ≤ kernelConstant
          * (Threshold.threshold parameter * weightedLocalMass)

    localMassBelowCriticalTimesDissipation :
      weightedLocalMass
      ≤ Owner.integralCritical environment * Owner.dissipation environment

open HHGoodSquaredYoungInput public

hhGoodSquaredYoungAbsorption :
  ∀ {environment parameter}
    (input : HHGoodSquaredYoungInput environment parameter) →
  positiveProduction input
  ≤ Threshold.threshold (viscositySplit input)
      * Owner.dissipation environment
    + youngCriticalCoefficient
        (viscositySplit input) (kernelConstant input) parameter
        * Owner.integralCritical environment
hhGoodSquaredYoungAbsorption {environment} {parameter} input =
  let
    K = kernelThresholdFactor (kernelConstant input) parameter
    critical = Owner.integralCritical environment
    dissipation = Owner.dissipation environment

    KNN = multiplyNonnegative
      (kernelConstantNonnegative input)
      (Threshold.thresholdNonnegative parameter)

    localScaled :
      K * weightedLocalMass input
      ≤ K * (critical * dissipation)
    localScaled =
      let instance KNNI = nonNegative KNN
      in ℚP.*-monoˡ-≤-nonNeg K
        (localMassBelowCriticalTimesDissipation input)

    squareToProduct :
      L2.square (positiveProduction input)
      ≤ K * critical * dissipation
    squareToProduct =
      ℚP.≤-trans
        (subst
          (λ upper → L2.square (positiveProduction input) ≤ upper)
          (solve
            ( kernelConstant input
            ∷ Threshold.threshold parameter
            ∷ weightedLocalMass input
            ∷ []))
          (squaredProductionBound input))
        (subst
          (λ upper → K * weightedLocalMass input ≤ upper)
          (solve (K ∷ critical ∷ dissipation ∷ []))
          localScaled)

    productToYoungSquare =
      kernelCriticalDissipationBelowYoungSquare
        (viscositySplit input) (kernelConstant input) parameter
        critical dissipation

    squareToYoungSquare = ℚP.≤-trans squareToProduct productToYoungSquare

    youngNN = youngUpperNonnegative
      (viscositySplit input) (kernelConstant input) parameter
      critical dissipation
      (kernelConstantNonnegative input)
      (criticalNonnegative input)
      (dissipationNonnegative input)
  in
  squareBoundWithNonnegativeUpperImpliesUpper
    (positiveProduction input)
    (youngUpper (viscositySplit input) (kernelConstant input) parameter
      critical dissipation)
    youngNN
    squareToYoungSquare

hhGoodOwnerFromSquaredYoung :
  ∀ {environment parameter} →
  HHGoodSquaredYoungInput environment parameter →
  Owner.AdmissibleOwnerEstimate environment
hhGoodOwnerFromSquaredYoung {environment} {parameter} input =
  Owner.admissible-owner-estimate
    Tax.HH-good
    (positiveProduction input)
    (Threshold.threshold (viscositySplit input))
    0ℚ
    (youngCriticalCoefficient
      (viscositySplit input) (kernelConstant input) parameter)
    ownerBound
  where
  ownerBound :
    positiveProduction input
    ≤ Threshold.threshold (viscositySplit input)
        * Owner.dissipation environment
      + 0ℚ
      + youngCriticalCoefficient
          (viscositySplit input) (kernelConstant input) parameter
          * Owner.integralCritical environment
  ownerBound =
    subst
      (λ upper → positiveProduction input ≤ upper)
      (sym (solve
        ( Threshold.threshold (viscositySplit input)
        ∷ Owner.dissipation environment
        ∷ youngCriticalCoefficient
            (viscositySplit input) (kernelConstant input) parameter
        ∷ Owner.integralCritical environment
        ∷ [])))
      (hhGoodSquaredYoungAbsorption input)

record PeriodizedHHGoodYoungInput
    {st}
    {TorusPoint : Set st}
    (environment : Owner.TaxEnvironment)
    (kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint)
    (shell : Agda.Builtin.Nat.Nat)
    (parameter : Threshold.PositiveThreshold)
    (samples : Agda.Builtin.List.List (Good.HHGoodKernelSample parameter)) : Set where
  field
    identification :
      Periodized.PhysicalStrainShellKernelMassIdentification
        kernelTheorem shell parameter samples
    viscositySplit : Threshold.PositiveThreshold
    criticalNonnegative : 0ℚ ≤ Owner.integralCritical environment
    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment
    localMassBelowCriticalTimesDissipation :
      Good.weightedLocalMass samples
      ≤ Owner.integralCritical environment * Owner.dissipation environment

open PeriodizedHHGoodYoungInput public

periodizedHHGoodOwnerFromLocalMassFactorization :
  ∀ {st} {TorusPoint : Set st}
    {environment kernelTheorem shell parameter samples} →
  PeriodizedHHGoodYoungInput
    environment kernelTheorem shell parameter samples →
  Owner.AdmissibleOwnerEstimate environment
periodizedHHGoodOwnerFromLocalMassFactorization
    {kernelTheorem = kernelTheorem}
    {parameter = parameter}
    {samples = samples} physical =
  hhGoodOwnerFromSquaredYoung record
    { positiveProduction = Good.weightedStretch samples
    ; kernelConstant =
        Periodized.masterAnnularStrainKernelL1Norm kernelTheorem
    ; weightedLocalMass = Good.weightedLocalMass samples
    ; viscositySplit = viscositySplit physical
    ; kernelConstantNonnegative =
        Periodized.masterAnnularStrainKernelL1Nonnegative kernelTheorem
    ; weightedLocalMassNonnegative = Good.weightedLocalMassNonnegative samples
    ; criticalNonnegative = criticalNonnegative physical
    ; dissipationNonnegative = dissipationNonnegative physical
    ; squaredProductionBound =
        Periodized.periodizedHHGoodShellBound (identification physical)
    ; localMassBelowCriticalTimesDissipation =
        localMassBelowCriticalTimesDissipation physical
    }

hhGoodSquaredYoungOwnerReductionClosed : Bool
hhGoodSquaredYoungOwnerReductionClosed = true

physicalHHGoodWeightedLocalMassFactorizationConstructed : Bool
physicalHHGoodWeightedLocalMassFactorizationConstructed = false

physicalHHGoodTimeDissipationAbsorptionNoLongerIndependent : Bool
physicalHHGoodTimeDissipationAbsorptionNoLongerIndependent = true

hhGoodSquaredYoungOwnerReductionClosedIsTrue :
  hhGoodSquaredYoungOwnerReductionClosed ≡ true
hhGoodSquaredYoungOwnerReductionClosedIsTrue = refl
