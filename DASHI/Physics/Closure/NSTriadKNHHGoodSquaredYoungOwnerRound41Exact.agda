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
-- Round 40 reduced the HH-good shell estimate to
--
--   P^2 <= C_strain delta W.
--
-- A tempting Round-41 shortcut was W <= X D.  The companion scaling-no-go
-- module rejects that as a universal arbitrary-data bound: Round 38's literal
-- local weight a^2 b^4 is degree six in amplitude whereas X D is only degree
-- four.  The scale-compatible correction retains one additional quadratic
-- resource E0, intended to be the data-controlled L2 energy (or an equivalent
-- already-controlled amplitude factor):
--
--   W <= E0 X D.
--
-- This file proves the remaining Young algebra without square roots.  For
-- every positive epsilon,
--
--   P <= epsilon D
--        + [ C_strain delta E0 / (4 epsilon) ] X.
--
-- Thus the physical HH-good problem is sharpened to proving a data-weighted
-- local-mass factorization, not the false raw W <= X D shortcut.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _/_; _+_; _-_; _*_; _≤_
  ; NonNegative; NonZero; Positive; nonNegative)
import Data.Rational.Properties as ℚP
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
... | inj₂ bound≤x with ℚP._≡?_ x 0ℚ
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
  nonnegativeSquareReflectsOrder scalar bound zero≤scalar boundNN squareBound

fourProductBelowSquareSum : ∀ left right →
  four * left * right ≤ L2.square (left + right)
fourProductBelowSquareSum left right =
  let
    gapNN = L2.squareNonnegative (left - right)
    base :
      four * left * right + 0ℚ
      ≤ four * left * right + L2.square (left - right)
    base = ℚP.+-monoʳ-≤ (four * left * right) gapNN
  in
  subst
    (λ lower → lower ≤ L2.square (left + right))
    (solve (left ∷ right ∷ []))
    (subst
      (λ upper → four * left * right + 0ℚ ≤ upper)
      (solve (left ∷ right ∷ []))
      base)

kernelThresholdFactor :
  ℚ → Threshold.PositiveThreshold → ℚ
kernelThresholdFactor kernelConstant parameter =
  kernelConstant * Threshold.threshold parameter

effectiveKernelConstant : ℚ → ℚ → ℚ
effectiveKernelConstant kernelConstant dataEnergyFactor =
  kernelConstant * dataEnergyFactor

youngCriticalCoefficient :
  Threshold.PositiveThreshold → ℚ → Threshold.PositiveThreshold → ℚ
youngCriticalCoefficient viscositySplit effectiveKernel parameter =
  quarter
  * Threshold.thresholdInverse viscositySplit
  * kernelThresholdFactor effectiveKernel parameter

youngUpper :
  Threshold.PositiveThreshold → ℚ → Threshold.PositiveThreshold →
  ℚ → ℚ → ℚ
youngUpper viscositySplit effectiveKernel parameter critical dissipation =
  Threshold.threshold viscositySplit * dissipation
  + youngCriticalCoefficient viscositySplit effectiveKernel parameter * critical

youngUpperNonnegative :
  ∀ viscositySplit effectiveKernel parameter critical dissipation →
  0ℚ ≤ effectiveKernel →
  0ℚ ≤ critical →
  0ℚ ≤ dissipation →
  0ℚ ≤ youngUpper
      viscositySplit effectiveKernel parameter critical dissipation
youngUpperNonnegative viscositySplit effectiveKernel parameter
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
  ∀ viscositySplit effectiveKernel parameter critical dissipation →
  four
    * (Threshold.threshold viscositySplit * dissipation)
    * (youngCriticalCoefficient viscositySplit effectiveKernel parameter
        * critical)
  ≡ kernelThresholdFactor effectiveKernel parameter
      * critical * dissipation
youngFactorProductExact viscositySplit effectiveKernel parameter
    critical dissipation =
  let
    epsilon = Threshold.threshold viscositySplit
    epsilonInv = Threshold.thresholdInverse viscositySplit
    K = kernelThresholdFactor effectiveKernel parameter

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
  ∀ viscositySplit effectiveKernel parameter critical dissipation →
  kernelThresholdFactor effectiveKernel parameter * critical * dissipation
  ≤ L2.square
      (youngUpper viscositySplit effectiveKernel parameter critical dissipation)
kernelCriticalDissipationBelowYoungSquare viscositySplit effectiveKernel
    parameter critical dissipation =
  let
    left = Threshold.threshold viscositySplit * dissipation
    right = youngCriticalCoefficient viscositySplit effectiveKernel parameter
      * critical
  in
  subst
    (λ lower →
      lower
      ≤ L2.square
          (youngUpper viscositySplit effectiveKernel parameter
            critical dissipation))
    (sym (youngFactorProductExact viscositySplit effectiveKernel parameter
      critical dissipation))
    (fourProductBelowSquareSum left right)

record HHGoodDataEnergyYoungInput
    (environment : Owner.TaxEnvironment)
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    positiveProduction : ℚ
    kernelConstant : ℚ
    weightedLocalMass : ℚ
    dataEnergyFactor : ℚ
    viscositySplit : Threshold.PositiveThreshold

    kernelConstantNonnegative : 0ℚ ≤ kernelConstant
    weightedLocalMassNonnegative : 0ℚ ≤ weightedLocalMass
    dataEnergyFactorNonnegative : 0ℚ ≤ dataEnergyFactor
    criticalNonnegative : 0ℚ ≤ Owner.integralCritical environment
    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment

    squaredProductionBound :
      L2.square positiveProduction
      ≤ kernelConstant
          * (Threshold.threshold parameter * weightedLocalMass)

    localMassBelowDataCriticalDissipation :
      weightedLocalMass
      ≤ dataEnergyFactor
          * Owner.integralCritical environment
          * Owner.dissipation environment

open HHGoodDataEnergyYoungInput public

hhGoodDataEnergyYoungAbsorption :
  ∀ {environment parameter}
    (input : HHGoodDataEnergyYoungInput environment parameter) →
  positiveProduction input
  ≤ Threshold.threshold (viscositySplit input)
      * Owner.dissipation environment
    + youngCriticalCoefficient
        (viscositySplit input)
        (effectiveKernelConstant
          (kernelConstant input) (dataEnergyFactor input))
        parameter
        * Owner.integralCritical environment
hhGoodDataEnergyYoungAbsorption {environment} {parameter} input =
  let
    C = kernelConstant input
    E0 = dataEnergyFactor input
    effective = effectiveKernelConstant C E0
    baseK = kernelThresholdFactor C parameter
    targetK = kernelThresholdFactor effective parameter
    critical = Owner.integralCritical environment
    dissipation = Owner.dissipation environment

    baseKNN = multiplyNonnegative
      (kernelConstantNonnegative input)
      (Threshold.thresholdNonnegative parameter)

    effectiveNN = multiplyNonnegative
      (kernelConstantNonnegative input)
      (dataEnergyFactorNonnegative input)

    localScaled :
      baseK * weightedLocalMass input
      ≤ baseK * (E0 * critical * dissipation)
    localScaled =
      let instance baseKNNI = nonNegative baseKNN
      in ℚP.*-monoˡ-≤-nonNeg baseK
        (localMassBelowDataCriticalDissipation input)

    squareToBase :
      L2.square (positiveProduction input)
      ≤ baseK * weightedLocalMass input
    squareToBase =
      subst
        (λ upper → L2.square (positiveProduction input) ≤ upper)
        (solve
          ( C
          ∷ Threshold.threshold parameter
          ∷ weightedLocalMass input
          ∷ []))
        (squaredProductionBound input)

    normalizedLocal :
      baseK * (E0 * critical * dissipation)
      ≡ targetK * critical * dissipation
    normalizedLocal = solve
      ( C ∷ E0 ∷ Threshold.threshold parameter
      ∷ critical ∷ dissipation ∷ [])

    squareToProduct :
      L2.square (positiveProduction input)
      ≤ targetK * critical * dissipation
    squareToProduct =
      ℚP.≤-trans squareToBase
        (subst
          (λ upper → baseK * weightedLocalMass input ≤ upper)
          normalizedLocal
          localScaled)

    productToYoungSquare =
      kernelCriticalDissipationBelowYoungSquare
        (viscositySplit input) effective parameter critical dissipation

    squareToYoungSquare = ℚP.≤-trans squareToProduct productToYoungSquare

    youngNN = youngUpperNonnegative
      (viscositySplit input) effective parameter critical dissipation
      effectiveNN
      (criticalNonnegative input)
      (dissipationNonnegative input)
  in
  squareBoundWithNonnegativeUpperImpliesUpper
    (positiveProduction input)
    (youngUpper (viscositySplit input) effective parameter critical dissipation)
    youngNN
    squareToYoungSquare

hhGoodOwnerFromDataEnergyYoung :
  ∀ {environment parameter} →
  HHGoodDataEnergyYoungInput environment parameter →
  Owner.AdmissibleOwnerEstimate environment
hhGoodOwnerFromDataEnergyYoung {environment} {parameter} input =
  Owner.admissible-owner-estimate
    Tax.HH-good
    (positiveProduction input)
    (Threshold.threshold (viscositySplit input))
    0ℚ
    (youngCriticalCoefficient
      (viscositySplit input)
      (effectiveKernelConstant
        (kernelConstant input) (dataEnergyFactor input))
      parameter)
    ownerBound
  where
  ownerBound :
    positiveProduction input
    ≤ Threshold.threshold (viscositySplit input)
        * Owner.dissipation environment
      + 0ℚ
      + youngCriticalCoefficient
          (viscositySplit input)
          (effectiveKernelConstant
            (kernelConstant input) (dataEnergyFactor input))
          parameter
          * Owner.integralCritical environment
  ownerBound =
    subst
      (λ upper → positiveProduction input ≤ upper)
      (sym (solve
        ( Threshold.threshold (viscositySplit input)
        ∷ Owner.dissipation environment
        ∷ youngCriticalCoefficient
            (viscositySplit input)
            (effectiveKernelConstant
              (kernelConstant input) (dataEnergyFactor input))
            parameter
        ∷ Owner.integralCritical environment
        ∷ [])))
      (hhGoodDataEnergyYoungAbsorption input)

record PeriodizedHHGoodDataEnergyYoungInput
    {st : Level}
    {TorusPoint : Set st}
    (environment : Owner.TaxEnvironment)
    (kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint)
    (shell : Nat)
    (parameter : Threshold.PositiveThreshold)
    (samples : List (Good.HHGoodKernelSample parameter)) : Set (lsuc st) where
  field
    identification :
      Periodized.PhysicalStrainShellKernelMassIdentification
        kernelTheorem shell parameter samples
    dataEnergyFactor : ℚ
    dataEnergyFactorNonnegative : 0ℚ ≤ dataEnergyFactor
    viscositySplit : Threshold.PositiveThreshold
    criticalNonnegative : 0ℚ ≤ Owner.integralCritical environment
    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment
    localMassBelowDataCriticalDissipation :
      Good.weightedLocalMass samples
      ≤ dataEnergyFactor
          * Owner.integralCritical environment
          * Owner.dissipation environment

open PeriodizedHHGoodDataEnergyYoungInput public

periodizedHHGoodOwnerFromDataEnergyFactorization :
  ∀ {st : Level} {TorusPoint : Set st}
    {environment kernelTheorem shell parameter samples} →
  PeriodizedHHGoodDataEnergyYoungInput
    environment kernelTheorem shell parameter samples →
  Owner.AdmissibleOwnerEstimate environment
periodizedHHGoodOwnerFromDataEnergyFactorization
    {kernelTheorem = kernelTheorem}
    {parameter = parameter}
    {samples = samples} physical =
  hhGoodOwnerFromDataEnergyYoung record
    { positiveProduction = Good.weightedStretch samples
    ; kernelConstant =
        Periodized.masterAnnularStrainKernelL1Norm kernelTheorem
    ; weightedLocalMass = Good.weightedLocalMass samples
    ; dataEnergyFactor = dataEnergyFactor physical
    ; viscositySplit = viscositySplit physical
    ; kernelConstantNonnegative =
        Periodized.masterAnnularStrainKernelL1Nonnegative kernelTheorem
    ; weightedLocalMassNonnegative = Good.weightedLocalMassNonnegative samples
    ; dataEnergyFactorNonnegative = dataEnergyFactorNonnegative physical
    ; criticalNonnegative = criticalNonnegative physical
    ; dissipationNonnegative = dissipationNonnegative physical
    ; squaredProductionBound =
        Periodized.periodizedHHGoodShellBound (identification physical)
    ; localMassBelowDataCriticalDissipation =
        localMassBelowDataCriticalDissipation physical
    }

hhGoodDataEnergyYoungOwnerReductionClosed : Bool
hhGoodDataEnergyYoungOwnerReductionClosed = true

rawHHGoodQuadraticProductShortcutRejected : Bool
rawHHGoodQuadraticProductShortcutRejected = true

physicalHHGoodDataWeightedLocalMassFactorizationConstructed : Bool
physicalHHGoodDataWeightedLocalMassFactorizationConstructed = false

physicalHHGoodTimeDissipationStillRequiresDataEnergyOrEquivalentGain : Bool
physicalHHGoodTimeDissipationStillRequiresDataEnergyOrEquivalentGain = true

hhGoodDataEnergyYoungOwnerReductionClosedIsTrue :
  hhGoodDataEnergyYoungOwnerReductionClosed ≡ true
hhGoodDataEnergyYoungOwnerReductionClosedIsTrue = refl
