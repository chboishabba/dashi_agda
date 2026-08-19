module DASHI.Physics.Closure.NSTriadKNHHViscousVariationCriticalGateRound88Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Finite time blowup for an averaged three-dimensional Navier-Stokes
-- equation".
-- DOI: 10.1090/jams/838.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND88 / REMOVE THE EXTRA COHERENCE OBSERVER
--
-- Write the signed selected HH transfer as
--
--     q = P - N
--
-- with positive and negative masses P,N, and total variation
--
--     A = P + N.
--
-- If the viscous damping magnitude on positive atoms is at least M and on
-- negative atoms is at most C, then the worst signed endpoint is
--
--     R_nu <= - M P + C N.
--
-- Exact algebra rewrites that endpoint as
--
--     - M P + C N
--       = ((C-M)/2) A - ((C+M)/2) q.
--
-- This is the key Round88 compression.  No independent N/P coherence selector
-- is necessary if the existing physical lanes can provide
--
--     A <= K D                 (absolute/Gram variation bound)
--     lambda D <= q            (selected positive critical-transfer event).
--
-- Then
--
--   R_nu <= 1/2 [ (C-M)K - (C+M)lambda ] D.
--
-- Therefore strict viscous coercivity is reduced to the scalar gate
--
--     (C+M) lambda > (C-M) K.
--
-- This is precisely the kind of fine nonlinear information not preserved by a
-- bare energy identity: the absolute transfer mass A and the signed net q must
-- be retained separately until this gate is checked.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _-_; _*_; _≤_; -_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

half : ℚ
half = Int.+ 1 / 2

record SignedVariationViscousBudget : Set where
  constructor signed-variation-viscous-budget
  field
    positiveMass negativeMass : ℚ
    minimumDamping maximumDamping : ℚ
    netViscousContribution : ℚ

    positiveMassNonnegative : 0ℚ ≤ positiveMass
    negativeMassNonnegative : 0ℚ ≤ negativeMass
    minimumDampingNonnegative : 0ℚ ≤ minimumDamping
    maximumDampingNonnegative : 0ℚ ≤ maximumDamping
    dampingOrdered : minimumDamping ≤ maximumDamping

    viscousEndpoint :
      netViscousContribution
      ≤ maximumDamping * negativeMass - minimumDamping * positiveMass

open SignedVariationViscousBudget public

netTransfer : SignedVariationViscousBudget → ℚ
netTransfer budget = positiveMass budget - negativeMass budget

totalVariation : SignedVariationViscousBudget → ℚ
totalVariation budget = positiveMass budget + negativeMass budget

variationNetEndpointIdentity : ∀ budget →
  maximumDamping budget * negativeMass budget
    - minimumDamping budget * positiveMass budget
  ≡
  half * (maximumDamping budget - minimumDamping budget)
      * totalVariation budget
  - half * (maximumDamping budget + minimumDamping budget)
      * netTransfer budget
variationNetEndpointIdentity budget =
  solve
    ( maximumDamping budget
    ∷ minimumDamping budget
    ∷ positiveMass budget
    ∷ negativeMass budget
    ∷ half ∷ [])

record CriticalVariationControl
    (budget : SignedVariationViscousBudget) : Set where
  constructor critical-variation-control
  field
    dissipation variationConstant criticalThreshold : ℚ
    dissipationNonnegative : 0ℚ ≤ dissipation
    variationConstantNonnegative : 0ℚ ≤ variationConstant
    criticalThresholdNonnegative : 0ℚ ≤ criticalThreshold

    totalVariationBelowDissipation :
      totalVariation budget ≤ variationConstant * dissipation
    criticalTransferLower :
      criticalThreshold * dissipation ≤ netTransfer budget

open CriticalVariationControl public

maximumMinusMinimumNonnegative : ∀ budget →
  0ℚ ≤ maximumDamping budget - minimumDamping budget
maximumMinusMinimumNonnegative budget =
  let
    shifted = ℚP.+-mono-≤ (dampingOrdered budget) ℚP.≤-refl
  in
  subst
    (λ left → left ≤ maximumDamping budget - minimumDamping budget)
    (solve (minimumDamping budget ∷ []))
    (subst
      (λ right →
        minimumDamping budget + (- minimumDamping budget) ≤ right)
      (solve (maximumDamping budget ∷ minimumDamping budget ∷ []))
      shifted)

maximumPlusMinimumNonnegative : ∀ budget →
  0ℚ ≤ maximumDamping budget + minimumDamping budget
maximumPlusMinimumNonnegative budget =
  ℚP.+-mono-≤
    (maximumDampingNonnegative budget)
    (minimumDampingNonnegative budget)

halfNonnegative : 0ℚ ≤ half
halfNonnegative = ℚP.0≤⇒0≤[/] (ℚP.0≤1)

variationCoefficientNonnegative : ∀ budget →
  0ℚ ≤ half * (maximumDamping budget - minimumDamping budget)
variationCoefficientNonnegative budget =
  let instance
    halfNNI = nonNegative halfNonnegative
    spreadNNI = nonNegative (maximumMinusMinimumNonnegative budget)
    productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
      half (maximumDamping budget - minimumDamping budget)
  in ℚP.nonNegative⁻¹ _

netCoefficientNonnegative : ∀ budget →
  0ℚ ≤ half * (maximumDamping budget + minimumDamping budget)
netCoefficientNonnegative budget =
  let instance
    halfNNI = nonNegative halfNonnegative
    sumNNI = nonNegative (maximumPlusMinimumNonnegative budget)
    productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
      half (maximumDamping budget + minimumDamping budget)
  in ℚP.nonNegative⁻¹ _

criticalVariationEndpointBound :
  ∀ {budget} (control : CriticalVariationControl budget) →
  netViscousContribution budget
  ≤
  half *
    ((maximumDamping budget - minimumDamping budget)
      * variationConstant control
     - (maximumDamping budget + minimumDamping budget)
      * criticalThreshold control)
    * dissipation control
criticalVariationEndpointBound {budget} control =
  let
    C = maximumDamping budget
    M = minimumDamping budget
    A = totalVariation budget
    q = netTransfer budget
    K = variationConstant control
    lambda = criticalThreshold control
    D = dissipation control
    a = half * (C - M)
    b = half * (C + M)

    endpointToVariationNet :
      netViscousContribution budget ≤ a * A - b * q
    endpointToVariationNet =
      subst
        (λ upper → netViscousContribution budget ≤ upper)
        (variationNetEndpointIdentity budget)
        (viscousEndpoint budget)

    variationScaled : a * A ≤ a * (K * D)
    variationScaled =
      let instance aNNI = nonNegative (variationCoefficientNonnegative budget)
      in ℚP.*-monoˡ-≤-nonNeg a
        (totalVariationBelowDissipation control)

    criticalScaled : b * (lambda * D) ≤ b * q
    criticalScaled =
      let instance bNNI = nonNegative (netCoefficientNonnegative budget)
      in ℚP.*-monoˡ-≤-nonNeg b (criticalTransferLower control)

    negativeCriticalScaled : - (b * q) ≤ - (b * (lambda * D))
    negativeCriticalScaled = ℚP.neg-antimono-≤ criticalScaled

    combined : a * A + (- (b * q))
      ≤ a * (K * D) + (- (b * (lambda * D)))
    combined = ℚP.+-mono-≤ variationScaled negativeCriticalScaled

    endpointMeaning :
      a * (K * D) + (- (b * (lambda * D)))
      ≡ half * ((C - M) * K - (C + M) * lambda) * D
    endpointMeaning = solve (C ∷ M ∷ K ∷ lambda ∷ D ∷ half ∷ [])

    leftMeaning : a * A - b * q ≡ a * A + (- (b * q))
    leftMeaning = solve (a ∷ A ∷ b ∷ q ∷ [])
  in
  ℚP.≤-trans endpointToVariationNet
    (subst
      (λ left → left ≤
        half * ((C - M) * K - (C + M) * lambda) * D)
      (sym leftMeaning)
      (subst
        (λ right → a * A + (- (b * q)) ≤ right)
        endpointMeaning combined))

record StrictCriticalVariationGate
    {budget : SignedVariationViscousBudget}
    (control : CriticalVariationControl budget) : Set where
  constructor strict-critical-variation-gate
  field
    margin : ℚ
    marginNonnegative : 0ℚ ≤ margin
    scalarGate :
      (maximumDamping budget - minimumDamping budget)
          * variationConstant control
        + margin
      ≤ (maximumDamping budget + minimumDamping budget)
          * criticalThreshold control

open StrictCriticalVariationGate public

criticalVariationGateGivesCoerciveViscousBound :
  ∀ {budget} {control : CriticalVariationControl budget} →
  StrictCriticalVariationGate control →
  netViscousContribution budget
  ≤ - (half * margin _ * dissipation control)
criticalVariationGateGivesCoerciveViscousBound {budget} {control} gate =
  let
    C = maximumDamping budget
    M = minimumDamping budget
    K = variationConstant control
    lambda = criticalThreshold control
    D = dissipation control
    delta = margin gate

    base = criticalVariationEndpointBound control

    shifted = ℚP.+-mono-≤ (scalarGate gate) ℚP.≤-refl

    coefficientGate :
      (C - M) * K - (C + M) * lambda ≤ - delta
    coefficientGate =
      subst
        (λ left → left ≤ - delta)
        (solve (C ∷ M ∷ K ∷ lambda ∷ delta ∷ []))
        (subst
          (λ right →
            ((C - M) * K + delta) + (- ((C + M) * lambda))
            ≤ right)
          (solve (C ∷ M ∷ K ∷ lambda ∷ []))
          shifted)

    halfScaled :
      half * ((C - M) * K - (C + M) * lambda)
      ≤ half * (- delta)
    halfScaled =
      let instance halfNNI = nonNegative halfNonnegative
      in ℚP.*-monoˡ-≤-nonNeg half coefficientGate

    dissipationScaled :
      (half * ((C - M) * K - (C + M) * lambda)) * D
      ≤ (half * (- delta)) * D
    dissipationScaled =
      let instance dNNI = nonNegative (dissipationNonnegative control)
      in ℚP.*-monoʳ-≤-nonNeg D halfScaled

    endpoint : (half * (- delta)) * D ≡ - (half * delta * D)
    endpoint = solve (half ∷ delta ∷ D ∷ [])
  in
  ℚP.≤-trans base
    (subst
      (λ upper →
        half * ((C - M) * K - (C + M) * lambda) * D ≤ upper)
      endpoint dissipationScaled)

round88SignedCoherenceCanBeReplacedByVariationCriticalGate : Bool
round88SignedCoherenceCanBeReplacedByVariationCriticalGate = true

round88D1AbsoluteMassCanDirectlyFundHHViscousCoherence : Bool
round88D1AbsoluteMassCanDirectlyFundHHViscousCoherence = true

round88SignedCoherenceCanBeReplacedByVariationCriticalGateIsTrue :
  round88SignedCoherenceCanBeReplacedByVariationCriticalGate ≡ true
round88SignedCoherenceCanBeReplacedByVariationCriticalGateIsTrue = refl
