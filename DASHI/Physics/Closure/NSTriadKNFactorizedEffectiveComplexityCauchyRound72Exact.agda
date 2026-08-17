module DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND72 CONTRIBUTION
--
-- Round71 applied Cauchy to (a_tau,1), forcing the second squared norm to be
-- literal atom count.  The correct high-alpha generalisation is already latent
-- in the repository's finite Gram theorem: factor each signed contribution as
--
--      a_tau = x_tau y_tau.
--
-- Then
--
--      (sum a_tau)^2
--        <= (sum x_tau^2) (sum y_tau^2).
--
-- Interpret the first factor as concentration charge and the second as
-- EFFECTIVE COMPLEXITY.  No square roots or division are required.  A later
-- physical theorem may choose y_tau from low-leg energy, shell mass, dominant-
-- hat self-mass, dissipation, or a normalized Gram factor.
--
-- This strictly subsumes raw cardinality: y_tau=1 recovers #atoms.  More
-- importantly, if the physical effective complexity is bounded by W, then
--
--      mu^2 <= concentrationCharge * W
--
-- for every same-object remainder lower bound mu.  Thus Round72 turns the
-- controlled-subfibre problem into a concrete factorisation/weight problem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record FactorizedContribution : Set where
  constructor factorized-contribution
  field
    leftFactor : ℚ
    rightFactor : ℚ

open FactorizedContribution public

asPair : FactorizedContribution → L2.Pair
asPair contribution = leftFactor contribution , rightFactor contribution

factorPairs : List FactorizedContribution → List L2.Pair
factorPairs [] = []
factorPairs (head ∷ rest) = asPair head ∷ factorPairs rest

factorizedSignedSum : List FactorizedContribution → ℚ
factorizedSignedSum factors = L2.pairDot (factorPairs factors)

concentrationCharge : List FactorizedContribution → ℚ
concentrationCharge factors = L2.leftNormSquared (factorPairs factors)

effectiveComplexity : List FactorizedContribution → ℚ
effectiveComplexity factors = L2.rightNormSquared (factorPairs factors)

factorizedCauchy : ∀ factors →
  L2.square (factorizedSignedSum factors)
  ≤ concentrationCharge factors * effectiveComplexity factors
factorizedCauchy factors = L2.finiteCauchySchwarzSquared (factorPairs factors)

concentrationChargeNonnegative : ∀ factors →
  0ℚ ≤ concentrationCharge factors
concentrationChargeNonnegative factors =
  L2.leftNormSquaredNonnegative (factorPairs factors)

effectiveComplexityNonnegative : ∀ factors →
  0ℚ ≤ effectiveComplexity factors
effectiveComplexityNonnegative factors =
  L2.rightNormSquaredNonnegative (factorPairs factors)

record SameObjectFactorizedRemainder
    (factors : List FactorizedContribution)
    (remainder mu : ℚ) : Set where
  field
    muNonnegative : 0ℚ ≤ mu
    muBelowRemainder : mu ≤ remainder
    remainderExact : remainder ≡ factorizedSignedSum factors

open SameObjectFactorizedRemainder public

factorizedRemainderForcesChargeTimesComplexity :
  ∀ {factors remainder mu} →
  SameObjectFactorizedRemainder factors remainder mu →
  L2.square mu
  ≤ concentrationCharge factors * effectiveComplexity factors
factorizedRemainderForcesChargeTimesComplexity
    {factors} {remainder} {mu} witness =
  let
    sumNN : 0ℚ ≤ factorizedSignedSum factors
    sumNN = subst (0ℚ ≤_)
      (remainderExact witness)
      (ℚP.≤-trans (muNonnegative witness) (muBelowRemainder witness))

    muBelowSum : mu ≤ factorizedSignedSum factors
    muBelowSum = subst (mu ≤_)
      (remainderExact witness)
      (muBelowRemainder witness)
  in
  ℚP.≤-trans
    (L2.nonnegativeProductMonotone
      (muNonnegative witness) (muNonnegative witness)
      sumNN sumNN muBelowSum muBelowSum)
    (factorizedCauchy factors)

record EffectiveComplexityBudget
    (factors : List FactorizedContribution)
    (budget : ℚ) : Set where
  field
    budgetNonnegative : 0ℚ ≤ budget
    complexityBelowBudget : effectiveComplexity factors ≤ budget

open EffectiveComplexityBudget public

factorizedRemainderForcesChargeTimesBudget :
  ∀ {factors remainder mu budget} →
  SameObjectFactorizedRemainder factors remainder mu →
  EffectiveComplexityBudget factors budget →
  L2.square mu ≤ concentrationCharge factors * budget
factorizedRemainderForcesChargeTimesBudget
    {factors} remainderWitness budgetWitness =
  ℚP.≤-trans
    (factorizedRemainderForcesChargeTimesComplexity remainderWitness)
    (L2.nonnegativeProductMonotone
      (concentrationChargeNonnegative factors)
      (effectiveComplexityNonnegative factors)
      (concentrationChargeNonnegative factors)
      (budgetNonnegative budgetWitness)
      ℚP.≤-refl
      (complexityBelowBudget budgetWitness))

unitFactorization : List ℚ → List FactorizedContribution
unitFactorization [] = []
unitFactorization (value ∷ rest) =
  factorized-contribution value 1ℚ ∷ unitFactorization rest

unitFactorizationEffectiveComplexity : List ℚ → ℚ
unitFactorizationEffectiveComplexity values =
  effectiveComplexity (unitFactorization values)

round72FactorizedEffectiveComplexityCauchyConstructed : Bool
round72FactorizedEffectiveComplexityCauchyConstructed = true

round72RawCardinalityIsOnlyUnitWeightSpecialCase : Bool
round72RawCardinalityIsOnlyUnitWeightSpecialCase = true

round72PhysicalEnergyOrGramFactorizationConstructed : Bool
round72PhysicalEnergyOrGramFactorizationConstructed = false

round72FactorizedEffectiveComplexityCauchyConstructedIsTrue :
  round72FactorizedEffectiveComplexityCauchyConstructed ≡ true
round72FactorizedEffectiveComplexityCauchyConstructedIsTrue = refl

round72PhysicalEnergyOrGramFactorizationConstructedIsFalse :
  round72PhysicalEnergyOrGramFactorizationConstructed ≡ false
round72PhysicalEnergyOrGramFactorizationConstructedIsFalse = refl
