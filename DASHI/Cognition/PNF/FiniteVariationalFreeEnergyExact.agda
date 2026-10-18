module DASHI.Cognition.PNF.FiniteVariationalFreeEnergyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans; module ≡-Reasoning)

------------------------------------------------------------------------
-- FINITE VARIATIONAL FREE ENERGY ON A TWO-STATE FIBRE
--
-- Literature calibration:
-- Karl Friston,
-- "The free-energy principle: a unified brain theory?",
-- DOI 10.1038/nrn2787.
--
-- Giovanni Pezzulo; Thomas Parr; Karl Friston,
-- "Active inference as a theory of sentient behavior",
-- DOI 10.1016/j.biopsycho.2023.108741.
--
-- We work with exact rational probability masses and exact surprisal/log-score
-- coordinates supplied by a finite model.  The Boltzmann law is an explicit
-- hypothesis rather than an unproved analytic logarithm implementation.
-- Under that hypothesis we prove the standard finite identity
--
--   KL(q || p) = F(q) + log Z,
--   F(q) = E_q[E] - H(q).
--
-- This is a genuine variational identity, but does not assert Gibbs positivity,
-- continuous-state calculus, or that one functional defines PNF semantics.
------------------------------------------------------------------------

record TwoStateVariationalLaw : Set where
  constructor twoStateVariationalLaw
  field
    q₁ q₂ : ℚ
    posteriorSurprisal₁ posteriorSurprisal₂ : ℚ
    priorSurprisal₁ priorSurprisal₂ : ℚ
    energy₁ energy₂ : ℚ
    logPartition : ℚ
    normalizedQ : q₁ + q₂ ≡ 1ℚ
    priorBoltzmann₁ : priorSurprisal₁ ≡ energy₁ + logPartition
    priorBoltzmann₂ : priorSurprisal₂ ≡ energy₂ + logPartition

open TwoStateVariationalLaw public

entropy : TwoStateVariationalLaw → ℚ
entropy law =
  q₁ law * posteriorSurprisal₁ law
  + q₂ law * posteriorSurprisal₂ law

crossEntropy : TwoStateVariationalLaw → ℚ
crossEntropy law =
  q₁ law * priorSurprisal₁ law
  + q₂ law * priorSurprisal₂ law

expectedEnergy : TwoStateVariationalLaw → ℚ
expectedEnergy law =
  q₁ law * energy₁ law
  + q₂ law * energy₂ law

klDivergence : TwoStateVariationalLaw → ℚ
klDivergence law = crossEntropy law - entropy law

variationalFreeEnergy : TwoStateVariationalLaw → ℚ
variationalFreeEnergy law = expectedEnergy law - entropy law

weightedEnergyExpansion :
  (q₁ q₂ energy₁ energy₂ partition : ℚ) →
  q₁ * (energy₁ + partition) + q₂ * (energy₂ + partition)
    ≡ (q₁ * energy₁ + q₂ * energy₂) + (q₁ + q₂) * partition
weightedEnergyExpansion q₁ q₂ energy₁ energy₂ partition =
  begin
    q₁ * (energy₁ + partition) + q₂ * (energy₂ + partition)
  ≡⟨ cong₂ _+_
      (ℚP.*-distribˡ-+ q₁ energy₁ partition)
      (ℚP.*-distribˡ-+ q₂ energy₂ partition) ⟩
    (q₁ * energy₁ + q₁ * partition) + (q₂ * energy₂ + q₂ * partition)
  ≡⟨ ℚP.+-assoc (q₁ * energy₁) (q₁ * partition)
             (q₂ * energy₂ + q₂ * partition) ⟩
    q₁ * energy₁ +
      (q₁ * partition + (q₂ * energy₂ + q₂ * partition))
  ≡⟨ cong (λ tail → q₁ * energy₁ + tail)
      (trans
        (sym (ℚP.+-assoc (q₁ * partition) (q₂ * energy₂) (q₂ * partition)))
        (cong (λ head → head + q₂ * partition)
          (ℚP.+-comm (q₁ * partition) (q₂ * energy₂)))) ⟩
    q₁ * energy₁ +
      ((q₂ * energy₂ + q₁ * partition) + q₂ * partition)
  ≡⟨ cong (λ tail → q₁ * energy₁ + tail)
      (ℚP.+-assoc (q₂ * energy₂) (q₁ * partition) (q₂ * partition)) ⟩
    q₁ * energy₁ +
      (q₂ * energy₂ + (q₁ * partition + q₂ * partition))
  ≡⟨ sym (ℚP.+-assoc (q₁ * energy₁) (q₂ * energy₂)
      (q₁ * partition + q₂ * partition)) ⟩
    (q₁ * energy₁ + q₂ * energy₂) +
      (q₁ * partition + q₂ * partition)
  ≡⟨ cong (λ tail → (q₁ * energy₁ + q₂ * energy₂) + tail)
      (sym (ℚP.*-distribʳ-+ partition q₁ q₂)) ⟩
    (q₁ * energy₁ + q₂ * energy₂) + (q₁ + q₂) * partition
  ∎
  where open ≡-Reasoning

weightedEnergyPartition :
  (q₁ q₂ energy₁ energy₂ partition : ℚ) →
  q₁ + q₂ ≡ 1ℚ →
  q₁ * (energy₁ + partition) + q₂ * (energy₂ + partition)
    ≡ q₁ * energy₁ + q₂ * energy₂ + partition
weightedEnergyPartition q₁ q₂ energy₁ energy₂ partition normalized =
  trans (weightedEnergyExpansion q₁ q₂ energy₁ energy₂ partition) (trans
    (cong (λ weight → (q₁ * energy₁ + q₂ * energy₂) + weight * partition) normalized)
    (cong (λ term → q₁ * energy₁ + q₂ * energy₂ + term)
      (ℚP.*-identityˡ partition)))

addSubtractReassociate :
  (left right subtrahend : ℚ) →
  (left + right) - subtrahend ≡ (left - subtrahend) + right
addSubtractReassociate left right subtrahend =
  begin
    (left + right) - subtrahend
  ≡⟨ refl ⟩
    (left + right) + (- subtrahend)
  ≡⟨ ℚP.+-assoc left right (- subtrahend) ⟩
    left + (right + (- subtrahend))
  ≡⟨ cong (λ tail → left + tail) (ℚP.+-comm right (- subtrahend)) ⟩
    left + ((- subtrahend) + right)
  ≡⟨ sym (ℚP.+-assoc left (- subtrahend) right) ⟩
    (left + (- subtrahend)) + right
  ≡⟨ refl ⟩
    (left - subtrahend) + right
  ∎
  where open ≡-Reasoning

addThenSubtractSelf :
  (value offset : ℚ) →
  (value + offset) - offset ≡ value
addThenSubtractSelf value offset =
  begin
    (value + offset) - offset
  ≡⟨ refl ⟩
    (value + offset) + (- offset)
  ≡⟨ ℚP.+-assoc value offset (- offset) ⟩
    value + (offset + (- offset))
  ≡⟨ cong (λ tail → value + tail) (ℚP.+-inverseʳ offset) ⟩
    value + 0ℚ
  ≡⟨ ℚP.+-identityʳ value ⟩
    value
  ∎
  where open ≡-Reasoning

crossEntropyIsEnergyPlusLogPartition :
  (law : TwoStateVariationalLaw) →
  crossEntropy law ≡ expectedEnergy law + logPartition law
crossEntropyIsEnergyPlusLogPartition law
  rewrite priorBoltzmann₁ law
        | priorBoltzmann₂ law =
  weightedEnergyPartition
    (q₁ law) (q₂ law) (energy₁ law) (energy₂ law) (logPartition law)
    (normalizedQ law)

klEqualsFreeEnergyPlusLogPartition :
  (law : TwoStateVariationalLaw) →
  klDivergence law ≡ variationalFreeEnergy law + logPartition law
klEqualsFreeEnergyPlusLogPartition law
  rewrite priorBoltzmann₁ law
        | priorBoltzmann₂ law =
  trans
    (cong (λ value → value - entropy law)
      (weightedEnergyPartition
        (q₁ law) (q₂ law) (energy₁ law) (energy₂ law) (logPartition law)
        (normalizedQ law)))
    (addSubtractReassociate
      (expectedEnergy law) (logPartition law) (entropy law))

freeEnergyEqualsKLMinusLogPartition :
  (law : TwoStateVariationalLaw) →
  variationalFreeEnergy law ≡ klDivergence law - logPartition law
freeEnergyEqualsKLMinusLogPartition law =
  trans (sym (addThenSubtractSelf
    (variationalFreeEnergy law) (logPartition law)))
    (cong (λ value → value - logPartition law)
      (sym (klEqualsFreeEnergyPlusLogPartition law)))

record FiniteVariationalFreeEnergyBoundary : Set where
  constructor finiteVariationalFreeEnergyBoundary
  field
    klDefinesSemanticIdentity : Bool
    freeEnergyMinimumCreatesAuthority : Bool
    analyticLogarithmDerivedInternally : Bool
    finiteVariationalIdentityProved : Bool

canonicalFiniteVariationalFreeEnergyBoundary :
  FiniteVariationalFreeEnergyBoundary
canonicalFiniteVariationalFreeEnergyBoundary =
  finiteVariationalFreeEnergyBoundary false false false true
