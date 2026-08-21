module DASHI.Cognition.PNF.FiniteVariationalFreeEnergyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

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

crossEntropyIsEnergyPlusLogPartition :
  (law : TwoStateVariationalLaw) →
  crossEntropy law ≡ expectedEnergy law + logPartition law
crossEntropyIsEnergyPlusLogPartition law
  rewrite priorBoltzmann₁ law
        | priorBoltzmann₂ law
        | normalizedQ law = solve-∀

klEqualsFreeEnergyPlusLogPartition :
  (law : TwoStateVariationalLaw) →
  klDivergence law ≡ variationalFreeEnergy law + logPartition law
klEqualsFreeEnergyPlusLogPartition law
  rewrite priorBoltzmann₁ law
        | priorBoltzmann₂ law
        | normalizedQ law = solve-∀

freeEnergyEqualsKLMinusLogPartition :
  (law : TwoStateVariationalLaw) →
  variationalFreeEnergy law ≡ klDivergence law - logPartition law
freeEnergyEqualsKLMinusLogPartition law
  rewrite priorBoltzmann₁ law
        | priorBoltzmann₂ law
        | normalizedQ law = solve-∀

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
