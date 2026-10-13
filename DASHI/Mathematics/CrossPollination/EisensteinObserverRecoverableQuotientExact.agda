module DASHI.Mathematics.CrossPollination.EisensteinObserverRecoverableQuotientExact where

------------------------------------------------------------------------
-- EISENSTEIN / C3 OBSERVER AS AN EXACT RECOVERABLE QUOTIENT
--
-- This module is deliberately small.  It reuses the repository's existing
-- three-phase Eisenstein carrier, generic recoverable-quotient interface and
-- generic consumer-relative descent machinery already used by the complexity
-- and Millennium residual programmes.
--
-- The coarse observer is n mod 3, represented by the existing phases
--   1, omega, omega^2.
-- The residual receipt is the quotient after repeatedly removing blocks of 3.
-- Together they reconstruct n exactly.  Thus a coarse collision is not, by
-- itself, an information-theoretic or complexity lower bound: residual data
-- can reopen the full state.
--
-- The same phase carrier also owns the exact antisymmetric C3 character law
--
--   chi_-3(r) * (omega^2 - omega) = omega^(2r) - omega^r,
--
-- written without division.  This is the finite Fourier/Dirichlet-character
-- weld needed by the Eisenstein counting, atomic-C3 and cyclotomic lanes.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Biology.EisensteinNineRingInterferenceExact as E
import DASHI.Biology.EisensteinThreeSixSymmetryExact as ThreeSix
import DASHI.Core.EfficientRecoverableQuotientExact as ERQ
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized

------------------------------------------------------------------------
-- 1. Exact mod-3 phase observer and explicit residual receipt.
------------------------------------------------------------------------

phaseOfNat : Nat → ThreeSix.TernaryPhase
phaseOfNat zero = ThreeSix.phaseOne
phaseOfNat (suc zero) = ThreeSix.phaseOmega
phaseOfNat (suc (suc zero)) = ThreeSix.phaseOmegaSquared
phaseOfNat (suc (suc (suc n))) = phaseOfNat n

quotient3 : Nat → Nat
quotient3 zero = zero
quotient3 (suc zero) = zero
quotient3 (suc (suc zero)) = zero
quotient3 (suc (suc (suc n))) = suc (quotient3 n)

phaseValue : ThreeSix.TernaryPhase → Nat
phaseValue ThreeSix.phaseOne = 0
phaseValue ThreeSix.phaseOmega = 1
phaseValue ThreeSix.phaseOmegaSquared = 2

reopen3 : ThreeSix.TernaryPhase → Nat → Nat
reopen3 phase zero = phaseValue phase
reopen3 phase (suc quotient) =
  suc (suc (suc (reopen3 phase quotient)))

reopenPhaseQuotient :
  (n : Nat) → reopen3 (phaseOfNat n) (quotient3 n) ≡ n
reopenPhaseQuotient zero = refl
reopenPhaseQuotient (suc zero) = refl
reopenPhaseQuotient (suc (suc zero)) = refl
reopenPhaseQuotient (suc (suc (suc n))) =
  cong suc (cong suc (cong suc (reopenPhaseQuotient n)))

phaseOfReopen :
  (phase : ThreeSix.TernaryPhase) →
  (quotient : Nat) →
  phaseOfNat (reopen3 phase quotient) ≡ phase
phaseOfReopen ThreeSix.phaseOne zero = refl
phaseOfReopen ThreeSix.phaseOmega zero = refl
phaseOfReopen ThreeSix.phaseOmegaSquared zero = refl
phaseOfReopen phase (suc quotient) = phaseOfReopen phase quotient

quotientOfReopen :
  (phase : ThreeSix.TernaryPhase) →
  (quotient : Nat) →
  quotient3 (reopen3 phase quotient) ≡ quotient
quotientOfReopen ThreeSix.phaseOne zero = refl
quotientOfReopen ThreeSix.phaseOmega zero = refl
quotientOfReopen ThreeSix.phaseOmegaSquared zero = refl
quotientOfReopen phase (suc quotient) =
  cong suc (quotientOfReopen phase quotient)

------------------------------------------------------------------------
-- 2. Literal inhabitant of the generic recoverable-quotient interface.
------------------------------------------------------------------------

natIdentityWitnessProblem : ERQ.WitnessProblem
natIdentityWitnessProblem =
  ERQ.witnessProblem Nat Nat (λ instance witness → witness ≡ instance)

eisensteinResidueRecoverableQuotient :
  ERQ.WitnessRecoverableQuotient natIdentityWitnessProblem
eisensteinResidueRecoverableQuotient =
  ERQ.witnessRecoverableQuotient
    ThreeSix.TernaryPhase
    Nat
    phaseOfNat
    quotient3
    reopen3
    reopenPhaseQuotient

------------------------------------------------------------------------
-- 3. Coarse collision and exact reopening coexist.
------------------------------------------------------------------------

phaseZeroEqualsPhaseThree : phaseOfNat 0 ≡ phaseOfNat 3
phaseZeroEqualsPhaseThree = refl

zeroIsNotThree : 0 ≡ 3 → ⊥
zeroIsNotThree ()

phaseObserverIsNotInjective :
  ((left right : Nat) → phaseOfNat left ≡ phaseOfNat right → left ≡ right) → ⊥
phaseObserverIsNotInjective injective =
  zeroIsNotThree (injective 0 3 phaseZeroEqualsPhaseThree)

identityConsumer : Nat → Nat
identityConsumer n = n

phaseIdentityNonDescent :
  Descent.ConsumerNonDescentWitness phaseOfNat identityConsumer
phaseIdentityNonDescent =
  Descent.consumerNonDescentWitness
    0
    3
    phaseZeroEqualsPhaseThree
    zeroIsNotThree

phaseCannotPayIdentityConsumer :
  Descent.ConsumerSufficient phaseOfNat identityConsumer → ⊥
phaseCannotPayIdentityConsumer =
  Descent.nonDescentWitnessBlocksSufficiency phaseIdentityNonDescent

------------------------------------------------------------------------
-- 4. Exact C3-DFT antisymmetric channel = chi_-3, division-free.
------------------------------------------------------------------------

subtractEisenstein : E.Eisenstein → E.Eisenstein → E.Eisenstein
subtractEisenstein (E.eisenstein ar ao) (E.eisenstein br bo) =
  E.eisenstein (ar - br) (ao - bo)

scaleEisenstein : ℚ → E.Eisenstein → E.Eisenstein
scaleEisenstein scalar (E.eisenstein real omega) =
  E.eisenstein (scalar * real) (scalar * omega)

phaseSquareAmplitude : ThreeSix.TernaryPhase → E.Eisenstein
phaseSquareAmplitude ThreeSix.phaseOne = E.one
phaseSquareAmplitude ThreeSix.phaseOmega = E.omegaSquared
phaseSquareAmplitude ThreeSix.phaseOmegaSquared = E.omega

chiMinus3PhaseWeight : ThreeSix.TernaryPhase → ℚ
chiMinus3PhaseWeight ThreeSix.phaseOne = 0ℚ
chiMinus3PhaseWeight ThreeSix.phaseOmega = E.qOne
chiMinus3PhaseWeight ThreeSix.phaseOmegaSquared = E.qMinusOne

antisymmetricNumerator : ThreeSix.TernaryPhase → E.Eisenstein
antisymmetricNumerator phase =
  subtractEisenstein
    (phaseSquareAmplitude phase)
    (ThreeSix.phaseAmplitude phase)

antisymmetricDenominator : E.Eisenstein
antisymmetricDenominator = subtractEisenstein E.omegaSquared E.omega

eisensteinExt :
  ∀ {left right : E.Eisenstein} →
  E.realCoordinate left ≡ E.realCoordinate right →
  E.omegaCoordinate left ≡ E.omegaCoordinate right →
  left ≡ right
eisensteinExt {E.eisenstein _ _} {E.eisenstein _ _} refl refl = refl

antisymmetricCharacterFactorization :
  (phase : ThreeSix.TernaryPhase) →
  antisymmetricNumerator phase
  ≡ scaleEisenstein (chiMinus3PhaseWeight phase) antisymmetricDenominator
antisymmetricCharacterFactorization ThreeSix.phaseOne =
  eisensteinExt refl refl
antisymmetricCharacterFactorization ThreeSix.phaseOmega =
  eisensteinExt refl refl
antisymmetricCharacterFactorization ThreeSix.phaseOmegaSquared =
  eisensteinExt refl refl

------------------------------------------------------------------------
-- 5. The phase observer is exactly sufficient for the chi_-3 consumer.
------------------------------------------------------------------------

chiMinus3WeightOfNat : Nat → ℚ
chiMinus3WeightOfNat n = chiMinus3PhaseWeight (phaseOfNat n)

chiMinus3WeightThreePeriodic :
  (n : Nat) →
  chiMinus3WeightOfNat (suc (suc (suc n))) ≡ chiMinus3WeightOfNat n
chiMinus3WeightThreePeriodic n = refl

chiMinus3FactorsThroughPhase :
  Descent.FactorsThrough phaseOfNat chiMinus3WeightOfNat
chiMinus3FactorsThroughPhase =
  Factorized.factorizedRefinement
    chiMinus3PhaseWeight
    (λ n → refl)

phaseIsSufficientForChiMinus3 :
  Descent.ConsumerSufficient phaseOfNat chiMinus3WeightOfNat
phaseIsSufficientForChiMinus3 =
  Descent.fibreConstantIsConsumerSufficient
    (Descent.factorsThroughImpliesFibreConstant chiMinus3FactorsThroughPhase)

------------------------------------------------------------------------
-- Boundary: exact finite observer mathematics is not automatic promotion to
-- an arbitrary consumer, a complexity lower bound, an atomic Hamiltonian,
-- a Millennium theorem, or an E6 representation.
------------------------------------------------------------------------

data ConsumerPromotionFromCoarsePhaseAlone : Set where

data ComplexityLowerBoundFromCoarseCollisionAlone : Set where

data E6IdentificationFromThreePhaseCarrierAlone : Set where

noUniversalConsumerPromotion : ConsumerPromotionFromCoarsePhaseAlone → ⊥
noUniversalConsumerPromotion ()

noComplexityLowerBoundFromCollisionAlone :
  ComplexityLowerBoundFromCoarseCollisionAlone → ⊥
noComplexityLowerBoundFromCollisionAlone ()

noE6IdentificationFromPhaseCountAlone :
  E6IdentificationFromThreePhaseCarrierAlone → ⊥
noE6IdentificationFromPhaseCountAlone ()
