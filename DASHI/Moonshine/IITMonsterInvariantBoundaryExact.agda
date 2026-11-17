module DASHI.Moonshine.IITMonsterInvariantBoundaryExact where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicNormSeparationExact as NormSeparation
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- IIT / MONSTER-MOONSHINE INVARIANT BOUNDARY
--
-- The Monster lane already owns exact C3 cyclotomic evaluation and a
-- positive-definite norm separation theorem.  That transfers a useful general
-- lesson to the integration programme: an invariant can be strong enough to
-- detect zero while still being too coarse to recover phase/state identity.
------------------------------------------------------------------------

normObserver : C3.Cyclotomic3 → ℚ
normObserver = C3.norm

phaseIdentityConsumer : C3.Cyclotomic3 → C3.Cyclotomic3
phaseIdentityConsumer value = value

zetaAndConjugateHaveSameNorm :
  normObserver C3.zeta ≡ normObserver C3.zetaSquared
zetaAndConjugateHaveSameNorm =
  trans C3.normZetaIsOne (sym C3.normZetaSquaredIsOne)

zetaNotZetaSquared : C3.zeta ≡ C3.zetaSquared → ⊥
zetaNotZetaSquared ()

normLosesC3Phase :
  Descent.ConsumerNonDescentWitness
    normObserver
    phaseIdentityConsumer
normLosesC3Phase =
  Descent.consumerNonDescentWitness
    C3.zeta
    C3.zetaSquared
    zetaAndConjugateHaveSameNorm
    zetaNotZetaSquared

normCannotRecoverC3Phase :
  Descent.FactorsThrough normObserver phaseIdentityConsumer → ⊥
normCannotRecoverC3Phase =
  Descent.nonDescentWitnessBlocksFactorization normLosesC3Phase

normZeroStillSeparatesZero :
  (value : C3.Cyclotomic3) →
  C3.norm value ≡ 0ℚ →
  value ≡ C3.zero
normZeroStillSeparatesZero = NormSeparation.normZeroImpliesZero

record MonsterIITInvariantBoundary : Set where
  constructor monsterIITInvariantBoundary
  field
    cyclotomicNormSeparatesZero : Bool
    cyclotomicNormRecoversFullC3Phase : Bool
    MonsterCharacterOrNormAutomaticallyEqualsIITPhi : Bool
    gradedTraceAutomaticallyDeterminesCausalPartition : Bool
    moonshineSymmetryAutomaticallyDeterminesConsciousness : Bool
    invariantUseRequiresExplicitFactorisationOrSeparationTheorem : Bool

open MonsterIITInvariantBoundary public

canonicalMonsterIITInvariantBoundary : MonsterIITInvariantBoundary
canonicalMonsterIITInvariantBoundary =
  monsterIITInvariantBoundary
    true false false false false true

zeroSeparationDoesNotMeanFullRecovery :
  cyclotomicNormRecoversFullC3Phase canonicalMonsterIITInvariantBoundary ≡ false
zeroSeparationDoesNotMeanFullRecovery = refl

moonshineDoesNotSelfPromoteToIIT :
  MonsterCharacterOrNormAutomaticallyEqualsIITPhi canonicalMonsterIITInvariantBoundary ≡ false
moonshineDoesNotSelfPromoteToIIT = refl
