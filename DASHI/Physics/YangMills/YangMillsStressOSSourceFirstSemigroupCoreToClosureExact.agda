module DASHI.Physics.YangMills.YangMillsStressOSSourceFirstSemigroupCoreToClosureExact where

------------------------------------------------------------------------
-- ROUND L7 SOURCE-FIRST JOIN TO THE EXISTING ROUND86 COMMON CORE.
--
-- In a reflection-positive Euclidean reconstruction the time shift is
-- the contraction semigroup T(t) = exp(-t H_OS). On the H_OS core,
--   -rightDerivativeAtZero(T(t) psi) = H_OS psi.
-- The physical translation Ward identity must identify the renormalized
-- stress charge with this SAME derivative on the SAME local core.
--
-- This is deliberately a source-first record: both actions are literally
-- one function of the shared derivative. Therefore it avoids assuming
-- function extensionality to promote independent pointwise identities
-- into equality of core-action functions. The original Round86 closure
-- compiler then yields equality of closed operators.
--
-- PHYSICAL OPEN INPUTS:
--   (1) original OS semigroup reconstructed from actual Schwinger family;
--   (2) norm right-derivative of same semigroup on common invariant core;
--   (3) source stress Ward action = negative right-derivative on that core;
--   (4) both operators are the self-adjoint closures of that core action.
--
-- The current record does NOT establish any of these four analytic inputs:
-- its closure equalities are evidence-bearing fields. No Clay promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsStressWardCommonCoreGeneratorExact as Common

record SourceFirstStressOSSemigroupCore
    (C : Common.CommonCoreClosureCalculus)
    (Time : Set) : Set₁ where
  field
    osEuclideanSemigroup :
      Time → Common.Vector C → Common.Vector C

    -- Limit of (T(t) psi - psi)/t on the actual core, in the OS norm.
    -- Establishing the limit is the external physical/analytic theorem.
    rightStrongDerivativeOnCore : Common.Core C → Common.Vector C

    vectorNegation : Common.Vector C → Common.Vector C

    stressCharge : Common.Operator C
    reconstructedOSHamiltonian : Common.Operator C

    -- Evidence that each physical operator is the closure of the SAME
    -- negative Euclidean derivative, with the required domains/cores.
    stressIsCoreClosure :
      stressCharge ≡ Common.close C
        (λ psi → vectorNegation (rightStrongDerivativeOnCore psi))

    osIsCoreClosure :
      reconstructedOSHamiltonian ≡ Common.close C
        (λ psi → vectorNegation (rightStrongDerivativeOnCore psi))

open SourceFirstStressOSSemigroupCore public

asExistingRound86CommonCore :
  ∀ {C Time} →
  SourceFirstStressOSSemigroupCore C Time →
  Common.StressOSCommonCoreData C
asExistingRound86CommonCore {C} source = record
  { Common.StressOSCommonCoreData.stressCoreAction =
      λ psi → vectorNegation source (rightStrongDerivativeOnCore source psi)
  ; Common.StressOSCommonCoreData.osCoreAction =
      λ psi → vectorNegation source (rightStrongDerivativeOnCore source psi)
  ; Common.StressOSCommonCoreData.stressOperator = stressCharge source
  ; Common.StressOSCommonCoreData.osHamiltonian =
      reconstructedOSHamiltonian source
  ; Common.StressOSCommonCoreData.commonCoreActionEquality = refl
  ; Common.StressOSCommonCoreData.stressIsClosureOfCoreAction =
      stressIsCoreClosure source
  ; Common.StressOSCommonCoreData.osHamiltonianIsClosureOfCoreAction =
      osIsCoreClosure source
  }

stressOSSameGeneratorFromSourceFirstSemigroup :
  ∀ {C Time}
    (source : SourceFirstStressOSSemigroupCore C Time) →
    stressCharge source ≡ reconstructedOSHamiltonian source
stressOSSameGeneratorFromSourceFirstSemigroup {C} source =
  Common.commonCoreWardImpliesSameGenerator C
    (asExistingRound86CommonCore source)
