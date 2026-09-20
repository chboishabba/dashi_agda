{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsFiniteNormalizedExpectationSymmetryExact where

------------------------------------------------------------------------
-- A / FINITE NUMERATOR SYMMETRY -> NORMALIZED EXPECTATION SYMMETRY
--
-- The normalized finite expectation divides every observable numerator by the
-- same nonzero partition function.  Therefore OS1/OS3 do not need independent
-- normalized-expectation invariance theorems: it is enough to prove invariance
-- of the unnormalized Haar/Gibbs numerator under the finite action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient

record FiniteNumeratorActionInvariant
    {Configuration Action : Set}
    {sequenceLimit limitLaws quotient division}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (act : Action → (Configuration → DASHI.Foundations.RealAnalysisAxioms.ℝ) →
      Configuration → DASHI.Foundations.RealAnalysisAxioms.ℝ) : Set₁ where
  field
    numeratorInvariant :
      ∀ cutoff action observable →
      Finite.unnormalizedNumerator
        (Limit.finiteMeasure family cutoff)
        (act action observable)
      ≡
      Finite.unnormalizedNumerator
        (Limit.finiteMeasure family cutoff)
        observable

open FiniteNumeratorActionInvariant public

finiteNormalizedExpectationInvariantFromNumerator :
  ∀ {Configuration Action sequenceLimit limitLaws quotient division}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (act : Action → (Configuration → DASHI.Foundations.RealAnalysisAxioms.ℝ) →
      Configuration → DASHI.Foundations.RealAnalysisAxioms.ℝ)
    (invariance : FiniteNumeratorActionInvariant family act)
    cutoff action observable →
  Limit.finiteExpectation family cutoff (act action observable)
  ≡
  Limit.finiteExpectation family cutoff observable
finiteNormalizedExpectationInvariantFromNumerator
    {quotient = quotient} family act invariance cutoff action observable =
  cong
    (λ numerator →
      Quotient.divide quotient numerator
        (DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact.partitionFunction
          (Limit.finiteMeasure family cutoff)))
    (numeratorInvariant invariance cutoff action observable)

finiteNumeratorToNormalizedSymmetryCompilerLevel : ProofLevel
finiteNumeratorToNormalizedSymmetryCompilerLevel = machineChecked

-- Literal finite symmetry payment is now the natural change-of-variables
-- statement on the unnormalized product-Haar/Gibbs numerator.
literalFiniteNumeratorChangeOfVariablesLevel : ProofLevel
literalFiniteNumeratorChangeOfVariablesLevel = conditional
