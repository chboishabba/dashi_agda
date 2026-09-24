{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureSymmetryLimitExact where

------------------------------------------------------------------------
-- FINITE PHYSICAL SYMMETRIES -> SAME CONTINUUM LIMIT MEASURE
--
-- Gauge transformations, translations, and bosonic insertion permutations are
-- all instances of the same theorem: exact invariance of every finite
-- normalized expectation passes to the literal continuum expectation E∞.
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanCylinderLimitActionInvariantExact as Invariant
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as PhysicalLimit

record FinitePhysicalSymmetryLimitInputs
    (Configuration Action : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (family :
      PhysicalLimit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division) : Set₁ where
  field
    act :
      Action → (Configuration → ℝ) → (Configuration → ℝ)

    finiteExpectationInvariant :
      ∀ cutoff action observable →
      PhysicalLimit.finiteExpectation family cutoff
        (act action observable)
      ≡
      PhysicalLimit.finiteExpectation family cutoff observable

open FinitePhysicalSymmetryLimitInputs public

asCylinderActionInvariant :
  ∀ {Configuration Action sequenceLimit limitLaws quotient division family} →
  FinitePhysicalSymmetryLimitInputs
    Configuration Action limitLaws quotient division family →
  Invariant.CylinderActionInvariantInputs
    (PhysicalLimit.asCylinderLimitData family)
    Action
asCylinderActionInvariant inputs = record
  { Invariant.CylinderActionInvariantInputs.act =
      act inputs
  ; Invariant.CylinderActionInvariantInputs.finiteActionInvariant =
      finiteExpectationInvariant inputs
  }

continuumExpectationInvariant :
  ∀ {Configuration Action sequenceLimit limitLaws quotient division family}
    (inputs :
      FinitePhysicalSymmetryLimitInputs
        Configuration Action limitLaws quotient division family)
    action observable →
  PhysicalLimit.limitExpectation family
    (act inputs action observable)
  ≡
  PhysicalLimit.limitExpectation family observable
continuumExpectationInvariant inputs =
  Invariant.continuumActionInvariant
    (asCylinderActionInvariant inputs)

finitePhysicalSymmetryLimitCompilerLevel : ProofLevel
finitePhysicalSymmetryLimitCompilerLevel = machineChecked

-- Literal input is finite exact symmetry on the SAME Wilson/Balaban family.
literalFiniteGaugeInvarianceLevel : ProofLevel
literalFiniteGaugeInvarianceLevel = conditional

literalFiniteTranslationInvarianceLevel : ProofLevel
literalFiniteTranslationInvarianceLevel = conditional

literalFiniteBosonicPermutationInvarianceLevel : ProofLevel
literalFiniteBosonicPermutationInvarianceLevel = conditional
