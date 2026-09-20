{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact where

------------------------------------------------------------------------
-- A / BOSONIC FINITE PERMUTATION SYMMETRY -> LITERAL CMP119 OS3 INPUT
--
-- For gauge-invariant bosonic insertions, permutation symmetry of finite
-- Euclidean correlation functions is standard.  This owner does not encode a
-- source-intake boolean as a proof.  Instead it records the actual finite
-- normalized expectation equality on the literal CMP119 family and keeps only
-- the same-object observable/permutation attachment as the physical seam.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsFiniteNormalizedExpectationSymmetryExact as Symmetry
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record LiteralCMP119BosonicPermutationSymmetry
    (Configuration Permutation : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    : Set₂ where
  field
    permuteObservable :
      Permutation →
      (Configuration → ℝ) →
      (Configuration → ℝ)

    GaugeInvariantBosonic : (Configuration → ℝ) → Set

    selectedObservablesAreGaugeInvariantBosonic :
      ∀ observable → GaugeInvariantBosonic observable

    finiteBosonicPermutationSymmetry :
      ∀ cutoff permutation observable →
      GaugeInvariantBosonic observable →
      Limit.finiteExpectation family cutoff
        (permuteObservable permutation observable)
      ≡ Limit.finiteExpectation family cutoff observable

open LiteralCMP119BosonicPermutationSymmetry public

finitePermutationInvariant :
  ∀ {Configuration Permutation sequenceLimit limitLaws quotient division family}
    (dataSet :
      LiteralCMP119BosonicPermutationSymmetry
        Configuration Permutation
        {sequenceLimit} {limitLaws} {quotient} {division} family) →
  ∀ cutoff permutation observable →
  Limit.finiteExpectation family cutoff
    (permuteObservable dataSet permutation observable)
  ≡ Limit.finiteExpectation family cutoff observable
finitePermutationInvariant dataSet cutoff permutation observable =
  finiteBosonicPermutationSymmetry dataSet cutoff permutation observable
    (selectedObservablesAreGaugeInvariantBosonic dataSet observable)

bosonicPermutationSymmetrySourceLevel : ProofLevel
bosonicPermutationSymmetrySourceLevel = standardImported

literalCMP119BosonicObservableAttachmentLevel : ProofLevel
literalCMP119BosonicObservableAttachmentLevel = conditional

literalCMP119FiniteOS3AdapterLevel : ProofLevel
literalCMP119FiniteOS3AdapterLevel = machineChecked


bosonicFromNumeratorChangeOfVariables :
  ∀ {Configuration Permutation sequenceLimit limitLaws quotient division}
    {family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration {sequenceLimit = sequenceLimit}
        limitLaws quotient division}
    (permute :
      Permutation → (Configuration → ℝ) → Configuration → ℝ)
    (GaugeInvariantBosonic : (Configuration → ℝ) → Set)
    (selected :
      ∀ observable → GaugeInvariantBosonic observable)
    (numerator :
      Symmetry.FiniteNumeratorActionInvariant family permute) →
  LiteralCMP119BosonicPermutationSymmetry
    Configuration Permutation family
bosonicFromNumeratorChangeOfVariables
    permute GaugeInvariantBosonic selected numerator = record
  { LiteralCMP119BosonicPermutationSymmetry.permuteObservable =
      permute
  ; LiteralCMP119BosonicPermutationSymmetry.GaugeInvariantBosonic =
      GaugeInvariantBosonic
  ; LiteralCMP119BosonicPermutationSymmetry.selectedObservablesAreGaugeInvariantBosonic =
      selected
  ; LiteralCMP119BosonicPermutationSymmetry.finiteBosonicPermutationSymmetry =
      λ cutoff permutation observable bosonic →
        Symmetry.finiteNormalizedExpectationInvariantFromNumerator
          _ permute numerator cutoff permutation observable
  }

cmp119NumeratorBosonicAdapterLevel : ProofLevel
cmp119NumeratorBosonicAdapterLevel =
  Symmetry.finiteNumeratorToNormalizedSymmetryCompilerLevel
