{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119UniformProjectiveCompactnessExact where

------------------------------------------------------------------------
-- A4 / ONE UNIFORM COMPACT-CONTAINMENT CERTIFICATE -> ALL SUBSEQUENCES
--
-- The pinned projective owner historically asks directly for tightness of every
-- literal subsequence.  That quantifier is compiler-owned once the exact CMP119
-- finite expectation sequence has one uniform compact-containment certificate.
-- This module performs that restriction and feeds the existing selected
-- Prokhorov/cylinder-uniqueness compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119SelectedProjectiveCompactnessExact as Compact
import DASHI.Physics.YangMills.BalabanClayT5UniformTightnessSubsequenceInheritanceExact as Uniform
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Legacy
import DASHI.Physics.YangMills.BalabanClayT5SelectedProkhorovExtractionExact as Prokhorov
import DASHI.Physics.YangMills.BalabanClayT5SelectedCompactUniqueFullSequenceExact as CompactUnique
import DASHI.Physics.YangMills.BalabanClayT5CylinderDeterminingClusterUniquenessExact as Determining
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119UniformProjectiveInputs
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : G)
    (Epsilon Witness : Set) : Set₂ where
  field
    convergence :
      Selected.SequentialConvergence
        (Carrier.ExpectationMeasure (Configuration → ℝ))

    Admissible : Epsilon → Witness → Set
    Controls :
      Epsilon → Witness →
      Carrier.ExpectationMeasure (Configuration → ℝ) → Set

    uniformlyTight :
      Uniform.UniformTightnessCertificate
        (Carrier.ExpectationMeasure (Configuration → ℝ))
        Epsilon Witness Admissible Controls
        (Compact.cmp119ExpectationSequence inputs group)

    prokhorov :
      Prokhorov.SelectedProkhorovAuthority
        (Carrier.ExpectationMeasure (Configuration → ℝ))

    determining :
      Determining.CylinderDeterminingAuthority
        (Carrier.ExpectationMeasure (Configuration → ℝ))
        (Configuration → ℝ)
        ℝ
        (λ measure observable → measure observable)

    extractedClusterCylinderAgreement :
      Determining.ExtractedClusterCylinderAgreement
        (Carrier.ExpectationMeasure (Configuration → ℝ))
        (Configuration → ℝ)
        ℝ
        (λ measure observable → measure observable)
        (Compact.cmp119ExpectationSequence inputs group)
        (Prokhorov.clusterLimit prokhorov
          (record
            { Prokhorov.SelectedSubsequenceTightnessData.convergence =
                convergence
            ; Prokhorov.SelectedSubsequenceTightnessData.sequence =
                Compact.cmp119ExpectationSequence inputs group
            ; Prokhorov.SelectedSubsequenceTightnessData.TightMeasureSequence =
                Uniform.UniformTightnessCertificate
                  (Carrier.ExpectationMeasure (Configuration → ℝ))
                  Epsilon Witness Admissible Controls
            ; Prokhorov.SelectedSubsequenceTightnessData.everyLiteralSubsequenceTight =
                λ subsequence →
                  Uniform.restrictUniformTightnessToSubsequence
                    uniformlyTight subsequence
            }))
        (Compact.cmp119ExpectationTarget inputs group)

    fullConvergenceAuthority :
      CompactUnique.SelectedCompactUniqueFullConvergenceAuthority
        (Carrier.ExpectationMeasure (Configuration → ℝ))

open CMP119UniformProjectiveInputs public

asSelectedProjectiveCompactness :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S Epsilon Witness}
    {inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {group : G} →
  CMP119UniformProjectiveInputs inputs group Epsilon Witness →
  Compact.CMP119SelectedCompactnessInputs inputs group
asSelectedProjectiveCompactness
    {Epsilon = Epsilon} {Witness = Witness} dataSet = record
  { Compact.CMP119SelectedCompactnessInputs.convergence =
      convergence dataSet
  ; Compact.CMP119SelectedCompactnessInputs.TightMeasureSequence =
      Uniform.UniformTightnessCertificate
        _ Epsilon Witness (Admissible dataSet) (Controls dataSet)
  ; Compact.CMP119SelectedCompactnessInputs.everyLiteralSubsequenceTight =
      λ subsequence →
        Uniform.restrictUniformTightnessToSubsequence
          (uniformlyTight dataSet) subsequence
  ; Compact.CMP119SelectedCompactnessInputs.prokhorov =
      prokhorov dataSet
  ; Compact.CMP119SelectedCompactnessInputs.determining =
      determining dataSet
  ; Compact.CMP119SelectedCompactnessInputs.extractedClusterCylinderAgreement =
      extractedClusterCylinderAgreement dataSet
  ; Compact.CMP119SelectedCompactnessInputs.fullConvergenceAuthority =
      fullConvergenceAuthority dataSet
  }

fullCMP119ExpectationSequenceConvergesFromUniformTightness :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S Epsilon Witness}
    {inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {group : G}
    (dataSet : CMP119UniformProjectiveInputs
      inputs group Epsilon Witness) →
  Selected.Converges (convergence dataSet)
    (Compact.cmp119ExpectationSequence inputs group)
    (Compact.cmp119ExpectationTarget inputs group)
fullCMP119ExpectationSequenceConvergesFromUniformTightness dataSet =
  Compact.fullCMP119ExpectationSequenceConverges
    (asSelectedProjectiveCompactness dataSet)

cmp119UniformTightnessSubsequenceCompilerLevel : ProofLevel
cmp119UniformTightnessSubsequenceCompilerLevel = machineChecked

-- A4 is narrowed to ONE uniform compact-containment estimate on the literal
-- sequence.  Prokhorov extraction remains standardImported downstream.
literalCMP119UniformCompactContainmentLevel : ProofLevel
literalCMP119UniformCompactContainmentLevel = conditional

-- A5 remains the same-object cylinder agreement for extracted clusters; the
-- determining-class implication itself is already compiler-owned.
literalCMP119ExtractedClusterCylinderAgreementLevel : ProofLevel
literalCMP119ExtractedClusterCylinderAgreementLevel = conditional
