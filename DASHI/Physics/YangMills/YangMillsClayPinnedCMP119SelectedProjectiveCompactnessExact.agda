{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119SelectedProjectiveCompactnessExact where

------------------------------------------------------------------------
-- A / SPECIALIZE THE SELECTED T5 COMPACTNESS CHAIN TO THE CMP119 FAMILY
--
-- Use expectation functionals as the measure carrier:
--
--   sequence n = literal normalized CMP119 finite expectation at n
--   target     = literal CMP119 limit expectation
--
-- Hence compactness / Prokhorov / cylinder uniqueness cannot silently choose a
-- second continuum object.  The only remaining A inputs in this lane are the
-- actual tightness/extraction and determining-class cylinder agreement.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Legacy
import DASHI.Physics.YangMills.BalabanClayT5SelectedProkhorovExtractionExact as Prokhorov
import DASHI.Physics.YangMills.BalabanClayT5SelectedCompactUniqueFullSequenceExact as CompactUnique
import DASHI.Physics.YangMills.BalabanClayT5CylinderDeterminingClusterUniquenessExact as Determining
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

cmp119ExpectationSequence :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : G) →
  Nat → Carrier.ExpectationMeasure (Configuration → ℝ)
cmp119ExpectationSequence inputs group cutoff =
  Limit.finiteExpectation (A.family inputs group) cutoff

cmp119ExpectationTarget :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : G) →
  Carrier.ExpectationMeasure (Configuration → ℝ)
cmp119ExpectationTarget inputs group =
  Limit.limitExpectation (A.family inputs group)

record CMP119SelectedCompactnessInputs
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
    (group : G) : Set₂ where
  field
    convergence :
      Selected.SequentialConvergence
        (Carrier.ExpectationMeasure (Configuration → ℝ))

    TightMeasureSequence :
      (Nat → Carrier.ExpectationMeasure (Configuration → ℝ)) → Set

    everyLiteralSubsequenceTight :
      (subsequence :
        Legacy.SubsequenceWitness
          (cmp119ExpectationSequence inputs group)) →
      TightMeasureSequence (Legacy.values subsequence)

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
        (cmp119ExpectationSequence inputs group)
        (Prokhorov.clusterLimit prokhorov
          (record
            { Prokhorov.SelectedSubsequenceTightnessData.convergence = convergence
            ; Prokhorov.SelectedSubsequenceTightnessData.sequence =
                cmp119ExpectationSequence inputs group
            ; Prokhorov.SelectedSubsequenceTightnessData.TightMeasureSequence =
                TightMeasureSequence
            ; Prokhorov.SelectedSubsequenceTightnessData.everyLiteralSubsequenceTight =
                everyLiteralSubsequenceTight
            }))
        (cmp119ExpectationTarget inputs group)

    fullConvergenceAuthority :
      CompactUnique.SelectedCompactUniqueFullConvergenceAuthority
        (Carrier.ExpectationMeasure (Configuration → ℝ))

open CMP119SelectedCompactnessInputs public

selectedTightnessData :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    {inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {group : G} →
  CMP119SelectedCompactnessInputs inputs group →
  Prokhorov.SelectedSubsequenceTightnessData
    (Carrier.ExpectationMeasure (Configuration → ℝ))
selectedTightnessData {inputs = inputs} {group = group} dataSet = record
  { Prokhorov.SelectedSubsequenceTightnessData.convergence =
      convergence dataSet
  ; Prokhorov.SelectedSubsequenceTightnessData.sequence =
      cmp119ExpectationSequence inputs group
  ; Prokhorov.SelectedSubsequenceTightnessData.TightMeasureSequence =
      TightMeasureSequence dataSet
  ; Prokhorov.SelectedSubsequenceTightnessData.everyLiteralSubsequenceTight =
      everyLiteralSubsequenceTight dataSet
  }

everyClusterIsLiteralCMP119Target :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    {inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {group : G}
    (dataSet : CMP119SelectedCompactnessInputs inputs group)
    (subsequence :
      Legacy.SubsequenceWitness
        (cmp119ExpectationSequence inputs group)) →
  Prokhorov.clusterLimit
    (prokhorov dataSet)
    (selectedTightnessData dataSet)
    subsequence
  ≡ cmp119ExpectationTarget inputs group
everyClusterIsLiteralCMP119Target dataSet =
  Determining.everyExtractedClusterPointIsTarget
    (determining dataSet)
    (extractedClusterCylinderAgreement dataSet)

compactUniqueInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    {inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {group : G} →
  CMP119SelectedCompactnessInputs inputs group →
  Prokhorov.SelectedCompactUniqueBridgeInputs
    (Carrier.ExpectationMeasure (Configuration → ℝ))
compactUniqueInputs {inputs = inputs} {group = group} dataSet = record
  { Prokhorov.SelectedCompactUniqueBridgeInputs.tightness =
      selectedTightnessData dataSet
  ; Prokhorov.SelectedCompactUniqueBridgeInputs.target =
      cmp119ExpectationTarget inputs group
  ; Prokhorov.SelectedCompactUniqueBridgeInputs.prokhorov =
      prokhorov dataSet
  ; Prokhorov.SelectedCompactUniqueBridgeInputs.everyExtractedClusterPointIsTarget =
      everyClusterIsLiteralCMP119Target dataSet
  }

fullCMP119ExpectationSequenceConverges :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    {inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {group : G}
    (dataSet : CMP119SelectedCompactnessInputs inputs group) →
  Selected.Converges (convergence dataSet)
    (cmp119ExpectationSequence inputs group)
    (cmp119ExpectationTarget inputs group)
fullCMP119ExpectationSequenceConverges dataSet =
  CompactUnique.selectedFullSequenceConverges
    (fullConvergenceAuthority dataSet)
    (Prokhorov.compileSelectedCompactUniqueData
      (compactUniqueInputs dataSet))

cmp119SelectedProjectiveCompactnessCompilerLevel : ProofLevel
cmp119SelectedProjectiveCompactnessCompilerLevel = machineChecked

-- Genuine A inputs after specialization: tightness/Prokhorov on the literal
-- CMP119 sequence and cylinder-determining agreement for every extracted
-- cluster point.  The target itself is no longer separately selected.
literalCMP119ProjectiveTightnessAndClusterAgreementLevel : ProofLevel
literalCMP119ProjectiveTightnessAndClusterAgreementLevel = conditional
