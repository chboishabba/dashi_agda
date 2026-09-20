{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact where

------------------------------------------------------------------------
-- SAME CMP119 OS SYSTEM -> SAME RECONSTRUCTED H / OMEGA / HAMILTONIAN
--
-- The reconstructed objects are projections of one OS reconstruction datum for
-- the exact Schwinger system constructed from the CMP119 continuum measure.
-- They are never independently selected downstream.
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as OSR
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record PinnedCMP119OSReconstruction
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Vector Hamiltonian Algebra : Set)
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
    (osInputs :
      OSSystem.PinnedCMP119OSAxiomInputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian Vector
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S) : Set₂ where
  field
    reconstruction : ∀ G →
      OSR.OSReconstructionData
        (Configuration → ℝ) Position ℝ
        HilbertSpace Vector Hamiltonian Algebra
        (OSSystem.continuumOSSystem osInputs G)

    standardAuthority : ∀ G →
      OSR.OSReconstructionStandardAuthority
        (reconstruction G)

open PinnedCMP119OSReconstruction public

reconstructedHilbert :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs} →
  PinnedCMP119OSReconstruction
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} osInputs →
  G → Hilbert
reconstructedHilbert dataSet group =
  OSR.reconstructedHilbertSpace
    (reconstruction dataSet group)

reconstructedVacuum :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs} →
  PinnedCMP119OSReconstruction
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} osInputs →
  G → Vector
reconstructedVacuum dataSet group =
  OSR.reconstructedVacuum
    (reconstruction dataSet group)

reconstructedHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs} →
  PinnedCMP119OSReconstruction
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} osInputs →
  G → Hamiltonian
reconstructedHamiltonian dataSet group =
  OSR.reconstructedHamiltonian
    (reconstruction dataSet group)

osReconstructionWitness :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs}
    (dataSet :
      PinnedCMP119OSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs)
    group →
  OSR.osAxiomsReconstruct
    (standardAuthority dataSet group)
    (OSGap.os0 (OSSystem.continuumOSSystem osInputs group))
    (OSGap.os1 (OSSystem.continuumOSSystem osInputs group))
    (OSGap.os2 (OSSystem.continuumOSSystem osInputs group))
    (OSGap.os3 (OSSystem.continuumOSSystem osInputs group))
    (OSGap.os4 (OSSystem.continuumOSSystem osInputs group))
    (OSGap.os5 (OSSystem.continuumOSSystem osInputs group))
osReconstructionWitness dataSet group =
  OSR.reconstructionWitness
    (standardAuthority dataSet group)

reconstructedHamiltonianSelfAdjoint :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs}
    (dataSet :
      PinnedCMP119OSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs)
    group →
  OSR.SelfAdjoint (reconstruction dataSet group)
    (reconstructedHamiltonian dataSet group)
reconstructedHamiltonianSelfAdjoint dataSet group =
  OSR.reconstructedHamiltonianSelfAdjoint
    (reconstruction dataSet group)

reconstructedHamiltonianNonnegative :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs}
    (dataSet :
      PinnedCMP119OSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs)
    group →
  OSR.Nonnegative (reconstruction dataSet group)
    (reconstructedHamiltonian dataSet group)
reconstructedHamiltonianNonnegative dataSet group =
  OSR.reconstructedHamiltonianNonnegative
    (reconstruction dataSet group)

pinnedCMP119OSReconstructionObjectsLevel : ProofLevel
pinnedCMP119OSReconstructionObjectsLevel = machineChecked

pinnedCMP119OSSelfAdjointHamiltonianLevel : ProofLevel
pinnedCMP119OSSelfAdjointHamiltonianLevel = machineChecked

-- Standard OS reconstruction authority is imported; the genuine YM work is the
-- complete OS0/1/3/4/5 package on the constructed CMP119 Schwinger family.
pinnedCMP119OSReconstructionAuthorityLevel : ProofLevel
pinnedCMP119OSReconstructionAuthorityLevel = standardImported
