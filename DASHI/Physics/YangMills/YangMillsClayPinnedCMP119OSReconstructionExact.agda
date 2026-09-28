{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact where

------------------------------------------------------------------------
-- SAME CMP119 OS SYSTEM -> SAME RECONSTRUCTED H / OMEGA / HAMILTONIAN
--
-- The reconstructed objects are projections of one OS reconstruction datum for
-- the exact Schwinger system constructed from the CMP119 continuum measure.
-- They are never independently selected downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
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

------------------------------------------------------------------------
-- PRE-GAP PINNED RECONSTRUCTION.
--
-- This is the H2 reconstruction object.  It is indexed by the clustering-free
-- CMP119 OS core and therefore does not consume H1/OS4.
------------------------------------------------------------------------

record PinnedCMP119PreGapOSReconstruction
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
    (coreInputs :
      OSSystem.PinnedCMP119OSCoreInputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian Vector
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S) : Set₂ where
  field
    reconstructionCore : ∀ G →
      OSR.PreGapOSReconstructionData
        (Configuration → ℝ) Position ℝ
        HilbertSpace Vector Hamiltonian Algebra
        (OSSystem.continuumOSCoreSystem coreInputs G)

    standardCoreAuthority : ∀ G →
      OSR.PreGapOSReconstructionStandardAuthority
        (reconstructionCore G)

open PinnedCMP119PreGapOSReconstruction public

reconstructedHilbertCore :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S coreInputs} →
  PinnedCMP119PreGapOSReconstruction
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} coreInputs →
  G → Hilbert
reconstructedHilbertCore dataSet group =
  OSR.reconstructedHilbertSpaceCore
    (reconstructionCore dataSet group)

reconstructedVacuumCore :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S coreInputs} →
  PinnedCMP119PreGapOSReconstruction
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} coreInputs →
  G → Vector
reconstructedVacuumCore dataSet group =
  OSR.reconstructedVacuumCore
    (reconstructionCore dataSet group)

reconstructedHamiltonianCore :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S coreInputs} →
  PinnedCMP119PreGapOSReconstruction
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} coreInputs →
  G → Hamiltonian
reconstructedHamiltonianCore dataSet group =
  OSR.reconstructedHamiltonianCore
    (reconstructionCore dataSet group)

legacyReconstructionData :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S coreInputs}
    (preGap :
      PinnedCMP119PreGapOSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} coreInputs)
    (clustering : OSSystem.CMP119OS4Attachment coreInputs)
    group →
  OSR.OSReconstructionData
    (Configuration → ℝ) Position ℝ
    Hilbert Vector Hamiltonian Algebra
    (OSSystem.continuumOSSystem
      (OSSystem.corePlusOS4Inputs coreInputs clustering) group)
legacyReconstructionData preGap clustering group = record
  { OSR.OSReconstructionData.reconstructedHilbertSpace =
      OSR.reconstructedHilbertSpaceCore
        (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.reconstructedVacuum =
      OSR.reconstructedVacuumCore
        (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.reconstructedHamiltonian =
      OSR.reconstructedHamiltonianCore
        (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.reconstructedObservableAlgebra =
      OSR.reconstructedObservableAlgebraCore
        (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.SelfAdjoint =
      OSR.SelfAdjointCore (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.Nonnegative =
      OSR.NonnegativeCore (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.VacuumVector =
      OSR.VacuumVectorCore (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.PhysicalObservableAlgebra =
      OSR.PhysicalObservableAlgebraCore (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.VacuumFor =
      OSR.VacuumForCore (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.EqualVector =
      λ left right → left ≡ right
  ; OSR.OSReconstructionData.hilbertSpaceReconstructed =
      OSR.hilbertSpaceReconstructedCore
        (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.vacuumVectorExists =
      OSR.vacuumVectorExistsCore
        (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.hamiltonianSelfAdjoint =
      OSR.hamiltonianSelfAdjointCore
        (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.hamiltonianNonnegative =
      OSR.hamiltonianNonnegativeCore
        (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.observableAlgebraPhysical =
      OSR.observableAlgebraPhysicalCore
        (reconstructionCore preGap group)
  ; OSR.OSReconstructionData.reconstructedVacuumIsVacuum =
      OSR.reconstructedVacuumIsVacuumCore
        (reconstructionCore preGap group)
  }

legacyStandardAuthority :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S coreInputs}
    (preGap :
      PinnedCMP119PreGapOSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} coreInputs)
    (clustering : OSSystem.CMP119OS4Attachment coreInputs)
    group →
  OSR.OSReconstructionStandardAuthority
    (legacyReconstructionData preGap clustering group)
legacyStandardAuthority preGap clustering group = record
  { OSR.OSReconstructionStandardAuthority.osAxiomsReconstruct =
      λ os0 os1 os2 os3 os4 os5 →
        OSR.osCoreAxiomsReconstruct
          (standardCoreAuthority preGap group)
          os0 os1 os2 os3 os5
  ; OSR.OSReconstructionStandardAuthority.reconstructionWitness =
      OSR.preGapReconstructionWitness
        (standardCoreAuthority preGap group)
  }

preGapPlusOS4ToLegacyReconstruction :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S coreInputs} →
  (preGap :
    PinnedCMP119PreGapOSReconstruction
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      {sequenceLimit = sequenceLimit}
      {limitLaws = limitLaws} {quotient = quotient} {division = division}
      {S = S} coreInputs) →
  (clustering : OSSystem.CMP119OS4Attachment coreInputs) →
  PinnedCMP119OSReconstruction
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S}
    (OSSystem.corePlusOS4Inputs coreInputs clustering)
preGapPlusOS4ToLegacyReconstruction preGap clustering = record
  { PinnedCMP119OSReconstruction.reconstruction =
      legacyReconstructionData preGap clustering
  ; PinnedCMP119OSReconstruction.standardAuthority =
      legacyStandardAuthority preGap clustering
  }

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

pinnedCMP119PreGapOSReconstructionObjectsLevel : ProofLevel
pinnedCMP119PreGapOSReconstructionObjectsLevel = machineChecked

pinnedCMP119PreGapToLegacyCompilerLevel : ProofLevel
pinnedCMP119PreGapToLegacyCompilerLevel = machineChecked

pinnedCMP119OSReconstructionObjectsLevel : ProofLevel
pinnedCMP119OSReconstructionObjectsLevel = machineChecked

pinnedCMP119OSSelfAdjointHamiltonianLevel : ProofLevel
pinnedCMP119OSSelfAdjointHamiltonianLevel = machineChecked

-- Standard OS reconstruction authority is imported; the genuine YM work is the
-- complete OS0/1/3/4/5 package on the constructed CMP119 Schwinger family.
pinnedCMP119OSReconstructionAuthorityLevel : ProofLevel
pinnedCMP119OSReconstructionAuthorityLevel = standardImported
