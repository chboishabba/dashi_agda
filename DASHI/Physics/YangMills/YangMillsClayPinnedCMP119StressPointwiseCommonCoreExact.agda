{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressPointwiseCommonCoreExact where

------------------------------------------------------------------------
-- C / PINNED POINTWISE WARD DATA -> SAME CMP119 OS HAMILTONIAN
--
-- Ward identities are naturally statements on each local vector.  This pinned
-- owner therefore removes the stronger function-equality premise from the
-- historical common-core package.  The only generic operator input is that
-- closure respects pointwise equality on the identical domain.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsStressWardPointwiseCoreGeneratorExact as Pointwise
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedPointwiseStressCommonCoreData
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     Hilbert Vector Hamiltonian Algebra Core : Set)
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
    {osInputs :
      OSSystem.PinnedCMP119OSAxiomInputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        Hilbert Hamiltonian Vector
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    (reconstruction :
      OSR.PinnedCMP119OSReconstruction
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs)
    (group : CompactSimpleGroup) : Set₁ where
  field
    stressTensor : StressTensor
    stressCharge : StressTensor → Hamiltonian

    closeCoreAction : (Core → Vector) → Hamiltonian
    closeCoreActionRespectsPointwiseEquality :
      ∀ (left right : Core → Vector) →
      (∀ vector → left vector ≡ right vector) →
      closeCoreAction left ≡ closeCoreAction right

    stressCoreAction : Core → Vector
    osCoreAction : Core → Vector

    pointwiseCommonCoreWard :
      ∀ vector →
      stressCoreAction vector ≡ osCoreAction vector

    stressChargeIsClosure :
      stressCharge stressTensor ≡ closeCoreAction stressCoreAction

    pinnedOSHamiltonianIsClosure :
      OSR.reconstructedHamiltonian reconstruction group
      ≡ closeCoreAction osCoreAction

open PinnedPointwiseStressCommonCoreData public

asPointwiseClosureCalculus :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group} →
  PinnedPointwiseStressCommonCoreData
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} {osInputs = osInputs} reconstruction group →
  Pointwise.PointwiseCommonCoreClosureCalculus
asPointwiseClosureCalculus dataSet = record
  { Pointwise.PointwiseCommonCoreClosureCalculus.Core = _
  ; Pointwise.PointwiseCommonCoreClosureCalculus.Vector = _
  ; Pointwise.PointwiseCommonCoreClosureCalculus.Operator = _
  ; Pointwise.PointwiseCommonCoreClosureCalculus.close =
      closeCoreAction dataSet
  ; Pointwise.PointwiseCommonCoreClosureCalculus.closeRespectsPointwiseEquality =
      closeCoreActionRespectsPointwiseEquality dataSet
  }

asPointwiseStressOSData :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (dataSet :
      PinnedPointwiseStressCommonCoreData
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} {osInputs = osInputs} reconstruction group) →
  Pointwise.PointwiseStressOSCommonCoreData
    (asPointwiseClosureCalculus dataSet)
asPointwiseStressOSData {reconstruction = reconstruction} {group = group}
    dataSet = record
  { Pointwise.PointwiseStressOSCommonCoreData.stressCoreAction =
      stressCoreAction dataSet
  ; Pointwise.PointwiseStressOSCommonCoreData.osCoreAction =
      osCoreAction dataSet
  ; Pointwise.PointwiseStressOSCommonCoreData.stressOperator =
      stressCharge dataSet (stressTensor dataSet)
  ; Pointwise.PointwiseStressOSCommonCoreData.osHamiltonian =
      OSR.reconstructedHamiltonian reconstruction group
  ; Pointwise.PointwiseStressOSCommonCoreData.pointwiseCommonCoreWard =
      pointwiseCommonCoreWard dataSet
  ; Pointwise.PointwiseStressOSCommonCoreData.stressIsClosureOfCoreAction =
      stressChargeIsClosure dataSet
  ; Pointwise.PointwiseStressOSCommonCoreData.osHamiltonianIsClosureOfCoreAction =
      pinnedOSHamiltonianIsClosure dataSet
  }

stressChargeEqualsPinnedOSHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (dataSet :
      PinnedPointwiseStressCommonCoreData
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} {osInputs = osInputs} reconstruction group) →
  stressCharge dataSet (stressTensor dataSet)
  ≡ OSR.reconstructedHamiltonian reconstruction group
stressChargeEqualsPinnedOSHamiltonian dataSet =
  Pointwise.pointwiseCommonCoreWardImpliesSameGenerator
    (asPointwiseClosureCalculus dataSet)
    (asPointwiseStressOSData dataSet)

pinnedPointwiseStressCommonCoreCompilerLevel : ProofLevel
pinnedPointwiseStressCommonCoreCompilerLevel = machineChecked

-- The physical Ward leaf is now pointwise on the local core.  No equality of
-- functions and no function-extensionality principle is part of the YM input.
literalPinnedPointwiseStressWardLevel : ProofLevel
literalPinnedPointwiseStressWardLevel = conditional

stressAndOSClosureIdentificationLevel : ProofLevel
stressAndOSClosureIdentificationLevel = conditional
