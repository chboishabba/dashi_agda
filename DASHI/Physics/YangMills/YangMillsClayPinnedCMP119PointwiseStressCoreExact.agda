{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119PointwiseStressCoreExact where

------------------------------------------------------------------------
-- C / POINTWISE WARD IDENTITY ON THE PINNED CMP119 OS CORE
--
-- Preferred replacement for function-equality common-core input.
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

record PinnedPointwiseStressCoreData
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core : Set)
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
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    (reconstruction :
      OSR.PinnedCMP119OSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs)
    (group : G) : Set₁ where
  field
    stressTensor : StressTensor
    stressCharge : StressTensor → Hamiltonian

    closeCoreAction : (Core → Vector) → Hamiltonian

    closeRespectsPointwiseEquality :
      ∀ (left right : Core → Vector) →
      (∀ vector → left vector ≡ right vector) →
      closeCoreAction left ≡ closeCoreAction right

    stressCoreAction : Core → Vector
    osCoreAction : Core → Vector

    pointwiseWard :
      ∀ vector → stressCoreAction vector ≡ osCoreAction vector

    stressChargeIsClosure :
      stressCharge stressTensor
      ≡ closeCoreAction stressCoreAction

    pinnedOSHamiltonianIsClosure :
      OSR.reconstructedHamiltonian reconstruction group
      ≡ closeCoreAction osCoreAction

open PinnedPointwiseStressCoreData public

asPointwiseCalculus :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group} →
  PinnedPointwiseStressCoreData
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} {osInputs = osInputs} reconstruction group →
  Pointwise.PointwiseCommonCoreClosureCalculus
asPointwiseCalculus dataSet = record
  { Pointwise.PointwiseCommonCoreClosureCalculus.Core = _
  ; Pointwise.PointwiseCommonCoreClosureCalculus.Vector = _
  ; Pointwise.PointwiseCommonCoreClosureCalculus.Operator = _
  ; Pointwise.PointwiseCommonCoreClosureCalculus.close =
      closeCoreAction dataSet
  ; Pointwise.PointwiseCommonCoreClosureCalculus.closeRespectsPointwiseEquality =
      closeRespectsPointwiseEquality dataSet
  }

asPointwiseStressData :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (dataSet :
      PinnedPointwiseStressCoreData
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} {osInputs = osInputs} reconstruction group) →
  Pointwise.PointwiseStressOSCommonCoreData
    (asPointwiseCalculus dataSet)
asPointwiseStressData {reconstruction = reconstruction} {group = group} dataSet = record
  { Pointwise.PointwiseStressOSCommonCoreData.stressCoreAction =
      stressCoreAction dataSet
  ; Pointwise.PointwiseStressOSCommonCoreData.osCoreAction =
      osCoreAction dataSet
  ; Pointwise.PointwiseStressOSCommonCoreData.stressOperator =
      stressCharge dataSet (stressTensor dataSet)
  ; Pointwise.PointwiseStressOSCommonCoreData.osHamiltonian =
      OSR.reconstructedHamiltonian reconstruction group
  ; Pointwise.PointwiseStressOSCommonCoreData.pointwiseCommonCoreWard =
      pointwiseWard dataSet
  ; Pointwise.PointwiseStressOSCommonCoreData.stressIsClosureOfCoreAction =
      stressChargeIsClosure dataSet
  ; Pointwise.PointwiseStressOSCommonCoreData.osHamiltonianIsClosureOfCoreAction =
      pinnedOSHamiltonianIsClosure dataSet
  }

pointwiseStressChargeEqualsPinnedOSHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (dataSet :
      PinnedPointwiseStressCoreData
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} {osInputs = osInputs} reconstruction group) →
  stressCharge dataSet (stressTensor dataSet)
  ≡ OSR.reconstructedHamiltonian reconstruction group
pointwiseStressChargeEqualsPinnedOSHamiltonian dataSet =
  Pointwise.pointwiseCommonCoreWardImpliesSameGenerator
    (asPointwiseCalculus dataSet)
    (asPointwiseStressData dataSet)

pinnedPointwiseStressCoreCompilerLevel : ProofLevel
pinnedPointwiseStressCoreCompilerLevel = machineChecked

-- Remaining operator-theoretic stress payment:
-- pointwise local Ward identity on the actual OS core plus the two
-- self-adjoint/common-core closure identifications.
literalPinnedPointwiseWardAndClosureLevel : ProofLevel
literalPinnedPointwiseWardAndClosureLevel = conditional
