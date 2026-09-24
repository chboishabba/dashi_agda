{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressCommonCoreExact where

------------------------------------------------------------------------
-- LITERAL C / COMMON-CORE WARD DATA -> SAME PINNED OS HAMILTONIAN
--
-- The preferred C6 input is not a primitive equation
--
--     integral T00 = H_OS.
--
-- It is common-core data: the renormalized stress charge and the reconstructed
-- OS Hamiltonian have equal actions on one core and both are the closures of
-- those core actions.  The generic Round86 compiler then gives equality of the
-- global generators.  This owner pins the OS side definitionally to the exact
-- CMP119 reconstruction used by A.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsStressWardCommonCoreGeneratorExact as CommonCore
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedStressCommonCoreData
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

    stressCoreAction : Core → Vector
    osCoreAction : Core → Vector

    commonCoreWardAction :
      stressCoreAction ≡ osCoreAction

    stressChargeIsClosure :
      stressCharge stressTensor ≡ closeCoreAction stressCoreAction

    pinnedOSHamiltonianIsClosure :
      OSR.reconstructedHamiltonian reconstruction group
      ≡ closeCoreAction osCoreAction

open PinnedStressCommonCoreData public

asCommonCoreCalculus :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group} →
  PinnedStressCommonCoreData
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} {osInputs = osInputs} reconstruction group →
  CommonCore.CommonCoreClosureCalculus
asCommonCoreCalculus dataSet = record
  { CommonCore.CommonCoreClosureCalculus.Core = _
  ; CommonCore.CommonCoreClosureCalculus.Vector = _
  ; CommonCore.CommonCoreClosureCalculus.Operator = _
  ; CommonCore.CommonCoreClosureCalculus.close =
      closeCoreAction dataSet
  }

asStressOSCommonCoreData :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (dataSet :
      PinnedStressCommonCoreData
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} {osInputs = osInputs} reconstruction group) →
  CommonCore.StressOSCommonCoreData (asCommonCoreCalculus dataSet)
asStressOSCommonCoreData {reconstruction = reconstruction} {group = group} dataSet = record
  { CommonCore.StressOSCommonCoreData.stressCoreAction =
      stressCoreAction dataSet
  ; CommonCore.StressOSCommonCoreData.osCoreAction =
      osCoreAction dataSet
  ; CommonCore.StressOSCommonCoreData.stressOperator =
      stressCharge dataSet (stressTensor dataSet)
  ; CommonCore.StressOSCommonCoreData.osHamiltonian =
      OSR.reconstructedHamiltonian reconstruction group
  ; CommonCore.StressOSCommonCoreData.commonCoreActionEquality =
      commonCoreWardAction dataSet
  ; CommonCore.StressOSCommonCoreData.stressIsClosureOfCoreAction =
      stressChargeIsClosure dataSet
  ; CommonCore.StressOSCommonCoreData.osHamiltonianIsClosureOfCoreAction =
      pinnedOSHamiltonianIsClosure dataSet
  }

stressChargeEqualsPinnedOSHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (dataSet :
      PinnedStressCommonCoreData
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} {osInputs = osInputs} reconstruction group) →
  stressCharge dataSet (stressTensor dataSet)
  ≡ OSR.reconstructedHamiltonian reconstruction group
stressChargeEqualsPinnedOSHamiltonian dataSet =
  CommonCore.commonCoreWardImpliesSameGenerator
    (asCommonCoreCalculus dataSet)
    (asStressOSCommonCoreData dataSet)

pinnedStressCommonCoreSameHamiltonianCompilerLevel : ProofLevel
pinnedStressCommonCoreSameHamiltonianCompilerLevel = machineChecked

-- Genuine C physical input after this compiler:
-- construct the renormalized local stress charge on the same Schwinger family,
-- prove the translation Ward identity on one common core, and prove the stress
-- charge / pinned OS Hamiltonian are the self-adjoint closures of those core
-- actions.  Equality of the global generators is no longer primitive.
literalPinnedStressWardCommonCoreLevel : ProofLevel
literalPinnedStressWardCommonCoreLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
