{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LocalCoreStressExact where

------------------------------------------------------------------------
-- C / ROUND85 LOCAL-CORE CUTOFF REMOVAL -> PINNED COMMON CORE
--
-- Use the support-radius stabilized charge action as the stress core action.
-- No global spatial-cutoff convergence theorem is required to define the
-- charge on the local core. The remaining physical inputs are the translation
-- Ward equality on that same core and the two closure identifications.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsStressChargeLocalCoreCutoffStabilizationExact as R85
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressCommonCoreExact as Common
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedLocalCoreStressInputs
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

    cutoffCharge : R85.LocalCoreCutoffCharge Core Vector

    osCoreAction : Core → Vector
    localCoreWardAction :
      R85.localCoreChargeAction cutoffCharge ≡ osCoreAction

    closeCoreAction : (Core → Vector) → Hamiltonian

    stressChargeIsClosure :
      stressCharge stressTensor
      ≡ closeCoreAction (R85.localCoreChargeAction cutoffCharge)

    pinnedOSHamiltonianIsClosure :
      OSR.reconstructedHamiltonian reconstruction group
      ≡ closeCoreAction osCoreAction

open PinnedLocalCoreStressInputs public

asPinnedStressCommonCoreData :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group} →
  PinnedLocalCoreStressInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} {osInputs = osInputs} reconstruction group →
  Common.PinnedStressCommonCoreData
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} {osInputs = osInputs} reconstruction group
asPinnedStressCommonCoreData inputs = record
  { Common.PinnedStressCommonCoreData.stressTensor =
      stressTensor inputs
  ; Common.PinnedStressCommonCoreData.stressCharge =
      stressCharge inputs
  ; Common.PinnedStressCommonCoreData.closeCoreAction =
      closeCoreAction inputs
  ; Common.PinnedStressCommonCoreData.stressCoreAction =
      R85.localCoreChargeAction (cutoffCharge inputs)
  ; Common.PinnedStressCommonCoreData.osCoreAction =
      osCoreAction inputs
  ; Common.PinnedStressCommonCoreData.commonCoreWardAction =
      localCoreWardAction inputs
  ; Common.PinnedStressCommonCoreData.stressChargeIsClosure =
      stressChargeIsClosure inputs
  ; Common.PinnedStressCommonCoreData.pinnedOSHamiltonianIsClosure =
      pinnedOSHamiltonianIsClosure inputs
  }

localCoreStressChargeEqualsPinnedOSHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      PinnedLocalCoreStressInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} {osInputs = osInputs} reconstruction group) →
  stressCharge inputs (stressTensor inputs)
  ≡ OSR.reconstructedHamiltonian reconstruction group
localCoreStressChargeEqualsPinnedOSHamiltonian inputs =
  Common.stressChargeEqualsPinnedOSHamiltonian
    (asPinnedStressCommonCoreData inputs)

pinnedLocalCoreCutoffRemovalCompilerLevel : ProofLevel
pinnedLocalCoreCutoffRemovalCompilerLevel =
  R85.stressChargeLocalCoreCutoffRemovalLevel

pinnedLocalCoreToCommonCoreCompilerLevel : ProofLevel
pinnedLocalCoreToCommonCoreCompilerLevel = machineChecked

-- Remaining physics: local Ward/microcausal stabilization of cutoff charges,
-- the common-core Ward action, and self-adjoint/core closure identification.
literalPinnedLocalCoreWardClosureLevel : ProofLevel
literalPinnedLocalCoreWardClosureLevel = conditional
