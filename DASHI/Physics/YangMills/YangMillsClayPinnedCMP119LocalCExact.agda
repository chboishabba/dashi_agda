{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LocalCExact where

------------------------------------------------------------------------
-- C SPECIALIZED TO THE SAME OS-RECONSTRUCTED HAMILTONIAN AS LITERAL A
--
-- No post-hoc C-Hamiltonian equality is accepted.  The continuum local/OPE/
-- stress package is constructed with the OS Hamiltonian as its Hamiltonian
-- coordinate.  The remaining theorem is the physical Ward/generator statement
-- on that exact operator.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.BalabanSameFamilyCompositeOPEStressCompilerExact as C
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.YangMillsSharedMarkedCompositeOPERemainderExact as MarkedOPE
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedCMP119LocalCInputs
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily : Set)
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
      A.PinnedCMP119OSAxiomInputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        Hilbert Hamiltonian Vector
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (reconstruction :
      OSR.PinnedCMP119OSReconstruction
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs)
    (group : CompactSimpleGroup) : Set₂ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root

    selectedScale : Scale
    selectedVolume : Volume
    selectedRoot : Root
    remaining : Nat → Nat

    continuumFamily : ContinuumFamily

    localOperator : CurvaturePolynomial → LocalOperator
    GaugeInvariant : LocalOperator → Set
    LocalAt : LocalOperator → Position → Set
    curvatureOperatorsGaugeInvariant : ∀ polynomial →
      GaugeInvariant (localOperator polynomial)
    curvatureOperatorsLocal : ∀ polynomial position →
      LocalAt (localOperator polynomial) position

    OPEAdmissible : LocalOperator → LocalOperator → Set
    coefficient :
      LocalOperator → LocalOperator → LocalOperator → Position → OPECoefficient

    physicalRemainder :
      LocalOperator → LocalOperator → Position → Nat → ℚ

    physicalRemainderIsCompositeTail :
      ∀ left right position admissible depth →
      physicalRemainder left right position depth
      ≡
      Local.remainderMagnitude
        (MarkedOPE.sharedCompositeAsDyadicOPERemainder
          shared selectedScale selectedVolume selectedRoot remaining)
        depth

    ShortDistanceAFMatching : Set
    shortDistanceAFMatching : ShortDistanceAFMatching

    stressTensor : StressTensor
    Symmetric : StressTensor → Set
    ConservedInCorrelators : StressTensor → Set
    LocalStressTensor : StressTensor → Set
    stressTensorSymmetric : Symmetric stressTensor
    stressTensorConserved : ConservedInCorrelators stressTensor
    stressTensorLocal : LocalStressTensor stressTensor

    -- C4 is stated directly on the SAME OS Hamiltonian.
    SpatialIntegralT00Generates : StressTensor → Hamiltonian → Set
    stressTensorGeneratesOSHamiltonian :
      SpatialIntegralT00Generates
        stressTensor
        (OSR.reconstructedHamiltonian reconstruction group)

open PinnedCMP119LocalCInputs public

asSameFamilyCompositeInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily
      sequenceLimit limitLaws quotient division S osInputs reconstruction group} →
  PinnedCMP119LocalCInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    Scale Volume Root ContinuumFamily
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} osInputs reconstruction group →
  C.SameFamilyCompositeOPEStressInputs
    Scale Volume Root ContinuumFamily CurvaturePolynomial LocalOperator Position
    OPECoefficient StressTensor Hamiltonian
asSameFamilyCompositeInputs
    {reconstruction = reconstruction} {group = group}
    inputs = record
  { C.SameFamilyCompositeOPEStressInputs.shared =
      shared inputs
  ; C.SameFamilyCompositeOPEStressInputs.selectedScale =
      selectedScale inputs
  ; C.SameFamilyCompositeOPEStressInputs.selectedVolume =
      selectedVolume inputs
  ; C.SameFamilyCompositeOPEStressInputs.selectedRoot =
      selectedRoot inputs
  ; C.SameFamilyCompositeOPEStressInputs.remaining =
      remaining inputs
  ; C.SameFamilyCompositeOPEStressInputs.continuumFamily =
      continuumFamily inputs
  ; C.SameFamilyCompositeOPEStressInputs.localOperator =
      localOperator inputs
  ; C.SameFamilyCompositeOPEStressInputs.GaugeInvariant =
      GaugeInvariant inputs
  ; C.SameFamilyCompositeOPEStressInputs.LocalAt =
      LocalAt inputs
  ; C.SameFamilyCompositeOPEStressInputs.curvatureOperatorsGaugeInvariant =
      curvatureOperatorsGaugeInvariant inputs
  ; C.SameFamilyCompositeOPEStressInputs.curvatureOperatorsLocal =
      curvatureOperatorsLocal inputs
  ; C.SameFamilyCompositeOPEStressInputs.OPEAdmissible =
      OPEAdmissible inputs
  ; C.SameFamilyCompositeOPEStressInputs.coefficient =
      coefficient inputs
  ; C.SameFamilyCompositeOPEStressInputs.physicalRemainder =
      physicalRemainder inputs
  ; C.SameFamilyCompositeOPEStressInputs.physicalRemainderIsCompositeTail =
      physicalRemainderIsCompositeTail inputs
  ; C.SameFamilyCompositeOPEStressInputs.ShortDistanceAFMatching =
      ShortDistanceAFMatching inputs
  ; C.SameFamilyCompositeOPEStressInputs.shortDistanceAFMatching =
      shortDistanceAFMatching inputs
  ; C.SameFamilyCompositeOPEStressInputs.stressTensor =
      stressTensor inputs
  ; C.SameFamilyCompositeOPEStressInputs.Symmetric =
      Symmetric inputs
  ; C.SameFamilyCompositeOPEStressInputs.ConservedInCorrelators =
      ConservedInCorrelators inputs
  ; C.SameFamilyCompositeOPEStressInputs.LocalStressTensor =
      LocalStressTensor inputs
  ; C.SameFamilyCompositeOPEStressInputs.stressTensorSymmetric =
      stressTensorSymmetric inputs
  ; C.SameFamilyCompositeOPEStressInputs.stressTensorConserved =
      stressTensorConserved inputs
  ; C.SameFamilyCompositeOPEStressInputs.stressTensorLocal =
      stressTensorLocal inputs
  ; C.SameFamilyCompositeOPEStressInputs.reconstructedHamiltonian =
      OSR.reconstructedHamiltonian reconstruction group
  ; C.SameFamilyCompositeOPEStressInputs.SpatialIntegralT00Generates =
      SpatialIntegralT00Generates inputs
  ; C.SameFamilyCompositeOPEStressInputs.stressTensorGeneratesHamiltonian =
      stressTensorGeneratesOSHamiltonian inputs
  }

compilePinnedLocalPackage :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      PinnedCMP119LocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) →
  Local.ContinuumLocalOperatorOPEStressTensor
    ContinuumFamily CurvaturePolynomial LocalOperator Position
    OPECoefficient StressTensor Hamiltonian
compilePinnedLocalPackage inputs =
  C.compileContinuumLocalOperatorOPEStressTensor
    (asSameFamilyCompositeInputs inputs)

pinnedLocalHamiltonianIsOSHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      PinnedCMP119LocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) →
  Local.reconstructedHamiltonian (compilePinnedLocalPackage inputs)
  ≡
  OSR.reconstructedHamiltonian reconstruction group
pinnedLocalHamiltonianIsOSHamiltonian inputs =
  refl

pinnedCMP119LocalCSameHamiltonianCompilerLevel : ProofLevel
pinnedCMP119LocalCSameHamiltonianCompilerLevel = machineChecked

pinnedCMP119LocalCOpeRemainderCompilerLevel : ProofLevel
pinnedCMP119LocalCOpeRemainderCompilerLevel = machineChecked

-- Genuine C theorem content on the fixed A family/Hamiltonian.
literalCMP119CurvatureCompositeIdentificationLevel : ProofLevel
literalCMP119CurvatureCompositeIdentificationLevel = conditional

literalCMP119ShortDistanceAFMatchingLevel : ProofLevel
literalCMP119ShortDistanceAFMatchingLevel = conditional

literalCMP119StressWardSameOSHamiltonianLevel : ProofLevel
literalCMP119StressWardSameOSHamiltonianLevel = conditional
