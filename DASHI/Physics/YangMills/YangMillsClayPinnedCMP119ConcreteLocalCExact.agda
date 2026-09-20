{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact where

------------------------------------------------------------------------
-- LITERAL C / PREFERRED CONCRETE AF + STRESS PRESENTATION
--
-- The older pinned C input record permits arbitrary predicates named
-- ShortDistanceAFMatching and SpatialIntegralT00Generates.  This preferred
-- owner replaces them by concrete equalities:
--
--   coefficient(...) = selected AF coefficient(...)
--
-- and
--
--   stressCharge(T) = reconstructed CMP119 OS Hamiltonian.
--
-- The second equality is compiled from common-core Ward/closure data by the
-- pinned Round86 adapter, so it is not an independent physical premise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LocalCExact as C
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressCommonCoreExact as Common
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.YangMillsSharedMarkedCompositeOPERemainderExact as MarkedOPE
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedCMP119ConcreteLocalCInputs
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core : Set)
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

    -- Concrete C3 shape: selected literal coefficient equals the AF coordinate.
    asymptoticallyFreeCoefficient :
      LocalOperator → LocalOperator → LocalOperator → Position → OPECoefficient

    coefficientMatchesAsymptoticFreedom :
      ∀ left right output position →
      coefficient left right output position
      ≡ asymptoticallyFreeCoefficient left right output position

    stressTensor : StressTensor
    Symmetric : StressTensor → Set
    ConservedInCorrelators : StressTensor → Set
    LocalStressTensor : StressTensor → Set
    stressTensorSymmetric : Symmetric stressTensor
    stressTensorConserved : ConservedInCorrelators stressTensor
    stressTensorLocal : LocalStressTensor stressTensor

    -- Concrete C6 producer on the SAME pinned reconstruction.
    stressCommonCore :
      Common.PinnedStressCommonCoreData
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        Hilbert Vector Hamiltonian Algebra Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} {osInputs = osInputs} reconstruction group

    stressTensorIsCommonCoreStress :
      stressTensor ≡ Common.stressTensor stressCommonCore

open PinnedCMP119ConcreteLocalCInputs public

stressChargeGeneratesPinnedHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) →
  Common.stressCharge (stressCommonCore inputs) (stressTensor inputs)
  ≡ OSR.reconstructedHamiltonian reconstruction group
stressChargeGeneratesPinnedHamiltonian
    {reconstruction = reconstruction} {group = group} inputs =
  subst
    (λ selectedStress →
      Common.stressCharge (stressCommonCore inputs) selectedStress
      ≡ OSR.reconstructedHamiltonian reconstruction group)
    (sym (stressTensorIsCommonCoreStress inputs))
    (Common.stressChargeEqualsPinnedOSHamiltonian
      (stressCommonCore inputs))

asPinnedLocalCInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group} →
  PinnedCMP119ConcreteLocalCInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    Scale Volume Root ContinuumFamily Core
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} osInputs reconstruction group →
  C.PinnedCMP119LocalCInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    Scale Volume Root ContinuumFamily
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} osInputs reconstruction group
asPinnedLocalCInputs inputs = record
  { C.PinnedCMP119LocalCInputs.shared =
      shared inputs
  ; C.PinnedCMP119LocalCInputs.selectedScale =
      selectedScale inputs
  ; C.PinnedCMP119LocalCInputs.selectedVolume =
      selectedVolume inputs
  ; C.PinnedCMP119LocalCInputs.selectedRoot =
      selectedRoot inputs
  ; C.PinnedCMP119LocalCInputs.remaining =
      remaining inputs
  ; C.PinnedCMP119LocalCInputs.continuumFamily =
      continuumFamily inputs
  ; C.PinnedCMP119LocalCInputs.localOperator =
      localOperator inputs
  ; C.PinnedCMP119LocalCInputs.GaugeInvariant =
      GaugeInvariant inputs
  ; C.PinnedCMP119LocalCInputs.LocalAt =
      LocalAt inputs
  ; C.PinnedCMP119LocalCInputs.curvatureOperatorsGaugeInvariant =
      curvatureOperatorsGaugeInvariant inputs
  ; C.PinnedCMP119LocalCInputs.curvatureOperatorsLocal =
      curvatureOperatorsLocal inputs
  ; C.PinnedCMP119LocalCInputs.OPEAdmissible =
      OPEAdmissible inputs
  ; C.PinnedCMP119LocalCInputs.coefficient =
      coefficient inputs
  ; C.PinnedCMP119LocalCInputs.physicalRemainder =
      physicalRemainder inputs
  ; C.PinnedCMP119LocalCInputs.physicalRemainderIsCompositeTail =
      physicalRemainderIsCompositeTail inputs
  ; C.PinnedCMP119LocalCInputs.ShortDistanceAFMatching =
      ∀ left right output position →
      coefficient inputs left right output position
      ≡ asymptoticallyFreeCoefficient inputs left right output position
  ; C.PinnedCMP119LocalCInputs.shortDistanceAFMatching =
      coefficientMatchesAsymptoticFreedom inputs
  ; C.PinnedCMP119LocalCInputs.stressTensor =
      stressTensor inputs
  ; C.PinnedCMP119LocalCInputs.Symmetric =
      Symmetric inputs
  ; C.PinnedCMP119LocalCInputs.ConservedInCorrelators =
      ConservedInCorrelators inputs
  ; C.PinnedCMP119LocalCInputs.LocalStressTensor =
      LocalStressTensor inputs
  ; C.PinnedCMP119LocalCInputs.stressTensorSymmetric =
      stressTensorSymmetric inputs
  ; C.PinnedCMP119LocalCInputs.stressTensorConserved =
      stressTensorConserved inputs
  ; C.PinnedCMP119LocalCInputs.stressTensorLocal =
      stressTensorLocal inputs
  ; C.PinnedCMP119LocalCInputs.SpatialIntegralT00Generates =
      λ stress hamiltonian →
        Common.stressCharge (stressCommonCore inputs) stress
        ≡ hamiltonian
  ; C.PinnedCMP119LocalCInputs.stressTensorGeneratesOSHamiltonian =
      stressChargeGeneratesPinnedHamiltonian inputs
  }

compileConcretePinnedLocalPackage :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) →
  Local.ContinuumLocalOperatorOPEStressTensor
    ContinuumFamily CurvaturePolynomial LocalOperator Position
    OPECoefficient StressTensor Hamiltonian
compileConcretePinnedLocalPackage inputs =
  C.compilePinnedLocalPackage (asPinnedLocalCInputs inputs)

pinnedConcreteAFMatchingAdapterLevel : ProofLevel
pinnedConcreteAFMatchingAdapterLevel = machineChecked

pinnedConcreteStressSameHamiltonianAdapterLevel : ProofLevel
pinnedConcreteStressSameHamiltonianAdapterLevel = machineChecked

-- Remaining C physics is now concentrated in:
-- * actual same-family renormalized curvature/composite local fields;
-- * equality of the selected coefficient with the physical AF coordinate;
-- * continuum Ward/locality/common-core closure for the renormalized stress.
literalPinnedCurvatureCompositeFieldLevel : ProofLevel
literalPinnedCurvatureCompositeFieldLevel = conditional

literalPinnedAFCoefficientIdentificationLevel : ProofLevel
literalPinnedAFCoefficientIdentificationLevel = conditional

literalPinnedStressWardCommonCoreLevel : ProofLevel
literalPinnedStressWardCommonCoreLevel = Common.literalPinnedStressWardCommonCoreLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
