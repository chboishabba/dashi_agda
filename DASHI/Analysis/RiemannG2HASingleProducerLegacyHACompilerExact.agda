module DASHI.Analysis.RiemannG2HASingleProducerLegacyHACompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact as Character
import DASHI.Analysis.RiemannAnalyticTestModulationShiftExact as LegacyHA
import DASHI.Analysis.RiemannG2ConstructedComplexAnalyticCarrierAdapterExact as Carrier
import DASHI.Analysis.RiemannG2CanonicalTestModulationProofRelevantExact as StrongHA
import DASHI.Analysis.RiemannG2HASingleSourceProducerBidiExact as Single

------------------------------------------------------------------------
-- SINGLE-PRODUCER -> LEGACY H_A COMPILER
--
-- The historical H_A interface is weaker than the proof-relevant canonical
-- owner: several of its agreement/shift fields are proposition-valued Set
-- sockets rather than proof fields.  Once one ActualHASingleSourceProducer is
-- recovered, the stronger canonical H_A is already compiler output.  This file
-- shows that the historical RiemannTestModulationShift interface is therefore
-- also compiler output; it is not another independent scientific leaf.
--
-- This does NOT yet construct H_M.  The historical H_M extension carries a
-- richer frequency/character/spectral-response representation, so the next
-- seam is an exact representation/transport bridge from canonical H_X + the
-- proof-relevant H_A into that legacy extension shape.
------------------------------------------------------------------------

singleProducerToLegacyHA :
  ∀ {analytic space formula compat C F realization} →
  (H_X : Character.RiemannComplexCharacterExtension analytic) →
  (producer : Single.ActualHASingleSourceProducer analytic space formula compat) →
  LegacyHA.RiemannTestModulationShift analytic space formula compat H_X
singleProducerToLegacyHA {analytic} {space} {formula} {compat}
  {C} {F} {realization} H_X producer =
  let P : StrongHA.ProofRelevantCanonicalTestModulation
            analytic space formula compat C F realization
      P = Single.singleProducerToProofRelevantCanonicalHA producer
  in
  LegacyHA.riemann-test-modulation-shift
    -- carrierAgreementUsed
    (Weil.WeilTestSpace.Scalar space
      ≡ Analytic.ComplexAnalyticCarrier.Real
          (Analytic.AnalyticSubstrate.carrier analytic))
    -- explicitFormulaAgreementUsed
    ⊤
    -- characterAgreementUsed
    ((t : Weil.WeilTestSpace.Scalar space) →
     (f : Weil.WeilTestSpace.Test space) →
     StrongHA.modulateTest P t f
     ≡ StrongHA.expectedCharacterAction P t f)
    -- Target
    (Weil.WeilTestSpace.Scalar space)
    -- targetCarrierMatchesHXReal
    (Weil.WeilTestSpace.Scalar space ≡ Character.RealCarrier H_X)
    -- modulateTest
    (StrongHA.modulateTest P)
    -- modulationPreservesAdmissibility
    (StrongHA.modulationPreservesAdmissibility P)
    -- SpectralResponse
    (Weil.WeilTestSpace.Scalar space)
    -- shiftedSpectralResponse
    (λ t f → Explicit.RiemannExplicitFormula.spectralZeroForm formula
      (StrongHA.modulateTest P t f))
    -- unshiftedSpectralResponse
    (Explicit.RiemannExplicitFormula.spectralZeroForm formula)
    -- targetCharacterActsOnSpectralResponse
    ((t : Weil.WeilTestSpace.Scalar space) →
     (f : Weil.WeilTestSpace.Test space) →
     StrongHA.modulateTest P t f
     ≡ StrongHA.expectedCharacterAction P t f)
    -- spectralShiftLaw
    ((t : Weil.WeilTestSpace.Scalar space) →
     (f : Weil.WeilTestSpace.Test space) →
     Explicit.RiemannExplicitFormula.spectralZeroForm formula
       (StrongHA.modulateTest P t f)
     ≡ StrongHA.expectedShiftedSpectralResponse P t f)
    -- shiftedResponseBelongsToConcreteSpectralZeroForm
    ((t : Weil.WeilTestSpace.Scalar space) →
     (f : Weil.WeilTestSpace.Test space) →
     Explicit.RiemannExplicitFormula.spectralZeroForm formula
       (StrongHA.modulateTest P t f)
     ≡ StrongHA.expectedShiftedSpectralResponse P t f)
    -- transformShiftUsesCanonicalWeilTransform
    ((t : Weil.WeilTestSpace.Scalar space) →
     (f : Weil.WeilTestSpace.Test space) →
     Weil.WeilTestSpace.transform space (StrongHA.modulateTest P t f)
     ≡ StrongHA.expectedTransformShift P t f)
    -- mellinCarrierCompatibilityUsed
    (Weil.WeilTestSpace.Test space
      ≡ Analytic.GammaMellinLayer.Test
          (Analytic.AnalyticSubstrate.gammaMellin analytic))
    -- actionReference
    (StrongHA.producerReference P)

------------------------------------------------------------------------
-- Search consequence: the old H_A node is no longer an independent leaf once
-- the single source producer is targeted.
------------------------------------------------------------------------

data PostSingleProducerSearchAction : Set where
  recoverActualSingleSourceProducer
  rebuildLegacyHAInterface
  constructLegacyHMRepresentationBridge
  recoverPoleNearHTAdapter
  : PostSingleProducerSearchAction

data SearchStatus : Set where
  live pruned downstream : SearchStatus

searchStatus : PostSingleProducerSearchAction → SearchStatus
searchStatus recoverActualSingleSourceProducer = live
searchStatus rebuildLegacyHAInterface = pruned
searchStatus constructLegacyHMRepresentationBridge = downstream
searchStatus recoverPoleNearHTAdapter = downstream

legacyHARebuildPruned :
  searchStatus rebuildLegacyHAInterface ≡ pruned
legacyHARebuildPruned = refl

record HASingleProducerLegacyCompilerBoundary : Set where
  constructor ha-single-producer-legacy-compiler-boundary
  field
    proofRelevantSingleProducerGeneratesLegacyHA : Bool
    proofRelevantSingleProducerGeneratesLegacyHAIsTrue :
      proofRelevantSingleProducerGeneratesLegacyHA ≡ true

    legacyHARequiresIndependentSourceRecoveryAfterSingleProducer : Bool
    legacyHARequiresIndependentSourceRecoveryAfterSingleProducerIsFalse :
      legacyHARequiresIndependentSourceRecoveryAfterSingleProducer ≡ false

    legacyHMIsAlreadyGeneratedByThisCompiler : Bool
    legacyHMIsAlreadyGeneratedByThisCompilerIsFalse :
      legacyHMIsAlreadyGeneratedByThisCompiler ≡ false

    nextSeamIsRepresentationTransportIntoLegacyHM : Bool
    nextSeamIsRepresentationTransportIntoLegacyHMIsTrue :
      nextSeamIsRepresentationTransportIntoLegacyHM ≡ true

    sourceProducerRecoveredHere : Bool
    sourceProducerRecoveredHereIsFalse : sourceProducerRecoveredHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHASingleProducerLegacyCompilerBoundary :
  HASingleProducerLegacyCompilerBoundary
canonicalHASingleProducerLegacyCompilerBoundary =
  ha-single-producer-legacy-compiler-boundary
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    "Once the dependent source-native H_A producer is recovered, the stronger proof-relevant canonical modulation object compiles directly into the historical RiemannTestModulationShift interface. Do not search for a second legacy H_A implementation. The remaining H_M seam is narrower and representational: transport canonical H_X plus this proof-relevant test action into the richer historical modulation-extension frequency/character/spectral-response shape required by H_T. No producer is recovered and RH is not derived here."
