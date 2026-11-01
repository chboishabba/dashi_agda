module DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Canonical
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel
import DASHI.Core.IdentifiabilityActiveInformationExact as Active

------------------------------------------------------------------------
-- PURPOSE
--
-- Collapse the new consumer-relative reduction surface onto already-owned
-- canonical DASHI semantics instead of allowing it to become a parallel ROM
-- theory.  A certified reduction gives:
--
--   * ordinary current consumer descent;
--   * one-step intertwining for every admitted action;
--   * a kernel contained in canonical future-observation equivalence;
--   * an exact active-information discriminator when a measurement splits a
--     reduced collision.
--
-- Conversely, one finite future-separating collision refutes canonical future
-- safety of the candidate projection.  This is the reusable proof-search seam
-- behind cheap-model falsification and fidelity escalation.
------------------------------------------------------------------------

currentConsumerDescent :
  ∀ {Fine Action Observation}
    (rom : Reduction.ConsumerRelativeReduction Fine Action Observation) →
  Kernel.ConsumerDescent (Reduction.encode rom) (Reduction.fineObserve rom)
currentConsumerDescent rom =
  Kernel.consumerDescent
    (Reduction.reducedObserve rom)
    (Reduction.observationFactors rom)

actionIntertwiner :
  ∀ {Fine Action Observation}
    (rom : Reduction.ConsumerRelativeReduction Fine Action Observation) →
  (action : Action) →
  Kernel.Intertwiner
    (Reduction.encode rom)
    (Reduction.encode rom)
    (Reduction.fineStep rom action)
    (Reduction.reducedStep rom action)
actionIntertwiner rom action =
  Kernel.intertwiner (Reduction.stepCommutes rom action)

symmetryIntertwiner :
  ∀ {Fine Action Observation}
    {rom : Reduction.ConsumerRelativeReduction Fine Action Observation}
    {fineSymmetry : Reduction.SymmetryAction Fine}
    {reducedSymmetry : Reduction.SymmetryAction (Reduction.Reduced rom)} →
  (compatible :
    Reduction.SymmetryCompatibleReduction rom fineSymmetry reducedSymmetry) →
  (g : Reduction.Symmetry fineSymmetry) →
  Kernel.Intertwiner
    (Reduction.encode rom)
    (Reduction.encode rom)
    (Reduction.act fineSymmetry g)
    (Reduction.act reducedSymmetry (Reduction.symmetryMap compatible g))
symmetryIntertwiner compatible g =
  Kernel.intertwiner (Reduction.encodeEquivariant compatible g)

------------------------------------------------------------------------
-- Exact bridge to the canonical future-observation quotient.
------------------------------------------------------------------------

canonicalFutureSafety :
  ∀ {Fine Action Observation}
    (rom : Reduction.ConsumerRelativeReduction Fine Action Observation) →
  (actionLabel : Action → String) →
  Future.FutureLanguageSafeProjection
    (Canonical.deterministicSystem (Reduction.fineStep rom) actionLabel)
    (Reduction.fineObserve rom)
    (Reduction.encode rom)
canonicalFutureSafety rom actionLabel =
  Future.futureLanguageSafeProjection λ sameCode →
    Canonical.traceEquivalentImpliesCanonicalFutureEquivalent
      (Reduction.encodedEqualityImpliesConsumerFutureEquality rom sameCode)

canonicalFutureKernelSubrelation :
  ∀ {Fine Action Observation}
    (rom : Reduction.ConsumerRelativeReduction Fine Action Observation) →
  (actionLabel : Action → String) →
  Future.KernelSubrelation
    (Reduction.encode rom)
    (Future.FutureObservationEquivalent
      (Canonical.deterministicSystem (Reduction.fineStep rom) actionLabel)
      (Reduction.fineObserve rom))
canonicalFutureKernelSubrelation rom actionLabel =
  Future.safeProjectionKernelFactorsThroughFutureEquivalence
    (canonicalFutureSafety rom actionLabel)

------------------------------------------------------------------------
-- Optional symmetry quotient theorem.
--
-- Equivariance alone does NOT mean the symmetry should be quotiented out.  The
-- reduced action must additionally fix the represented state for the declared
-- consumer.  Only then is the fine symmetry orbit consumer-future invisible.
------------------------------------------------------------------------

record ConsumerInvisibleSymmetry
    {Fine Action Observation : Set}
    {rom : Reduction.ConsumerRelativeReduction Fine Action Observation}
    {fineSymmetry : Reduction.SymmetryAction Fine}
    {reducedSymmetry : Reduction.SymmetryAction (Reduction.Reduced rom)}
    (compatible :
      Reduction.SymmetryCompatibleReduction rom fineSymmetry reducedSymmetry) : Set₁ where
  constructor consumerInvisibleSymmetry
  field
    reducedOrbitFixed :
      (g : Reduction.Symmetry fineSymmetry) (state : Fine) →
      Reduction.act reducedSymmetry
        (Reduction.symmetryMap compatible g)
        (Reduction.encode rom state)
      ≡ Reduction.encode rom state

open ConsumerInvisibleSymmetry public

symmetryOrbitCollapsesInReduction :
  ∀ {Fine Action Observation}
    {rom : Reduction.ConsumerRelativeReduction Fine Action Observation}
    {fineSymmetry : Reduction.SymmetryAction Fine}
    {reducedSymmetry : Reduction.SymmetryAction (Reduction.Reduced rom)}
    {compatible :
      Reduction.SymmetryCompatibleReduction rom fineSymmetry reducedSymmetry} →
  ConsumerInvisibleSymmetry compatible →
  (g : Reduction.Symmetry fineSymmetry) →
  (state : Fine) →
  Reduction.encode rom (Reduction.act fineSymmetry g state)
  ≡ Reduction.encode rom state
symmetryOrbitCollapsesInReduction {compatible = compatible} invisible g state =
  trans
    (Reduction.encodeEquivariant compatible g state)
    (reducedOrbitFixed invisible g state)

symmetryOrbitIsCanonicalFutureEquivalent :
  ∀ {Fine Action Observation}
    {rom : Reduction.ConsumerRelativeReduction Fine Action Observation}
    {fineSymmetry : Reduction.SymmetryAction Fine}
    {reducedSymmetry : Reduction.SymmetryAction (Reduction.Reduced rom)}
    {compatible :
      Reduction.SymmetryCompatibleReduction rom fineSymmetry reducedSymmetry} →
  ConsumerInvisibleSymmetry compatible →
  (actionLabel : Action → String) →
  (g : Reduction.Symmetry fineSymmetry) →
  (state : Fine) →
  Future.FutureObservationEquivalent
    (Canonical.deterministicSystem (Reduction.fineStep rom) actionLabel)
    (Reduction.fineObserve rom)
    (Reduction.act fineSymmetry g state)
    state
symmetryOrbitIsCanonicalFutureEquivalent {rom = rom} invisible actionLabel g state =
  Future.kernelContainedInFutureEquivalence
    (canonicalFutureSafety rom actionLabel)
    (symmetryOrbitCollapsesInReduction invisible g state)

consumerVisibleSymmetryCannotBeQuotiented :
  ∀ {Fine Action Observation}
    (rom : Reduction.ConsumerRelativeReduction Fine Action Observation) →
  {left right : Fine} →
  Reduction.encode rom left ≡ Reduction.encode rom right →
  (Reduction.fineObserve rom left ≡ Reduction.fineObserve rom right → ⊥) →
  ⊥
consumerVisibleSymmetryCannotBeQuotiented rom sameCode visibleDifference =
  visibleDifference
    (trans
      (Reduction.observationFactors rom _)
      (trans
        (cong (Reduction.reducedObserve rom) sameCode)
        (sym (Reduction.observationFactors rom _))))

------------------------------------------------------------------------
-- Active measurement discrimination is already the repo's generic
-- DistinguishingExperiment theorem with a singleton experiment language.
------------------------------------------------------------------------

singletonMeasurementSystem :
  ∀ {Fine Action Observation}
    {rom : Reduction.ConsumerRelativeReduction Fine Action Observation}
    {left right : Fine} →
  (discriminator : Reduction.MeasurementDiscriminator rom left right) →
  Active.ExperimentSystem Fine ⊤ (Reduction.Measurement discriminator)
singletonMeasurementSystem discriminator =
  Active.experimentSystem
    (λ _ state → Reduction.measure discriminator state)

measurementDiscriminatorIsActiveExperiment :
  ∀ {Fine Action Observation}
    {rom : Reduction.ConsumerRelativeReduction Fine Action Observation}
    {left right : Fine} →
  (discriminator : Reduction.MeasurementDiscriminator rom left right) →
  Active.DistinguishingExperiment
    (singletonMeasurementSystem discriminator)
    left right
measurementDiscriminatorIsActiveExperiment discriminator =
  Active.distinguishingExperiment
    tt
    (Reduction.measurementSeparates discriminator)

------------------------------------------------------------------------
-- Negative direction: a single future consumer counterexample is sufficient to
-- reject a candidate as a canonical future-safe projection for that consumer.
------------------------------------------------------------------------

candidateFailureAsTraceConsumerDefect :
  ∀ {Fine Action Observation CandidateCode}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {candidate : Fine → CandidateCode} →
  (failure : Reduction.CandidateReductionFailure fineStep observe candidate) →
  Kernel.ConsumerDescentDefect
    candidate
    (λ state →
      observe
        (Reduction.run fineStep
          (Reduction.separatingTrace failure) state))
candidateFailureAsTraceConsumerDefect failure =
  Kernel.consumerDescentDefect
    (Reduction.left failure)
    (Reduction.right failure)
    (Reduction.candidateCollides failure)
    (Reduction.futureConsumerSeparates failure)

candidateFailureContradictsCanonicalFutureSafety :
  ∀ {Fine Action Observation CandidateCode}
    {fineStep : Action → Fine → Fine}
    {observe : Fine → Observation}
    {candidate : Fine → CandidateCode}
    (actionLabel : Action → String) →
  Reduction.CandidateReductionFailure fineStep observe candidate →
  Future.FutureLanguageSafeProjection
    (Canonical.deterministicSystem fineStep actionLabel)
    observe
    candidate →
  ⊥
candidateFailureContradictsCanonicalFutureSafety actionLabel failure safe =
  Reduction.futureConsumerSeparates failure
    (Canonical.canonicalFutureEquivalentImpliesTraceEquivalent
      (Future.kernelContainedInFutureEquivalence safe
        (Reduction.candidateCollides failure))
      (Reduction.separatingTrace failure))

certifiedReductionCannotCarryFutureCounterexample :
  ∀ {Fine Action Observation}
    (rom : Reduction.ConsumerRelativeReduction Fine Action Observation) →
  (actionLabel : Action → String) →
  Reduction.CandidateReductionFailure
    (Reduction.fineStep rom)
    (Reduction.fineObserve rom)
    (Reduction.encode rom) →
  ⊥
certifiedReductionCannotCarryFutureCounterexample rom actionLabel failure =
  candidateFailureContradictsCanonicalFutureSafety
    actionLabel failure (canonicalFutureSafety rom actionLabel)

------------------------------------------------------------------------
-- Boundary: this bridge introduces no external scientific source claim.  It
-- identifies theorem surfaces already present in the repository.
------------------------------------------------------------------------

record ConsumerReductionCanonicalBridgeBoundary : Set where
  constructor consumerReductionCanonicalBridgeBoundary
  field
    certifiedReductionKernelIsCanonicalFutureSafe : Bool
    symmetryCompatibilityIsJustAnotherIntertwiningReceipt : Bool
    invisibleSymmetryNeedsReducedOrbitFixedness : Bool
    invisibleSymmetryOrbitIsCanonicalFutureEquivalent : Bool
    consumerVisibleSymmetryCannotBeSilentlyQuotiented : Bool
    oneFutureCounterexampleRefutesCandidateFutureSafety : Bool
    measurementSplitterReusesActiveInformationSemantics : Bool
    canonicalFutureSafetyImpliesMechanisticRealization : Bool
    canonicalFutureSafetyImpliesMechanisticRealizationIsFalse :
      canonicalFutureSafetyImpliesMechanisticRealization ≡ false

canonicalConsumerReductionCanonicalBridgeBoundary :
  ConsumerReductionCanonicalBridgeBoundary
canonicalConsumerReductionCanonicalBridgeBoundary =
  consumerReductionCanonicalBridgeBoundary
    true true true true true true true false refl
