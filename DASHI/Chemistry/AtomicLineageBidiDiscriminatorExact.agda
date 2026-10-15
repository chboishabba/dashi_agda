module DASHI.Chemistry.AtomicLineageBidiDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi
import DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact as Lineage
import DASHI.Biology.AtomicLineageTargetRecognitionBridgeExact as Recognition

------------------------------------------------------------------------
-- LINEAGE-AWARE BIDI DISCRIMINATORS
--
-- Standard experiment surface for: isotope tracing, ionic substitution,
-- molecular substitution, cofactor/redox perturbation and alternative-backbone
-- tests.  The existing BIDI loop owns hypothesis refinement and selective
-- dependency reopening; this owner supplies lineage-aware candidate/readout
-- coordinates only.
------------------------------------------------------------------------

data LineagePerturbationKind : Set where
  isotopeTracerPerturbation : LineagePerturbationKind
  ionicSubstitutionPerturbation : LineagePerturbationKind
  molecularSubstitutionPerturbation : LineagePerturbationKind
  cofactorPerturbation : LineagePerturbationKind
  redoxPerturbation : LineagePerturbationKind
  alternativeBackbonePerturbation : LineagePerturbationKind
  reactionEnvironmentPerturbation : LineagePerturbationKind

record LineageDiscriminatorCandidate : Set where
  constructor lineageDiscriminatorCandidate
  field
    candidateKey : String
    kind : LineagePerturbationKind
    liveHypothesesReference : String
    observerCollisionReference : String
    interventionReference : String
    interventionAuthorityReference : String
    atomLineageReadoutReference : String
    electronEquivalentReadoutReference : String
    bondGeometryReadoutReference : String
    moleculeProductByproductReadoutReference : String
    biologicalCarrierReadoutReference : String
    downstreamConsumerReference : String
    nuisanceControlReference : String
    calibrationReference : String
    predictedDiscriminatorReference : String
    provenanceReference : String

open LineageDiscriminatorCandidate public

candidateToBidiCycle : LineageDiscriminatorCandidate → Bidi.ActiveBidiCycleReceipt
candidateToBidiCycle c =
  Bidi.active-bidi-cycle-receipt
    (liveHypothesesReference c)
    (observerCollisionReference c)
    (candidateKey c)
    (nuisanceControlReference c)
    (interventionAuthorityReference c)
    (calibrationReference c)
    (provenanceReference c)
    "assimilate atom/electron/bond/molecule/biology readouts without rewriting the frozen consumer"
    "refine only the lineage/recognition fibres separated by the observed discriminator"
    "reopen dependency-affected reaction/biology/consumer certificates"
    (downstreamConsumerReference c)
    "close only when the declared downstream consumer is separated at required fidelity"
    "choose next unresolved lineage coordinate / perturbation by BIDI planner"
    Bidi.refineAgain

record AtomicLineageBidiDiscriminatorBoundary : Set where
  constructor atomicLineageBidiDiscriminatorBoundary
  field
    candidatePerturbationCreatesWorldTruth : Bool
    candidatePerturbationCreatesWorldTruthIsFalse :
      candidatePerturbationCreatesWorldTruth ≡ false
    isotopeTracerCanRefineAtomLineage : Bool
    isotopeTracerCanRefineAtomLineageIsTrue :
      isotopeTracerCanRefineAtomLineage ≡ true
    ionicSubstitutionCanProbeRecognitionCollision : Bool
    ionicSubstitutionCanProbeRecognitionCollisionIsTrue :
      ionicSubstitutionCanProbeRecognitionCollision ≡ true
    redoxPerturbationCanProbeElectronEquivalentFlow : Bool
    redoxPerturbationCanProbeElectronEquivalentFlowIsTrue :
      redoxPerturbationCanProbeElectronEquivalentFlow ≡ true
    onePerturbationIdentifiesWholeCrossScaleSystem : Bool
    onePerturbationIdentifiesWholeCrossScaleSystemIsFalse :
      onePerturbationIdentifiesWholeCrossScaleSystem ≡ false
    observedFineDifferenceReopensOnlyAffectedConsumers : Bool
    observedFineDifferenceReopensOnlyAffectedConsumersIsTrue :
      observedFineDifferenceReopensOnlyAffectedConsumers ≡ true
    interventionAuthorityIsIndependentObligation : Bool
    interventionAuthorityIsIndependentObligationIsTrue :
      interventionAuthorityIsIndependentObligation ≡ true

open AtomicLineageBidiDiscriminatorBoundary public

canonicalAtomicLineageBidiDiscriminatorBoundary :
  AtomicLineageBidiDiscriminatorBoundary
canonicalAtomicLineageBidiDiscriminatorBoundary =
  atomicLineageBidiDiscriminatorBoundary
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
