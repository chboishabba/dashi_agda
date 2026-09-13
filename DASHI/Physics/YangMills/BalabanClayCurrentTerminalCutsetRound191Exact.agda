{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound191Exact where

------------------------------------------------------------------------
-- ROUND191: CURRENT YANG--MILLS TERMINAL SOURCE CUT
--
-- This module is a scheduler correction, not a Clay proof.
--
-- Two recent reductions materially change the preferred search surface:
--
--   * Eq. (119) now has exactly four independent least-privilege source
--     payments on the preferred Path13 route;
--   * M7b operator-domain construction and M7c self-adjointness are no longer
--     independent theorem searches on the preferred route: Kato's first
--     representation theorem compiles both from one physical densely-defined
--     closed semibounded form.  A common invariant operator core and the
--     physical action-variation/Hamiltonian same-object identification remain
--     separate obligations;
--   * T5 removes reconstructed-theory/interlacing values and their historical
--     agreement equalities as primitive inputs.  Only their producer maps
--     survive, together with the physical continuum/OS/clustering inputs.
--
-- Therefore the old Round146 source hypergraph and the Round190 raw M7 status
-- are useful archaeology but are not the preferred proof-search cutset.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Path13CurrentPreferredSourceFrontierExact as Eq119
import DASHI.Physics.YangMills.YMKatoClosedFormHamiltonianExact as Kato
import DASHI.Physics.YangMills.BalabanClayT5PreferredContinuumOSGapExact as T5
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier
import DASHI.Physics.Closure.YMClayPromotionBoundary as Clay

------------------------------------------------------------------------
-- Preferred terminal producer classes.
------------------------------------------------------------------------

data YMTerminalProducer : Set where
  eq119R171AlignedPhysicalSource : YMTerminalProducer
  eq119SelectedPrintedSemantics : YMTerminalProducer
  eq119Relative74CutThreshold : YMTerminalProducer
  eq119RationalRealRingEmbedding : YMTerminalProducer

  m7PhysicalClosedSemiboundedForm : YMTerminalProducer
  m7CommonInvariantOperatorCore : YMTerminalProducer
  m7ActionVariationHamiltonianSameObject : YMTerminalProducer

  t5PhysicalMeasureToOSGram : YMTerminalProducer
  t5FiniteToContinuumOSClosure : YMTerminalProducer
  t5MeasureSequenceSameObject : YMTerminalProducer
  t5ContinuumMeasureSameObject : YMTerminalProducer
  t5GramReflectionToClosureReflection : YMTerminalProducer
  t5ConditionalClusteringAssembly : YMTerminalProducer
  t5ClusteringToClosureClustering : YMTerminalProducer
  t5OSReconstructionProducer : YMTerminalProducer
  t5GapToPhysicalInterlacingProducer : YMTerminalProducer

  m8YMEvolutionEqualsOSReconstructedEvolution : YMTerminalProducer
  m9PhysicalVacuumRecoverySystem : YMTerminalProducer

preferredTerminalCut : List YMTerminalProducer
preferredTerminalCut =
  eq119R171AlignedPhysicalSource ∷
  eq119SelectedPrintedSemantics ∷
  eq119Relative74CutThreshold ∷
  eq119RationalRealRingEmbedding ∷
  m7PhysicalClosedSemiboundedForm ∷
  m7CommonInvariantOperatorCore ∷
  m7ActionVariationHamiltonianSameObject ∷
  t5PhysicalMeasureToOSGram ∷
  t5FiniteToContinuumOSClosure ∷
  t5MeasureSequenceSameObject ∷
  t5ContinuumMeasureSameObject ∷
  t5GramReflectionToClosureReflection ∷
  t5ConditionalClusteringAssembly ∷
  t5ClusteringToClosureClustering ∷
  t5OSReconstructionProducer ∷
  t5GapToPhysicalInterlacingProducer ∷
  m8YMEvolutionEqualsOSReconstructedEvolution ∷
  m9PhysicalVacuumRecoverySystem ∷ []

------------------------------------------------------------------------
-- Exact inherited Eq. (119) status.
------------------------------------------------------------------------

eq119CompilerAlreadyClosed :
  Eq119.currentPreferredEq119CompilerClosed
    Eq119.canonicalCurrentPreferredEq119FrontierStatus ≡ true
eq119CompilerAlreadyClosed = Eq119.currentPreferredEq119CompilerClosedIsTrue

eq119PhysicalSourceStillOpen :
  Eq119.r171AlignedPath13PhysicalSourceConstructed
    Eq119.canonicalCurrentPreferredEq119FrontierStatus ≡ false
eq119PhysicalSourceStillOpen = refl

eq119PrintedSemanticsStillOpen :
  Eq119.selectedPrintedSemanticsConstructed
    Eq119.canonicalCurrentPreferredEq119FrontierStatus ≡ false
eq119PrintedSemanticsStillOpen = refl

eq119Relative74CutStillOpen :
  Eq119.relative74CutThresholdConstructed
    Eq119.canonicalCurrentPreferredEq119FrontierStatus ≡ false
eq119Relative74CutStillOpen = refl

eq119ScalarEmbeddingStillOpen :
  Eq119.rationalRealRingEmbeddingConstructed
    Eq119.canonicalCurrentPreferredEq119FrontierStatus ≡ false
eq119ScalarEmbeddingStillOpen = refl

------------------------------------------------------------------------
-- M7 minimization: domain + self-adjointness share one producer.
------------------------------------------------------------------------

M7PreferredOperatorInput : Set → Set → Set₁
M7PreferredOperatorInput = Kato.KatoM7OperatorPackage

-- Keep the executable dependent compiler under the canonical Kato owner.
-- Round191 exposes its proof level and source cut rather than duplicating the
-- result type and accidentally creating a parallel terminal API.
m7DomainAndSelfAdjointnessCompilerLevel : ProofLevel
m7DomainAndSelfAdjointnessCompilerLevel = Kato.katoClosedFormHamiltonianCompilerLevel

m7KatoAuthorityLevel : ProofLevel
m7KatoAuthorityLevel = Kato.katoFirstRepresentationTheoremAuthorityLevel

m7PhysicalClosedFormStillConditional : ProofLevel
m7PhysicalClosedFormStillConditional = Kato.literalPhysicalYMClosedSemiboundedFormLevel

m7CommonInvariantCoreStillConditional : ProofLevel
m7CommonInvariantCoreStillConditional = Kato.literalPhysicalYMCommonInvariantOperatorCoreLevel

m7ActionVariationSameObjectStillOpen :
  Frontier.physicalActionVariationHamiltonianSameObjectClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7ActionVariationSameObjectStillOpen = refl

m7RawDomainStatusStillOpen :
  Frontier.genuinePartialDomainHamiltonianFormalized
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7RawDomainStatusStillOpen = refl

m7RawSelfAdjointStatusStillOpen :
  Frontier.physicalSelfAdjointSelectedYMFormClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7RawSelfAdjointStatusStillOpen = refl

-- Scheduler law: the two raw false coordinates above must not be interpreted as
-- two independent analytic theorem searches. Their preferred producer is the
-- one Kato package; the common invariant core is not produced by Kato.

------------------------------------------------------------------------
-- T5 minimization.
------------------------------------------------------------------------

T5PreferredInput :
  Set → Set → Set → Set → Set → Set → Set → Set → Set₁
T5PreferredInput = T5.PreferredPhysicalContinuumOSGapInputs

t5CompilerAlreadyClosed : ProofLevel
t5CompilerAlreadyClosed = T5.preferredPhysicalContinuumOSGapCompilerLevel

t5PhysicalContinuumInputsStillConditional : ProofLevel
t5PhysicalContinuumInputsStillConditional =
  T5.literalPhysicalUVToContinuumMeasureInputsLevel

t5OSReconstructionInputsStillConditional : ProofLevel
t5OSReconstructionInputsStillConditional =
  T5.literalPhysicalOSReconstructionInputsLevel

t5GapTransportInputsStillConditional : ProofLevel
t5GapTransportInputsStillConditional =
  T5.literalPhysicalGapToInterlacingInputsLevel

------------------------------------------------------------------------
-- Remaining promotion-facing continuum coordinates.
------------------------------------------------------------------------

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

ymEvolutionSameObjectStillOpen :
  Frontier.ymEvolutionEqualsOSReconstructedEvolutionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
ymEvolutionSameObjectStillOpen = refl

physicalVacuumRecoveryStillOpen :
  Frontier.physicalVacuumRecoverySystemConstructed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
physicalVacuumRecoveryStillOpen = refl

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

clayPromotionStillFailClosed : Clay.clayYangMillsPromoted ≡ false
clayPromotionStillFailClosed = refl

------------------------------------------------------------------------
-- Proof/search classification.
------------------------------------------------------------------------

currentYMTerminalCutsetRound191Level : ProofLevel
currentYMTerminalCutsetRound191Level = machineChecked

literalTerminalProducerInhabitationLevel : ProofLevel
literalTerminalProducerInhabitationLevel = conditional
