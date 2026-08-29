module DASHI.Cognition.PNF.DirectStreamingRoadmapSynthesisExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.DirectDeltaCompilerActivationExact as Activation
import DASHI.Cognition.PNF.DirectDeltaCompilerArchitectureExact as Direct
import DASHI.Cognition.PNF.StreamingSemanticPacmanKernelExact as Streaming

------------------------------------------------------------------------
-- Roadmap synthesis after the measured direct-path optimization tranche.
--
-- The roadmap separates semantic certification from performance evolution.
-- A cold direct build need not satisfy the final performance aspiration before
-- parity and production activation can be certified.  The streaming/delta
-- architecture is precisely what is intended to reduce remaining work.
------------------------------------------------------------------------

data RoadmapStage : Set where
  directMechanism
  boundedParity
  productionCutover
  streamingDeltaHierarchy
  systemRebenchmark : RoadmapStage

record CertificationFrontier : Set where
  constructor certificationFrontier
  field
    activation : Activation.DirectSentenceActivation
    currentStage : RoadmapStage

    -- Current executable mechanisms: packed parser carrier, DB-free local solve,
    -- stable evidence-native support.  Parity is still the next certification
    -- gate rather than a performance micro-optimization prerequisite.
    parserCarrierReady :
      Activation.parserCarrierGate activation ≡ Activation.executable
    localSolveReady :
      Activation.localSolveGate activation ≡ Activation.executable
    evidenceCarrierReady :
      Activation.tokenRetirementGate activation ≡ Activation.executable
    parityStillRequired :
      Activation.parityGate activation ≡ Activation.inactive

open CertificationFrontier public

currentDirectCertificationFrontier : CertificationFrontier
currentDirectCertificationFrontier =
  certificationFrontier
    Activation.sensibLawPackedDirectSeam
    boundedParity
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Performance receipts belong to runtime measurement.
--
-- Cold full-build latency and incremental/delta latency are distinct metrics.
-- The formal roadmap records both so an expensive cold publication path cannot
-- hide whether the delta-native architecture actually avoids repeated work.
------------------------------------------------------------------------

record RuntimePerformanceReceipt : Set where
  constructor runtimePerformanceReceipt
  field
    parserWork : Nat
    consumedDuringParserStream : Nat
    remainingAfterParserStream : Nat
    coldDirectWork : Nat
    incrementalAffectedWork : Nat

open RuntimePerformanceReceipt public

------------------------------------------------------------------------
-- Production certification remains fail closed.
------------------------------------------------------------------------

data PerformanceReceiptAloneActivatesProduction : Set where

data StreamingKernelAloneActivatesProduction : Set where

performanceAloneCannotReplaceParity :
  PerformanceReceiptAloneActivatesProduction → ⊥
performanceAloneCannotReplaceParity ()

streamingArchitectureAloneCannotReplaceParity :
  StreamingKernelAloneActivatesProduction → ⊥
streamingArchitectureAloneCannotReplaceParity ()

------------------------------------------------------------------------
-- Post-certification destination.
--
-- Once parity and production activation are supplied, the next architecture
-- target is streaming/delta hierarchy: do ordinary semantic work while parser
-- events arrive, transport only outward deltas, and rebenchmark the complete
-- system afterwards.  The kernel type is parameterised here rather than tied
-- to a particular parser implementation so spaCy is one concrete producer of
-- ParserEvent values, not the semantic authority itself.
------------------------------------------------------------------------

record PostCertificationStreamingTarget
    (Observation ParserEvent Authority SemanticDelta Frontier : Set) : Set₁ where
  constructor postCertificationStreamingTarget
  field
    certifiedDirect : Activation.CertifiedDirectActivation Observation
    kernel : Streaming.StreamingKernel ParserEvent Authority SemanticDelta Frontier

    -- The production physical constitution remains part of the certified
    -- activation while streaming changes scheduling, not semantic meaning.
    productionPhysical : Direct.DirectDeltaPhysicalConstitution
    samePhysicalConstitution :
      productionPhysical ≡ Activation.physical certifiedDirect

open PostCertificationStreamingTarget public

------------------------------------------------------------------------
-- Invalid roadmap inversion.
------------------------------------------------------------------------

data OptimizeColdPublicationForeverBeforeDeltaArchitecture : Set where

coldMicroOptimizationIsNotSemanticPrerequisite :
  OptimizeColdPublicationForeverBeforeDeltaArchitecture → ⊥
coldMicroOptimizationIsNotSemanticPrerequisite ()
