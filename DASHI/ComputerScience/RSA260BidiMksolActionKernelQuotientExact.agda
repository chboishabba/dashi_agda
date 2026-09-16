module DASHI.ComputerScience.RSA260BidiMksolActionKernelQuotientExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.RSA260BidiMksolConsumerProjectionExact as Mksol
import DASHI.ComputerScience.RSA260BidiHybridReplayMksolAdequacyExact as Replay

------------------------------------------------------------------------
-- CONTEXT-INDEXED MKSOL ACTION-KERNEL QUOTIENT
--
-- Once the active consumer is generator evaluation rather than receipt identity,
-- the natural equivalence is not byte/SHA equality.  For a fixed mksol context,
-- two generator states are consumer-equivalent exactly when they induce the same
-- action output.
--
-- The finite runtime probe studies the linear map
--
--   (F_0,...,F_{d-1}) |-> XOR_l M^l V F_l.
--
-- IMPORTANT AUDIT CORRECTION:
-- The first draft of this receipt accidentally ranked the helper's extra K_d
-- block although the action uses only K_0..K_{d-1}.  The corrected probe below
-- slices exactly d Krylov blocks.  With that correction most checked degree-16
-- contexts are injective, but seed4 has a 16-bit kernel and bitrev9 an 8-bit
-- kernel.  Ordinary checked degree-17 contexts have a 64-bit kernel; rotate1
-- has 72 bits.  This preserves the qualitative conclusion (consumer-relative
-- hidden directions exist) while removing the false claim that every checked
-- degree-16 context was injective.
--
-- Any such kernel remains context-indexed: changing V, the prepared operator,
-- or the requested solution context can reopen hidden directions.
------------------------------------------------------------------------

mksolBoundary : Mksol.MksolConsumerProjectionBoundary
mksolBoundary = Mksol.canonicalMksolConsumerProjectionBoundary

replayBoundary : Replay.HybridReplayMksolAdequacyBoundary
replayBoundary = Replay.canonicalHybridReplayMksolAdequacyBoundary

record GeneratorActionContext : Set₁ where
  constructor generator-action-context
  field
    GeneratorState : Set
    ActionOutput : Set
    action : GeneratorState -> ActionOutput
open GeneratorActionContext public

ActionKernelEquivalent : (context : GeneratorActionContext) ->
  GeneratorState context -> GeneratorState context -> Set
ActionKernelEquivalent context left right =
  action context left ≡ action context right

record ActionQuotientRepresentation (context : GeneratorActionContext) : Set₁ where
  constructor action-quotient-representation
  field
    Code : Set
    encode : GeneratorState context -> Code
    evaluateCode : Code -> ActionOutput context
    actionFactorsThroughCode :
      (generator : GeneratorState context) ->
      action context generator ≡ evaluateCode (encode generator)
open ActionQuotientRepresentation public

equalCodeImpliesEqualAction :
  {context : GeneratorActionContext} ->
  (representation : ActionQuotientRepresentation context) ->
  {left right : GeneratorState context} ->
  encode representation left ≡ encode representation right ->
  ActionKernelEquivalent context left right
equalCodeImpliesEqualAction {context} representation encodedEq =
  trans
    (actionFactorsThroughCode representation _)
    (trans
      (cong (evaluateCode representation) encodedEq)
      (sym (actionFactorsThroughCode representation _)))

------------------------------------------------------------------------
-- Corrected runtime rank probe.
------------------------------------------------------------------------

record MksolActionKernelRuntimeReceipt : Set where
  constructor mksol-action-kernel-runtime-receipt
  field
    runtimeHarness : String
    outputPath : String
    outputSHA256 : String
    checkedWorlds : Nat
    degree16Worlds : Nat
    degree17Worlds : Nat
    degree16CoefficientDomainBits : Nat
    seed0KernelBits : Nat
    seed3KernelBits : Nat
    seed4KernelBits : Nat
    seed7KernelBits : Nat
    bitrev9KernelBits : Nat
    degree17CoefficientDomainBits : Nat
    ordinaryDegree17KernelBits : Nat
    rotate1KernelBits : Nat
    fixedSyntheticContextOnly : Bool
    exactCADOMksolSemantics : Bool
    productionRSA260CarrierUsed : Bool
    exactLocalRuntimeExecuted : Bool
    runtimeSourceCommitted : Bool
open MksolActionKernelRuntimeReceipt public

currentMksolActionKernelRuntimeReceipt : MksolActionKernelRuntimeReceipt
currentMksolActionKernelRuntimeReceipt =
  mksol-action-kernel-runtime-receipt
    "/mnt/data/rsa260_bidi_raw_rank_crossvalidate.py plus corrected action-map rank probe"
    "/mnt/data/rsa260_bidi_mksol_action_kernel_quotient_corrected.json"
    "517f456a44265044e659b11f74d163bc7c8b97d473e003fa874e2150a75d94a6"
    12
    5
    7
    1024
    0 0 16 0 8
    1088
    64
    72
    true
    false
    false
    true
    false

------------------------------------------------------------------------
-- Interpretation.
------------------------------------------------------------------------

record MksolActionKernelQuotientBoundary : Set where
  constructor mksol-action-kernel-quotient-boundary
  field
    mksolEvaluationIsConsumerRelative : Bool
    actionKernelEquivalenceDefined : Bool
    genericActionFactoringRepresentationDefined : Bool
    exactReplayRemainsSufficientUpperEndpoint : Bool
    someCheckedDegree16FixedContextActionsInjective : Bool
    allCheckedDegree16FixedContextActionsInjective : Bool
    seed4Degree16Has16HiddenBits : Bool
    bitrev9Degree16Has8HiddenBits : Bool
    checkedDegree17FixedContextHasUnobservedDirections : Bool
    ordinaryDegree17KernelHas64BitsInRuntimeProbe : Bool
    rotate1KernelHas72BitsInRuntimeProbe : Bool
    fixedContextKernelIsUniversalGeneratorKernel : Bool
    hiddenDirectionsGuaranteedHiddenForDifferentV : Bool
    hiddenDirectionsGuaranteedHiddenForDifferentOperator : Bool
    runtimeProbeIsExactCADOMksol : Bool
    runtimeProbeUsesProductionRSA260 : Bool
    consumerRelativeCompressionOpportunityObserved : Bool
open MksolActionKernelQuotientBoundary public

canonicalMksolActionKernelQuotientBoundary : MksolActionKernelQuotientBoundary
canonicalMksolActionKernelQuotientBoundary =
  mksol-action-kernel-quotient-boundary
    true true true true
    true false true true
    true true true
    false false false false false true

data MksolActionKernelResidual : Set where
  stressQuotientAcrossMultipleVContexts : MksolActionKernelResidual
  stressQuotientAcrossPreparedOperatorContexts : MksolActionKernelResidual
  identifyIntersectionKernelAcrossDeclaredMksolContextFamily : MksolActionKernelResidual
  buildConcreteCoordinatesOnlyIfIntersectionKernelPersists : MksolActionKernelResidual
  alignContextFamilyWithSourceNativeCADOMksol : MksolActionKernelResidual
  bindSameObjectProductionVAndPreparedOperator : MksolActionKernelResidual

firstMksolActionKernelResidual : MksolActionKernelResidual
firstMksolActionKernelResidual = stressQuotientAcrossMultipleVContexts
