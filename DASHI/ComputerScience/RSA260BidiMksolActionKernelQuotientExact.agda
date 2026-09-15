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
-- This owner packages that quotient generically and binds a finite runtime probe
-- on the existing synthetic BWC harness.  The runtime probe studies the linear
-- map
--
--   (F_0,...,F_{d-1}) |-> XOR_l M^l V F_l.
--
-- It finds a nontrivial kernel on the degree-17 synthetic contexts but an
-- injective map on the checked degree-16 contexts.  This is positive evidence
-- for consumer-relative quotienting, not a universal compression theorem:
-- changing V, the prepared operator, or the requested solution context can
-- reopen directions hidden by one fixed action map.
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
-- Runtime rank probe.
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
    degree16ActionMapRankBits : Nat
    allCheckedDegree16MapsInjective : Bool
    degree17CoefficientDomainBits : Nat
    ordinaryDegree17ActionMapRankBits : Nat
    ordinaryDegree17KernelBits : Nat
    rotate1ActionMapRankBits : Nat
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
    "/mnt/data/rsa260_bidi_raw_rank_crossvalidate.py plus action-map rank probe"
    "/mnt/data/rsa260_bidi_mksol_action_kernel_quotient.json"
    "4f70d638ea963182df530f30464060035a6a9f036622c0a0cdd1e36f480a143f"
    12
    5
    7
    1024
    1024
    true
    1088
    1024
    64
    1016
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
    checkedDegree16FixedContextActionInjective : Bool
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
    true true true true
    false false false false false true

data MksolActionKernelResidual : Set where
  buildConcreteQuotientCoordinatesForFixedSyntheticContext : MksolActionKernelResidual
  stressQuotientAcrossMultipleVContexts : MksolActionKernelResidual
  stressQuotientAcrossPreparedOperatorContexts : MksolActionKernelResidual
  identifyIntersectionKernelAcrossDeclaredMksolContextFamily : MksolActionKernelResidual
  alignContextFamilyWithSourceNativeCADOMksol : MksolActionKernelResidual
  bindSameObjectProductionVAndPreparedOperator : MksolActionKernelResidual

firstMksolActionKernelResidual : MksolActionKernelResidual
firstMksolActionKernelResidual = buildConcreteQuotientCoordinatesForFixedSyntheticContext
