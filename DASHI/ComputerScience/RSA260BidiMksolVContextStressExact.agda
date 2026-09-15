module DASHI.ComputerScience.RSA260BidiMksolVContextStressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.RSA260BidiMksolActionKernelQuotientExact as Quotient

------------------------------------------------------------------------
-- MULTI-V STRESS OF THE CONTEXT-INDEXED ACTION KERNEL
--
-- The fixed-context action quotient exposed a 64-bit hidden coefficient space
-- for the ordinary degree-17 synthetic identity context.  That compression is
-- only useful if the same directions remain invisible across the context family
-- demanded by the downstream consumer.
--
-- Runtime stress stacks the linear maps for independent synthetic V blocks:
--
--   one V context: rank 1024 / 1088 -> 64-bit kernel;
--   two V contexts: rank 1088 / 1088 -> zero intersection kernel.
--
-- Thus the one-context quotient is not stable under this two-context expansion.
-- This is not a theorem that every pair of V contexts identifies every generator,
-- and it is not exact CADO mksol semantics.  It demonstrates the generic rule:
-- consumer-relative compression must be tested against the declared consumer
-- FAMILY, not just one query instance.
------------------------------------------------------------------------

quotientBoundary : Quotient.MksolActionKernelQuotientBoundary
quotientBoundary = Quotient.canonicalMksolActionKernelQuotientBoundary

record MksolVContextStressRuntimeReceipt : Set where
  constructor mksol-v-context-stress-runtime-receipt
  field
    runtimeHarness : String
    outputPath : String
    outputSHA256 : String
    degree : Nat
    coefficientDomainBits : Nat
    oneContextActionRankBits : Nat
    oneContextKernelBits : Nat
    twoContextActionFamilyRankBits : Nat
    twoContextIntersectionKernelBits : Nat
    firstContextSynthetic : Bool
    secondContextSynthetic : Bool
    samePreparedOperatorUsed : Bool
    exactCADOMksolContextFamily : Bool
    productionRSA260CarrierUsed : Bool
    exactLocalRuntimeExecuted : Bool
open MksolVContextStressRuntimeReceipt public

currentMksolVContextStressRuntimeReceipt : MksolVContextStressRuntimeReceipt
currentMksolVContextStressRuntimeReceipt =
  mksol-v-context-stress-runtime-receipt
    "/mnt/data/rsa260_bidi_raw_rank_crossvalidate.py plus stacked V-context rank probe"
    "/mnt/data/rsa260_bidi_mksol_V_context_stress.json"
    "11dc5183f9c197b47ec58fdc684dbd0dcf35c8eab60c4589ae063b38beaf6538"
    17
    1088
    1024
    64
    1088
    0
    true true true
    false false true

record MksolVContextStressBoundary : Set where
  constructor mksol-v-context-stress-boundary
  field
    fixedContextKernelInherited : Bool
    oneContextHasNontrivialKernel : Bool
    secondSyntheticVReopensHiddenDirections : Bool
    twoContextIntersectionKernelZeroInProbe : Bool
    oneContextCompressionStableUnderCheckedTwoContextFamily : Bool
    consumerFamilyMustPrecedeCompressionRanking : Bool
    twoContextInjectivityIsUniversalTheorem : Bool
    exactCADOMksolContextFamilyPaid : Bool
    productionRSA260Claimed : Bool
open MksolVContextStressBoundary public

canonicalMksolVContextStressBoundary : MksolVContextStressBoundary
canonicalMksolVContextStressBoundary =
  mksol-v-context-stress-boundary
    true true true true
    false true false false false

data MksolVContextStressResidual : Set where
  defineSourceNativeCADOMksolContextFamily : MksolVContextStressResidual
  determineActualVBlockFamilyAndSolutionRanges : MksolVContextStressResidual
  testIntersectionKernelAcrossDeclaredContextFamily : MksolVContextStressResidual
  searchCompressionOnlyInsidePersistentIntersectionKernel : MksolVContextStressResidual
  bindSameObjectProductionContexts : MksolVContextStressResidual

firstMksolVContextStressResidual : MksolVContextStressResidual
firstMksolVContextStressResidual = defineSourceNativeCADOMksolContextFamily
