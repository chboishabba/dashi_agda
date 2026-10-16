module DASHI.Moonshine.OggSSP2BOuterActionLastEquationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSP2BSourceActionLastLeafCompressionExact as Source
import DASHI.Moonshine.OggSSP2BM22d2Completion10RuntimeReceiptExact as M22d2

record OuterActionLastEquationStatus : Set where
  constructor outer-action-last-equation-status
  field
    externalActualTateActionSourcedMathematically : Bool
    finiteM22d2OuterJ2x5OperatorPaid : Bool
    exteriorActionTransportIsCompilerConsequence : Bool
    coordinateChoiceIsCompilerConsequence : Bool
    stableQ10TransportIsCompilerConsequence : Bool
    formalSourceActionObjectInstantiated : Bool
    actualCokernelOuterEqualsTransportedModelOuterPaid : Bool
    actualStableQ10AndCompletionPaid : Bool
    remainingOuterActionSameObjectEquations : Nat
    remainingDefectSourceBits : Nat
    nextResidual : String

canonicalOuterActionLastEquationStatus : OuterActionLastEquationStatus
canonicalOuterActionLastEquationStatus =
  outer-action-last-equation-status
    true true true true true false false false 1 2
    "Historical frontier only: the newer equivariant-weld compiler shows this operator equality is generated automatically from weld equivariance."

finiteOuterJ2x5PaidUpstream : M22d2.outerJ2x5MatchCount ≡ 2
finiteOuterJ2x5PaidUpstream = M22d2.outerJ2x5MatchCountIsTwo

sourceActionScientificDiscoveryClosedUpstream :
  Source.SourceActionLastLeafCompressionStatus.remainingScientificRepresentationDiscoveryLeaves
    Source.canonicalSourceActionLastLeafCompressionStatus ≡ 0
sourceActionScientificDiscoveryClosedUpstream = Source.noScientificRepresentationDiscoveryLeafRemains

oneOuterSameObjectEquationRemains :
  OuterActionLastEquationStatus.remainingOuterActionSameObjectEquations
    canonicalOuterActionLastEquationStatus ≡ 1
oneOuterSameObjectEquationRemains = refl

formalSourceActionStillOpen :
  OuterActionLastEquationStatus.formalSourceActionObjectInstantiated
    canonicalOuterActionLastEquationStatus ≡ false
formalSourceActionStillOpen = refl

outerActionEquationStillOpen :
  OuterActionLastEquationStatus.actualCokernelOuterEqualsTransportedModelOuterPaid
    canonicalOuterActionLastEquationStatus ≡ false
outerActionEquationStillOpen = refl
