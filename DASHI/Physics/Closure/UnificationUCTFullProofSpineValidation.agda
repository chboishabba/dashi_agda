{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.UnificationUCTFullProofSpineValidation where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.UnificationUCTFullProofSpineExact as Spine

uctSpineCompilerIsMachineChecked : ProofLevel
uctSpineCompilerIsMachineChecked = Spine.uctAnalyticSpineCompilerLevel

uct1RemainsConditional : ProofLevel
uct1RemainsConditional = Spine.uct1ResidualPDEPhysicalLevel

uct2RemainsConditional : ProofLevel
uct2RemainsConditional = Spine.uct2OperatorClassPhysicalLevel

uct3RemainsConditional : ProofLevel
uct3RemainsConditional = Spine.uct3UniqueContinuationPhysicalLevel

uct4RemainsConditional : ProofLevel
uct4RemainsConditional = Spine.uct4CrossTermNullityPhysicalLevel
