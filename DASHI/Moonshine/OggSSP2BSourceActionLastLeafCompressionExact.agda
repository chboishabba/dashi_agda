module DASHI.Moonshine.OggSSP2BSourceActionLastLeafCompressionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSP2BIntegralMoonshineLocalActionSourceExact as Action
import DASHI.Moonshine.OggSSP2BModularBlockIdempotentSourceExact as Block
import DASHI.Moonshine.OggSSP2BNormWeldLastLeafExact as Last

record SourceActionLastLeafCompressionStatus : Set where
  constructor source-action-last-leaf-compression-status
  field
    carnahanMonsterStableIntegralActionSourced : Bool
    twoBCentralizerActionExistsByRestriction : Bool
    modularBlockProjectorExistenceSourced : Bool
    residualBlockLabelRuntimePaid : Bool
    directInvariantRangeCompilerImplementedInLean : Bool
    blockProjectorIsIndependentScientificLeaf : Bool
    formalSourceNativeCentralizerActionObjectInRepo : Bool
    literalTateExteriorSquareWeldPaid : Bool
    remainingScientificRepresentationDiscoveryLeaves : Nat
    remainingFormalCarrierInstantiationLeaves : Nat
    nextResidual : String

canonicalSourceActionLastLeafCompressionStatus : SourceActionLastLeafCompressionStatus
canonicalSourceActionLastLeafCompressionStatus =
  source-action-last-leaf-compression-status
    true true true true true false false false 0 1
    "Historical pre-equivariance frontier: instantiate the sourced centralizer action on the formal norm carrier. Newer compilers automatically descend that action to the Tate quotient and derive the terminal outer conjugation equation from weld equivariance."

externalMonsterActionSourcedUpstream :
  Action.restrictedLocalActionExistsMathematically Action.canonicalIntegralMoonshineLocalActionSource ≡ true
externalMonsterActionSourcedUpstream = Action.externalRestrictedLocalActionIsSourced

blockProjectorExistenceSourcedUpstream :
  Block.ModularBlockIdempotentSourceStatus.centralPrimitiveIdempotentsSourced
    Block.canonicalModularBlockIdempotentSourceStatus ≡ true
blockProjectorExistenceSourcedUpstream = refl

noScientificRepresentationDiscoveryLeafRemains :
  SourceActionLastLeafCompressionStatus.remainingScientificRepresentationDiscoveryLeaves
    canonicalSourceActionLastLeafCompressionStatus ≡ 0
noScientificRepresentationDiscoveryLeafRemains = refl

oneFormalCarrierInstantiationLeafRemains :
  SourceActionLastLeafCompressionStatus.remainingFormalCarrierInstantiationLeaves
    canonicalSourceActionLastLeafCompressionStatus ≡ 1
oneFormalCarrierInstantiationLeafRemains = refl

formalCentralizerActionObjectStillOpen :
  SourceActionLastLeafCompressionStatus.formalSourceNativeCentralizerActionObjectInRepo
    canonicalSourceActionLastLeafCompressionStatus ≡ false
formalCentralizerActionObjectStillOpen = refl

literalTateExteriorSquareWeldStillOpen :
  SourceActionLastLeafCompressionStatus.literalTateExteriorSquareWeldPaid
    canonicalSourceActionLastLeafCompressionStatus ≡ false
literalTateExteriorSquareWeldStillOpen = refl

olderLastLeafCountWasOne :
  Last.NormWeldLastLeafStatus.remainingSameObjectLeafCount Last.canonicalNormWeldLastLeafStatus ≡ 1
olderLastLeafCountWasOne = Last.remainingSameObjectLeafCountIsOne
