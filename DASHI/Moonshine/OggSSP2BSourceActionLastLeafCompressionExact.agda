module DASHI.Moonshine.OggSSP2BSourceActionLastLeafCompressionExact where

------------------------------------------------------------------------
-- SOURCE-ACTION LAST-LEAF COMPRESSION FOR THE 2B NORM WELD
--
-- ATTRIBUTION / OWNERSHIP
--
-- External source facts:
--   * Scott Carnahan, "A Self-Dual Integral Form of the Moonshine Module",
--     SIGMA 15 (2019), 030: a self-dual integral Moonshine form with Monster
--     symmetry.  Hence every subgroup of the Monster, in particular the
--     centralizer of a selected 2B involution, acts on the integral weight-two
--     carrier by restriction.
--   * ATLAS / CTblLib: the 2B-centralizer / Co1 local structure and the concrete
--     modular block labels used by the executed decomposition screens.
--   * Standard modular block theory (Linckelmann / Schneider): central block
--     idempotents act functorially on every module and module homomorphisms
--     preserve block summands.
--
-- DASHI contribution:
--   * the source-native C2 Tate cokernel and common/residual rank squeeze;
--   * the executed Co1 Sym2(24) / Frobenius-socle runtime receipts;
--   * Lean compilers showing equivariant residual range + rank 24 + unique
--     Frobenius socle forces literal range equality and therefore
--       Tate cokernel ~= wedge2(24).
--
-- CONSEQUENCE
-- The residual block projector is not a separate scientific discovery gate.
-- Once the externally sourced centralizer action is represented as a formal
-- module action on the source-native norm carrier, the existing compiler stack
-- derives invariance, Frobenius-range equality and the exterior-square cokernel.
--
-- IMPORTANT FIREWALL
-- This file does NOT claim that the Carnahan carrier/action has already been
-- instantiated as an Agda/Lean module object.  The literal Tate/exterior weld
-- remains unpaid until that formal same-object action object exists.
------------------------------------------------------------------------

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

canonicalSourceActionLastLeafCompressionStatus :
  SourceActionLastLeafCompressionStatus
canonicalSourceActionLastLeafCompressionStatus =
  source-action-last-leaf-compression-status
    true true true true true false
    false false
    0 1
    "Instantiate the externally sourced C_M(2B)/Co1 action on the formal source-native mod-2 norm carrier. The direct invariant-range compiler then uses the already-paid rank-24 and Frobenius-socle receipts to force the residual image to the Frobenius 24 and the Tate cokernel to wedge2(24)/duad276. No additional block-projector discovery is required."

externalMonsterActionSourcedUpstream :
  Action.restrictedLocalActionExistsMathematically
    Action.canonicalIntegralMoonshineLocalActionSource
  ≡ true
externalMonsterActionSourcedUpstream =
  Action.externalRestrictedLocalActionIsSourced

blockProjectorExistenceSourcedUpstream :
  Block.ModularBlockIdempotentSourceStatus.centralPrimitiveIdempotentsSourced
    Block.canonicalModularBlockIdempotentSourceStatus
  ≡ true
blockProjectorExistenceSourcedUpstream = refl

noScientificRepresentationDiscoveryLeafRemains :
  SourceActionLastLeafCompressionStatus.remainingScientificRepresentationDiscoveryLeaves
    canonicalSourceActionLastLeafCompressionStatus
  ≡ 0
noScientificRepresentationDiscoveryLeafRemains = refl

oneFormalCarrierInstantiationLeafRemains :
  SourceActionLastLeafCompressionStatus.remainingFormalCarrierInstantiationLeaves
    canonicalSourceActionLastLeafCompressionStatus
  ≡ 1
oneFormalCarrierInstantiationLeafRemains = refl

formalCentralizerActionObjectStillOpen :
  SourceActionLastLeafCompressionStatus.formalSourceNativeCentralizerActionObjectInRepo
    canonicalSourceActionLastLeafCompressionStatus
  ≡ false
formalCentralizerActionObjectStillOpen = refl

literalTateExteriorSquareWeldStillOpen :
  SourceActionLastLeafCompressionStatus.literalTateExteriorSquareWeldPaid
    canonicalSourceActionLastLeafCompressionStatus
  ≡ false
literalTateExteriorSquareWeldStillOpen = refl

-- Compatibility cross-check: the older frontier counted one same-object leaf.
-- The new statement refines its meaning: that leaf is a formal action-object
-- instantiation, not an unresolved representation-discovery theorem.
olderLastLeafCountWasOne :
  Last.NormWeldLastLeafStatus.remainingSameObjectLeafCount
    Last.canonicalNormWeldLastLeafStatus
  ≡ 1
olderLastLeafCountWasOne = Last.remainingSameObjectLeafCountIsOne
