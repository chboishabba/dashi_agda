{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLangevinPhysicalHessianSourceRecutRound263Exact where

------------------------------------------------------------------------
-- ROUND263 / C4b SOURCE RECUT
--
-- Current source machinery already proves on the literal differentiated
-- carrier that the CMP116 marked Hessian is the second variation of the SAME
-- CMP109 effective potential.  Therefore C4b must not charge that identity as
-- fresh physical analysis.
--
-- Remaining C4b physics is strictly:
--
--   (1) the symmetric nonlocal part of the literal differentiated Langevin
--       commutator is this existing physical second variation;
--   (2) its finite weighted influence row realizes the existing marked shell.
--
-- R262 then sends the same object bidirectionally to spatial Dyson propagation
-- and temporal Heat/Doob curvature debt.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanLangevinHessianBidirectionalWeldRound262Exact as Bidi

-- This is already a proved source/compiler theorem, not a new C4b leaf.
cmp109CMP116SamePhysicalSecondVariationLevel : ProofLevel
cmp109CMP116SamePhysicalSecondVariationLevel =
  Carrier.cmp109CMP116PhysicalHessianIdentityLevel

-- R262 already compiles a single source inhabitant into both downstream uses.
bidirectionalConsumerCompilerLevel : ProofLevel
bidirectionalConsumerCompilerLevel = Bidi.round262BidiCompilerLevel

-- Live physical seam 1: identify the symmetric nonlocal part of the ACTUAL
-- differentiated compact-group Langevin commutator with the existing literal
-- physical second variation owned by `Carrier`.
literalLangevinSymmetricPartIsExistingPhysicalSecondVariationLevel : ProofLevel
literalLangevinSymmetricPartIsExistingPhysicalSecondVariationLevel = conditional

-- Live physical seam 2: realize that same bilinear Hessian as the finite
-- nonnegative weighted influence row consumed by the shared marked-shell
-- compiler.  This is representation/localization, not a second Hessian theorem.
literalPhysicalSecondVariationToWeightedInfluenceRowLevel : ProofLevel
literalPhysicalSecondVariationToWeightedInfluenceRowLevel = conditional

-- The CMP109<->CMP116 identity itself is explicitly removed from the open cut.
round263CMPIdentityIsNotOpenPhysicsLevel : ProofLevel
round263CMPIdentityIsNotOpenPhysicsLevel = machineChecked

round263LiteralSourceClosureLevel : ProofLevel
round263LiteralSourceClosureLevel = conditional

round263ClayClosureLevel : ProofLevel
round263ClayClosureLevel = conditional
