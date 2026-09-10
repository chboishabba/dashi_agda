{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLangevinPhysicalHessianSourceRecutRound263Exact where

------------------------------------------------------------------------
-- ROUND263/R269 / C4b SOURCE RECUT AFTER TYPED/ANCHORED INTROSPECTION
--
-- The open C4b claim has now been split at the correct trust boundaries:
--
--   CMP109 effective potential
--     = CMP116 physical marked Hessian                 [already compiler-owned]
--     = typed Langevin symmetric nonlocal entry       [R267 source seam]
--     <= R260 comparison + SAME-carrier reference     [R268 source seam]
--     -> rational influence entry                     [compiler-owned]
--     -> weighted row / every Dyson power             [compiler-owned]
--
-- This file is a status/frontier adapter only; it does not promote conditional
-- source realizations to machineChecked.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact as Langevin
import DASHI.Physics.YangMills.BalabanLangevinHessianBidirectionalWeldRound262Exact as Bidi
import DASHI.Physics.YangMills.BalabanCMP109LangevinTypedSecondVariationRound267Exact as CMP
import DASHI.Physics.YangMills.BalabanLangevinAnchoredInfluenceRound268Exact as Anchor

-- Already paid: literal CMP109 E^(2)/Pi = CMP116 physical Hessian.
cmp109CMP116SamePhysicalSecondVariationLevel : ProofLevel
cmp109CMP116SamePhysicalSecondVariationLevel =
  Carrier.cmp109CMP116PhysicalHessianIdentityLevel

-- Already paid once a typed commutator is inhabited: its symmetric entry is the
-- exact action-Hessian entry by a proof-relevant equality, not an opaque Set.
typedCommutatorDecompositionCompilerLevel : ProofLevel
typedCommutatorDecompositionCompilerLevel =
  Langevin.typedLangevinCommutatorCompilerLevel

-- R267 compiles the typed action Hessian onto the literal CMP109/CMP116 carrier.
typedCMP109LangevinCompilerLevel : ProofLevel
typedCMP109LangevinCompilerLevel = CMP.round267TypedCMP109LangevinCompilerLevel

-- R268 compiles a same-object R260 anchored entry into the rational influence
-- majorant required by R266.
anchoredEntryToInfluenceCompilerLevel : ProofLevel
anchoredEntryToInfluenceCompilerLevel =
  Anchor.round268AnchoredEntryToInfluenceCompilerLevel

bidirectionalConsumerCompilerLevel : ProofLevel
bidirectionalConsumerCompilerLevel = Bidi.round262BidiCompilerLevel

------------------------------------------------------------------------
-- CURRENT LIVE PHYSICAL SOURCE CUT
------------------------------------------------------------------------

-- C4a/C4b source geometry: instantiate the actual differentiated compact-group
-- Langevin coefficients on the literal CMP109 effective density and its
-- site-indexed physical tangent directions.
literalCMP109LangevinDifferentiationLevel : ProofLevel
literalCMP109LangevinDifferentiationLevel =
  CMP.round267LiteralLangevinDifferentiationInstantiationLevel

-- R260 trust boundary: realize the published marked comparison AND a reference
-- Hessian anchor on that exact same typed CMP109 action-Hessian entry.
literalSameObjectMarkedComparisonAndReferenceAnchorLevel : ProofLevel
literalSameObjectMarkedComparisonAndReferenceAnchorLevel =
  Anchor.round268SameObjectAnchoredSourceLevel

-- Least-privilege aggregate spatial theorem after anchoring: the weighted row
-- of the generated rational absolute debts is uniformly below the shared
-- marked Hessian constant.  No exact shell-partial equality is requested.
literalWeightedAnchoredDebtRowLevel : ProofLevel
literalWeightedAnchoredDebtRowLevel =
  Anchor.round268WeightedAnchoredDebtRowLevel

-- These are now the three spatial source payments; everything between/after
-- them in this C4 subchain is compiler-owned.
round269LiteralSpatialSourceClosureLevel : ProofLevel
round269LiteralSpatialSourceClosureLevel = conditional

round269ClayClosureLevel : ProofLevel
round269ClayClosureLevel = conditional
