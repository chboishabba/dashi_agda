module DASHI.Biology.JCoarseFineDepthDecompositionBridgeExact where

------------------------------------------------------------------------
-- J / DECIMAL / STAGE COARSE-FINE DECOMPOSITION BRIDGE
--
-- PRIMARY BACKGROUND SOURCES
--
-- Ingrid Daubechies,
-- "Ten Lectures on Wavelets", SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Donald E. Knuth,
-- "The Art of Computer Programming, Volume 2: Seminumerical Algorithms",
-- 3rd ed., Addison-Wesley, 1997. ISBN 9780201896848.
--
-- DASHI PROVENANCE / REUSE
--
-- Older supplied coarse/fine notes used the retained decimal relation 1+10=11.
-- The merged StageValuationBundleAtlas independently has Stage 11 as a carried
-- ten-unit bundle plus one fresh local unit.  JFineCoarseRelativeScaleExact has
-- the distinct triadic depth reconstruction 2+9=11 and frequency factorisation
-- 3^2 * 3^9 = 3^11.
--
-- This file proves that all three instantiate the same generic additive
-- decomposition *shape*.  It explicitly does not identify their semantic or
-- mathematical roles.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CoarseFineDepthDecompositionExact as Core
import DASHI.Biology.JFineCoarseRelativeScaleExact as J
import DASHI.Foundations.StageValuationBundleAtlas as Stage

------------------------------------------------------------------------
-- Three distinct 11-valued decompositions.
------------------------------------------------------------------------

decimalRetainedResolutionEleven : Core.CoarseFineDecomposition
decimalRetainedResolutionEleven =
  Core.coarse-fine-decomposition 1 10 11 refl

triadicJDepthEleven : Core.CoarseFineDecomposition
triadicJDepthEleven =
  Core.coarse-fine-decomposition 2 9 11 refl

stage11BundlePlusFreshUnit : Core.CoarseFineDecomposition
stage11BundlePlusFreshUnit =
  Core.coarse-fine-decomposition 10 1 11 refl

------------------------------------------------------------------------
-- Exact agreement with existing authoritative owners.
------------------------------------------------------------------------

triadicJCoarseDepthMatchesExistingOwner :
  Core.coarseComponent triadicJDepthEleven
  ≡ J.coarseDepth J.canonicalTwoToElevenFibre
triadicJCoarseDepthMatchesExistingOwner = refl

triadicJRelativeDepthMatchesExistingOwner :
  Core.relativeFineComponent triadicJDepthEleven
  ≡ J.jFineDepth J.canonicalTwoToElevenFibre
triadicJRelativeDepthMatchesExistingOwner = refl

triadicJAbsoluteDepthMatchesExistingOwner :
  Core.absoluteComponent triadicJDepthEleven
  ≡ J.absoluteFineDepth J.canonicalTwoToElevenFibre
triadicJAbsoluteDepthMatchesExistingOwner = refl

stage11CarriedBundleMatchesExistingOwner :
  Core.coarseComponent stage11BundlePlusFreshUnit
  ≡ Stage.Stage11CrossScaleJoin.carriedBundleValue
      Stage.canonicalStage11CrossScaleJoin
stage11CarriedBundleMatchesExistingOwner = refl

stage11FreshUnitMatchesExistingOwner :
  Core.relativeFineComponent stage11BundlePlusFreshUnit
  ≡ Stage.Stage11CrossScaleJoin.freshLocalValue
      Stage.canonicalStage11CrossScaleJoin
stage11FreshUnitMatchesExistingOwner = refl

stage11AbsoluteMatchesExistingOwner :
  Core.absoluteComponent stage11BundlePlusFreshUnit
  ≡ Stage.Stage11CrossScaleJoin.joinedValue
      Stage.canonicalStage11CrossScaleJoin
stage11AbsoluteMatchesExistingOwner = refl

------------------------------------------------------------------------
-- Typed role separation: same printed 11, different decomposition semantics.
------------------------------------------------------------------------

data ElevenRole : Set where
  decimalRetentionRole triadicJDepthRole stageCrossScaleJoinRole : ElevenRole

record JCoarseFineDepthBridgeBoundary : Set where
  constructor j-coarse-fine-depth-bridge-boundary
  field
    decimalOnePlusTenIsTriadicTwoPlusNine : Bool
    decimalOnePlusTenIsTriadicTwoPlusNineIsFalse :
      decimalOnePlusTenIsTriadicTwoPlusNine ≡ false
    triadicDepthIsStageSemantics : Bool
    triadicDepthIsStageSemanticsIsFalse :
      triadicDepthIsStageSemantics ≡ false
    equalAbsoluteElevenImpliesEqualDecompositionRole : Bool
    equalAbsoluteElevenImpliesEqualDecompositionRoleIsFalse :
      equalAbsoluteElevenImpliesEqualDecompositionRole ≡ false

canonicalJCoarseFineDepthBridgeBoundary :
  JCoarseFineDepthBridgeBoundary
canonicalJCoarseFineDepthBridgeBoundary =
  j-coarse-fine-depth-bridge-boundary
    false refl
    false refl
    false refl
