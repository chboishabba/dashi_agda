module DASHI.Codec.TriadicExplodedTransformBridge where

-- Codec-facing bridge for the application-independent exploded-transform tower.
-- This module intentionally reuses, rather than duplicates, the existing
-- SSP tree-action and W9 MDL termination seams.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; _⊔_; lsuc)

import DASHI.Geometry.TriadicExplodedTransformTower as Tower
import DASHI.Geometry.SSP369TreeAutomorphism as Tree
import DASHI.Physics.Closure.W9MDLTerminationSeamRoute as W9

------------------------------------------------------------------------
-- Exact support/sign factorisation of one balanced trit.

data Support : Set where
  inactive active : Support

data Sign : Set where
  negative positive : Sign

data FoldedTrit : Set where
  atZero : FoldedTrit
  onSupport : Sign → FoldedTrit

foldTrit : Tower.Trit → FoldedTrit
foldTrit Tower.neg = onSupport negative
foldTrit Tower.zeroT = atZero
foldTrit Tower.pos = onSupport positive

unfoldTrit : FoldedTrit → Tower.Trit
unfoldTrit atZero = Tower.zeroT
unfoldTrit (onSupport negative) = Tower.neg
unfoldTrit (onSupport positive) = Tower.pos

fold-unfold : (x : FoldedTrit) → foldTrit (unfoldTrit x) ≡ x
fold-unfold atZero = refl
fold-unfold (onSupport negative) = refl
fold-unfold (onSupport positive) = refl

unfold-fold : (t : Tower.Trit) → unfoldTrit (foldTrit t) ≡ t
unfold-fold Tower.neg = refl
unfold-fold Tower.zeroT = refl
unfold-fold Tower.pos = refl

------------------------------------------------------------------------
-- Causal chart contract.  The concrete sampler, lag carrier, and residual
-- algebra are supplied by applications; the structural requirement is that
-- chart choice is history-indexed and its geometry is an exploded transform.

record CausalChart
  {ℓH ℓG : Level}
  (History : Set ℓH)
  (Geometry : Set ℓG) : Set (ℓH ⊔ ℓG) where
  field
    treeDepth : History → Nat
    referenceLag : History → Nat
    transform : History → Tower.ExplodedTransform Geometry
    sideCost : History → Nat

------------------------------------------------------------------------
-- Existing-repo reference surface.

record ExistingFormalismReferences : Set where
  field
    treeActionReference : String
    mdlReference : String
    scopeBoundary : List String

canonicalExistingFormalismReferences : ExistingFormalismReferences
canonicalExistingFormalismReferences =
  record
    { treeActionReference =
        "DASHI.Geometry.SSP369TreeAutomorphism: prefix/depth-preserving finite tree actions"
    ; mdlReference =
        "DASHI.Physics.Closure.W9MDLTerminationSeamRoute: accepted non-pressure MDL Lyapunov seam"
    ; scopeBoundary =
        "Exploded-transform involution equivariance is proved constructively"
        ∷ "Partition recognisability and analytic universality require receipts"
        ∷ "No AV1 comparison, continuum-warp theorem, or physical promotion is asserted"
        ∷ []
    }

-- Import-level witnesses ensure these bridge references remain tied to the
-- live theorem spine rather than becoming documentation-only names.

w9Witness : W9.MDLTerminationSeamWitness
w9Witness = W9.canonicalMDLTerminationSeamWitness

treePrefixWitness = Tree.actionCommutesWithPrefix
