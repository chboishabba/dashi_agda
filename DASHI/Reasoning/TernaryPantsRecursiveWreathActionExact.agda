module DASHI.Reasoning.TernaryPantsRecursiveWreathActionExact where

------------------------------------------------------------------------
-- FINITE-DEPTH RECURSIVE WREATH ACTION ON THE TERNARY PANTS TREE
--
-- Primary sources / context:
--   John D. Dixon and Brian Mortimer, "Permutation Groups",
--   Springer GTM 163 (1996), DOI 10.1007/978-1-4612-0731-3.
--   Volodymyr Nekrashevych, "Self-Similar Groups",
--   AMS Mathematical Surveys and Monographs 117 (2005),
--   DOI 10.1090/surv/117.
--
-- DASHI contribution:
--   upgrade the prior two-site finite wreath witness and the local ternary S3
--   pants action to the actual finite-depth recursive rooted-tree action.
--
-- At depth n+1 an automorphism consists of:
--   * one root S3 permutation; and
--   * one depth-n section for each of the three original child slots.
--
-- This is the standard recursive shape of the iterated permutational wreath
-- product.  We construct its action and explicit inverse on every finite pants
-- path.  No infinite inverse-limit/profinite completion is claimed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Foundations.TernaryEndomorphismConjugacyExact as S3
import DASHI.Reasoning.TernaryPantsSynthesisS3BridgeExact as Local
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

------------------------------------------------------------------------
-- Recursive automorphism carrier.
------------------------------------------------------------------------

data PantsTreeAut : Nat → Set where
  leafAut : PantsTreeAut 0
  nodeAut :
    ∀ {n : Nat} →
    S3.TriPermutation →
    (Pants.BranchSlot → PantsTreeAut n) →
    PantsTreeAut (suc n)

act :
  ∀ {n : Nat} →
  PantsTreeAut n →
  Frontier.PantsPath n →
  Frontier.PantsPath n
act leafAut vnil = vnil
act (nodeAut permutation sections) (slot vcons rest) =
  Local.permuteSlot permutation slot
  vcons act (sections slot) rest

------------------------------------------------------------------------
-- Identity automorphism at every depth.
------------------------------------------------------------------------

identityAut : (n : Nat) → PantsTreeAut n
identityAut 0 = leafAut
identityAut (suc n) =
  nodeAut S3.permIdentity (λ _ → identityAut n)

identityActsAt :
  ∀ {n : Nat} →
  (path : Frontier.PantsPath n) →
  act (identityAut n) path ≡ path
identityActsAt vnil = refl
identityActsAt (slot vcons rest)
  rewrite identityActsAt rest = refl

------------------------------------------------------------------------
-- Recursive inverse.
--
-- For an output branch y, the inverse section is the inverse of the original
-- section at p^{-1}(y).  This is the nontrivial wreath recursion; simply
-- inverting each section at the same output label would be wrong.
------------------------------------------------------------------------

inverseAut :
  ∀ {n : Nat} →
  PantsTreeAut n →
  PantsTreeAut n
inverseAut leafAut = leafAut
inverseAut (nodeAut permutation sections) =
  nodeAut
    (S3.inversePermutation permutation)
    (λ outputSlot →
      inverseAut
        (sections
          (Local.permuteSlot
            (S3.inversePermutation permutation)
            outputSlot)))

inverseActsLeft :
  ∀ {n : Nat}
  (automorphism : PantsTreeAut n)
  (path : Frontier.PantsPath n) →
  act (inverseAut automorphism) (act automorphism path) ≡ path
inverseActsLeft leafAut vnil = refl
inverseActsLeft
  (nodeAut permutation sections)
  (slot vcons rest)
  rewrite Local.permuteSlotInverseLeft permutation slot
        | inverseActsLeft (sections slot) rest = refl

------------------------------------------------------------------------
-- The forward action is injective because an explicit left inverse exists.
------------------------------------------------------------------------

actInjective :
  ∀ {n : Nat}
  (automorphism : PantsTreeAut n)
  (left right : Frontier.PantsPath n) →
  act automorphism left ≡ act automorphism right →
  left ≡ right
actInjective automorphism left right equality =
  trans
    (sym (inverseActsLeft automorphism left))
    (trans
      (cong (act (inverseAut automorphism)) equality)
      (inverseActsLeft automorphism right))

------------------------------------------------------------------------
-- A canonical nontrivial depth-two example: rotate at the root, then use a
-- slot-dependent transposition in the selected depth-one section.
------------------------------------------------------------------------

sectionSwap : Pants.BranchSlot → PantsTreeAut 1
sectionSwap Pants.slot3 =
  nodeAut S3.permSwapLowMid (λ _ → leafAut)
sectionSwap Pants.slot6 =
  nodeAut S3.permSwapLowHigh (λ _ → leafAut)
sectionSwap Pants.slot9 =
  nodeAut S3.permSwapMidHigh (λ _ → leafAut)

canonicalDepthTwoAut : PantsTreeAut 2
canonicalDepthTwoAut =
  nodeAut S3.permRotate sectionSwap

samplePath : Frontier.PantsPath 2
samplePath = Pants.slot3 vcons Pants.slot3 vcons vnil

sampleAction :
  act canonicalDepthTwoAut samplePath
  ≡ Pants.slot6 vcons Pants.slot6 vcons vnil
sampleAction = refl

sampleInverseRoundTrip :
  act (inverseAut canonicalDepthTwoAut)
    (act canonicalDepthTwoAut samplePath)
  ≡ samplePath
sampleInverseRoundTrip = inverseActsLeft canonicalDepthTwoAut samplePath

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record TernaryPantsRecursiveWreathBoundary : Set where
  constructor ternaryPantsRecursiveWreathBoundary
  field
    finiteDepthRecursiveActionConstructed : Bool
    independentSectionsPerChildConstructed : Bool
    explicitRecursiveInverseConstructed : Bool
    finiteDepthActionInjective : Bool
    infiniteProfiniteLimitConstructed : Bool
    smoothGeometricActionConstructed : Bool

canonicalTernaryPantsRecursiveWreathBoundary : TernaryPantsRecursiveWreathBoundary
canonicalTernaryPantsRecursiveWreathBoundary =
  ternaryPantsRecursiveWreathBoundary
    true true true true false false
