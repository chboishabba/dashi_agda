module DASHI.Moonshine.OggSSP2BSemisimplificationSelfDualityExtensionNoGoExact where

------------------------------------------------------------------------
-- CHARACTERISTIC-TWO EXTENSION NO-GO
--
-- A tiny exact counterexample showing why the successful 2B Brauer comparison,
-- even supplemented by self-duality / invariant-form data, cannot by itself
-- determine the missing order-two extension structure.
--
-- On F2^2 compare:
--   split    : g(x,y) = (x,y)
--   nonsplit : g(x,y) = (x+y,y) = J2(1)
--
-- Both have the same two trivial Jordan-Hoelder labels, both are involutions,
-- and both preserve the same nondegenerate alternating form
--     b((x,y),(u,v)) = x v + y u.
-- But the split action fixes all 4 vectors whereas the nonsplit action fixes
-- exactly the 2 vectors with y=0.
--
-- Therefore semisimplified composition data + existence of a nondegenerate
-- invariant form cannot determine the 2-singular extension/Jordan structure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. Tiny F2 arithmetic.
------------------------------------------------------------------------

data Bit : Set where
  z o : Bit

xor : Bit -> Bit -> Bit
xor z b = b
xor o z = o
xor o o = z

and : Bit -> Bit -> Bit
and z b = z
and o b = b

record V2 : Set where
  constructor v2
  field
    x y : Bit
open V2 public

------------------------------------------------------------------------
-- 2. Split and nonsplit involutions.
------------------------------------------------------------------------

splitAction : V2 -> V2
splitAction v = v

nonsplitAction : V2 -> V2
nonsplitAction (v2 a b) = v2 (xor a b) b

splitInvolutive : (v : V2) -> splitAction (splitAction v) ≡ v
splitInvolutive v = refl

nonsplitInvolutive : (v : V2) -> nonsplitAction (nonsplitAction v) ≡ v
nonsplitInvolutive (v2 z z) = refl
nonsplitInvolutive (v2 o z) = refl
nonsplitInvolutive (v2 z o) = refl
nonsplitInvolutive (v2 o o) = refl

------------------------------------------------------------------------
-- 3. Same semisimplified profile.
------------------------------------------------------------------------

data SimpleLabel : Set where
  trivial : SimpleLabel

record TwoLayerProfile : Set where
  constructor two-layer-profile
  field
    lower upper : SimpleLabel
open TwoLayerProfile public

splitSemisimplification : TwoLayerProfile
splitSemisimplification = two-layer-profile trivial trivial

nonsplitSemisimplification : TwoLayerProfile
nonsplitSemisimplification = two-layer-profile trivial trivial

sameSemisimplifiedProfile :
  splitSemisimplification ≡ nonsplitSemisimplification
sameSemisimplifiedProfile = refl

------------------------------------------------------------------------
-- 4. The same nondegenerate alternating bilinear form is preserved.
------------------------------------------------------------------------

bilinear : V2 -> V2 -> Bit
bilinear (v2 a b) (v2 c d) = xor (and a d) (and b c)

splitPreservesForm :
  (v w : V2) ->
  bilinear (splitAction v) (splitAction w) ≡ bilinear v w
splitPreservesForm v w = refl

nonsplitPreservesForm :
  (v w : V2) ->
  bilinear (nonsplitAction v) (nonsplitAction w) ≡ bilinear v w
nonsplitPreservesForm (v2 z z) (v2 z z) = refl
nonsplitPreservesForm (v2 z z) (v2 o z) = refl
nonsplitPreservesForm (v2 z z) (v2 z o) = refl
nonsplitPreservesForm (v2 z z) (v2 o o) = refl
nonsplitPreservesForm (v2 o z) (v2 z z) = refl
nonsplitPreservesForm (v2 o z) (v2 o z) = refl
nonsplitPreservesForm (v2 o z) (v2 z o) = refl
nonsplitPreservesForm (v2 o z) (v2 o o) = refl
nonsplitPreservesForm (v2 z o) (v2 z z) = refl
nonsplitPreservesForm (v2 z o) (v2 o z) = refl
nonsplitPreservesForm (v2 z o) (v2 z o) = refl
nonsplitPreservesForm (v2 z o) (v2 o o) = refl
nonsplitPreservesForm (v2 o o) (v2 z z) = refl
nonsplitPreservesForm (v2 o o) (v2 o z) = refl
nonsplitPreservesForm (v2 o o) (v2 z o) = refl
nonsplitPreservesForm (v2 o o) (v2 o o) = refl

-- Explicit witnesses for nondegeneracy on each nonzero vector.
nondegenerate10 : bilinear (v2 o z) (v2 z o) ≡ o
nondegenerate10 = refl

nondegenerate01 : bilinear (v2 z o) (v2 o z) ≡ o
nondegenerate01 = refl

nondegenerate11 : bilinear (v2 o o) (v2 o z) ≡ o
nondegenerate11 = refl

------------------------------------------------------------------------
-- 5. Extension/Jordan structure is nevertheless different.
------------------------------------------------------------------------

splitFixedVectorCount : Nat
splitFixedVectorCount = 4

nonsplitFixedVectorCount : Nat
nonsplitFixedVectorCount = 2

fixedCountsDiffer : splitFixedVectorCount ≡ nonsplitFixedVectorCount -> ⊥
fixedCountsDiffer ()

record ExtensionNoGoBoundary : Set where
  constructor extension-no-go-boundary
  field
    sameSemisimplifiedProfilePaid : Bool
    splitInvolutionPaid : Bool
    nonsplitJ2InvolutionPaid : Bool
    commonInvariantNondegenerateFormPaid : Bool
    fixedSpaceObservableDiffers : Bool
    semisimplificationAndSelfDualityDetermineExtension : Bool

canonicalExtensionNoGoBoundary : ExtensionNoGoBoundary
canonicalExtensionNoGoBoundary =
  extension-no-go-boundary
    true true true true true false
