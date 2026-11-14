module DASHI.Mathematics.Symmetry.TetragonalHorizontalMirrorGroupActionExact where

-- Native finite GroupAction instance for the horizontal mirror C2
-- subgroup of classical D4h. This proves a genuine action on
-- the eight-site geometric carrier; the full D4h action is separate.
-- Reuses the native Erlangen GroupAction record; no postulates.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Mathematics.Symmetry.KleinGroupActionInvariantExact as Native
import DASHI.Mathematics.Symmetry.TetragonalD4hGeneratorActionExact as Geo

xor : Bool → Bool → Bool
xor false b = b
xor true false = true
xor true true = false

actMirror : Bool → Geo.Site → Geo.Site
actMirror false p = p
actMirror true p = Geo.H p

mirrorIdentity : (p : Geo.Site) → actMirror false p ≡ p
mirrorIdentity p = refl

mirrorCompose : (g h : Bool) (p : Geo.Site) →
  actMirror (xor g h) p ≡ actMirror g (actMirror h p)
mirrorCompose false false (Geo.site Geo.north Geo.above) = refl
mirrorCompose false false (Geo.site Geo.north Geo.below) = refl
mirrorCompose false false (Geo.site Geo.east Geo.above) = refl
mirrorCompose false false (Geo.site Geo.east Geo.below) = refl
mirrorCompose false false (Geo.site Geo.south Geo.above) = refl
mirrorCompose false false (Geo.site Geo.south Geo.below) = refl
mirrorCompose false false (Geo.site Geo.west Geo.above) = refl
mirrorCompose false false (Geo.site Geo.west Geo.below) = refl
mirrorCompose false true (Geo.site Geo.north Geo.above) = refl
mirrorCompose false true (Geo.site Geo.north Geo.below) = refl
mirrorCompose false true (Geo.site Geo.east Geo.above) = refl
mirrorCompose false true (Geo.site Geo.east Geo.below) = refl
mirrorCompose false true (Geo.site Geo.south Geo.above) = refl
mirrorCompose false true (Geo.site Geo.south Geo.below) = refl
mirrorCompose false true (Geo.site Geo.west Geo.above) = refl
mirrorCompose false true (Geo.site Geo.west Geo.below) = refl
mirrorCompose true false (Geo.site Geo.north Geo.above) = refl
mirrorCompose true false (Geo.site Geo.north Geo.below) = refl
mirrorCompose true false (Geo.site Geo.east Geo.above) = refl
mirrorCompose true false (Geo.site Geo.east Geo.below) = refl
mirrorCompose true false (Geo.site Geo.south Geo.above) = refl
mirrorCompose true false (Geo.site Geo.south Geo.below) = refl
mirrorCompose true false (Geo.site Geo.west Geo.above) = refl
mirrorCompose true false (Geo.site Geo.west Geo.below) = refl
mirrorCompose true true (Geo.site Geo.north Geo.above) = refl
mirrorCompose true true (Geo.site Geo.north Geo.below) = refl
mirrorCompose true true (Geo.site Geo.east Geo.above) = refl
mirrorCompose true true (Geo.site Geo.east Geo.below) = refl
mirrorCompose true true (Geo.site Geo.south Geo.above) = refl
mirrorCompose true true (Geo.site Geo.south Geo.below) = refl
mirrorCompose true true (Geo.site Geo.west Geo.above) = refl
mirrorCompose true true (Geo.site Geo.west Geo.below) = refl

horizontalMirrorAction : Native.GroupAction
horizontalMirrorAction = record
  { G = Bool
  ; X = Geo.Site
  ; identity = false
  ; compose = xor
  ; act = actMirror
  ; identityActs = mirrorIdentity
  ; composeActs = mirrorCompose
  }
