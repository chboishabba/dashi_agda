module DASHI.Moonshine.OggSSPP2BanerjeeGaloisOrbitNoGoExact where

------------------------------------------------------------------------
-- BANERJEE p=2 GALOIS SHEET: FIVE ORBITS, NOT TEN
--
-- DASHI FINITE RECONSTRUCTION
--
-- The retained Banerjee presentation has two Galois-sheet labels and five
-- conjugacy/inversion-inertia labels.  Flipping the Galois sheet is free.
-- Its orbit label is the inertia sector alone.  Consequently the ten-state
-- retained presentation is NOT pi0 for the bare Galois C2 quotient.
--
-- This does not claim an actual action on Gamma_0(4) finite-flat structures:
-- that arithmetic recognition remains open.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2BanerjeeF4UniversalDeformationSourceExact as B
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Target
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

flipSheet : B.GaloisSheet -> B.GaloisSheet
flipSheet B.identityGaloisSheet = B.frobeniusGaloisSheet
flipSheet B.frobeniusGaloisSheet = B.identityGaloisSheet

flipSheetInvolutive :
  (sheet : B.GaloisSheet) ->
  flipSheet (flipSheet sheet) ≡ sheet
flipSheetInvolutive B.identityGaloisSheet = refl
flipSheetInvolutive B.frobeniusGaloisSheet = refl

flipSheetMoves :
  (sheet : B.GaloisSheet) ->
  flipSheet sheet ≡ sheet -> ⊥
flipSheetMoves B.identityGaloisSheet ()
flipSheetMoves B.frobeniusGaloisSheet ()

galoisFlip : B.GaloisInertiaState -> B.GaloisInertiaState
galoisFlip (sheet , inertia) = flipSheet sheet , inertia

galoisFlipInvolutive :
  (state : B.GaloisInertiaState) ->
  galoisFlip (galoisFlip state) ≡ state
galoisFlipInvolutive (B.identityGaloisSheet , inertia) = refl
galoisFlipInvolutive (B.frobeniusGaloisSheet , inertia) = refl

galoisFlipMoves :
  (state : B.GaloisInertiaState) ->
  galoisFlip state ≡ state -> ⊥
galoisFlipMoves (B.identityGaloisSheet , inertia) ()
galoisFlipMoves (B.frobeniusGaloisSheet , inertia) ()

galoisOrbitLabel :
  B.GaloisInertiaState ->
  Inertia.BinaryTetrahedralInversionOrbit
galoisOrbitLabel = proj₂

galoisOrbitInvariant :
  (state : B.GaloisInertiaState) ->
  galoisOrbitLabel (galoisFlip state) ≡ galoisOrbitLabel state
galoisOrbitInvariant (sheet , inertia) = refl

orbitRepresentative :
  Inertia.BinaryTetrahedralInversionOrbit ->
  B.GaloisInertiaState
orbitRepresentative orbit = B.identityGaloisSheet , orbit

orbitRepresentativeExact :
  (orbit : Inertia.BinaryTetrahedralInversionOrbit) ->
  galoisOrbitLabel (orbitRepresentative orbit) ≡ orbit
orbitRepresentativeExact orbit = refl

-- The exact ten-state rechart separates states that the Galois quotient
-- identifies, so it cannot be an invariant observer for this action.
targetMapNotGaloisInvariant :
  ((state : B.GaloisInertiaState) ->
     B.toTarget (galoisFlip state) ≡ B.toTarget state) ->
  ⊥
targetMapNotGaloisInvariant invariant =
  impossible (invariant (B.identityGaloisSheet , Inertia.identityInertiaOrbit))
  where
    impossible :
      Target.fixedOneRefinement ≡ Target.fixedZeroRefinement -> ⊥
    impossible ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record BanerjeeGaloisOrbitNoGoBoundary : Set where
  constructor banerjee-galois-orbit-no-go-boundary
  field
    galoisFlipFree : Bool
    inertiaFiveIsOrbitLabel : Bool
    targetTenLabelMapIsGaloisInvariant : Bool
    gamma0FourArithmeticRecognitionClaimed : Bool

canonicalBanerjeeGaloisOrbitNoGoBoundary :
  BanerjeeGaloisOrbitNoGoBoundary
canonicalBanerjeeGaloisOrbitNoGoBoundary =
  banerjee-galois-orbit-no-go-boundary true true false false
