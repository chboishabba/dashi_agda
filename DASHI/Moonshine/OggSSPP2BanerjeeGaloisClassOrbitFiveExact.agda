module DASHI.Moonshine.OggSSPP2BanerjeeGaloisClassOrbitFiveExact where

------------------------------------------------------------------------
-- BANERJEE GALOIS ACTION ON G24 CONJUGACY CLASSES
--
-- Source + reconstruction:
--
--   * G24 has seven conjugacy classes.
--   * the nontrivial Gal(F4/F2) outer action fixes the identity, central -1,
--     and order-4 class, while swapping the two order-3 classes and the two
--     order-6 classes.
--
-- On the repository's seven-class presentation this is exactly the same
-- permutation as inverseClass.
--
-- Therefore the five inversion-orbits already constructed in
-- OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact are also the five Galois
-- class-orbits.  A later Galois-sheet x five product is retained-sheet
-- presentation data, not a second independent quotient coordinate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2BanerjeeF4UniversalDeformationSourceExact as Banerjee
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

galoisClassAction :
  Inertia.BinaryTetrahedralConjugacyClass ->
  Inertia.BinaryTetrahedralConjugacyClass
galoisClassAction Inertia.identityClass =
  Inertia.identityClass
galoisClassAction Inertia.centralMinusOneClass =
  Inertia.centralMinusOneClass
galoisClassAction Inertia.orderFourClass =
  Inertia.orderFourClass
galoisClassAction Inertia.orderThreePositiveClass =
  Inertia.orderThreeNegativeClass
galoisClassAction Inertia.orderThreeNegativeClass =
  Inertia.orderThreePositiveClass
galoisClassAction Inertia.orderSixPositiveClass =
  Inertia.orderSixNegativeClass
galoisClassAction Inertia.orderSixNegativeClass =
  Inertia.orderSixPositiveClass

galoisClassActionEqualsInversion :
  (class : Inertia.BinaryTetrahedralConjugacyClass) ->
  galoisClassAction class ≡ Inertia.inverseClass class
galoisClassActionEqualsInversion Inertia.identityClass = refl
galoisClassActionEqualsInversion Inertia.centralMinusOneClass = refl
galoisClassActionEqualsInversion Inertia.orderFourClass = refl
galoisClassActionEqualsInversion Inertia.orderThreePositiveClass = refl
galoisClassActionEqualsInversion Inertia.orderThreeNegativeClass = refl
galoisClassActionEqualsInversion Inertia.orderSixPositiveClass = refl
galoisClassActionEqualsInversion Inertia.orderSixNegativeClass = refl

galoisClassActionInvolutive :
  (class : Inertia.BinaryTetrahedralConjugacyClass) ->
  galoisClassAction (galoisClassAction class) ≡ class
galoisClassActionInvolutive Inertia.identityClass = refl
galoisClassActionInvolutive Inertia.centralMinusOneClass = refl
galoisClassActionInvolutive Inertia.orderFourClass = refl
galoisClassActionInvolutive Inertia.orderThreePositiveClass = refl
galoisClassActionInvolutive Inertia.orderThreeNegativeClass = refl
galoisClassActionInvolutive Inertia.orderSixPositiveClass = refl
galoisClassActionInvolutive Inertia.orderSixNegativeClass = refl

galoisQuotientToFive :
  Inertia.BinaryTetrahedralConjugacyClass ->
  Inertia.BinaryTetrahedralInversionOrbit
galoisQuotientToFive =
  Inertia.quotientByInversion

galoisQuotientInvariant :
  (class : Inertia.BinaryTetrahedralConjugacyClass) ->
  galoisQuotientToFive (galoisClassAction class)
  ≡ galoisQuotientToFive class
galoisQuotientInvariant Inertia.identityClass = refl
galoisQuotientInvariant Inertia.centralMinusOneClass = refl
galoisQuotientInvariant Inertia.orderFourClass = refl
galoisQuotientInvariant Inertia.orderThreePositiveClass = refl
galoisQuotientInvariant Inertia.orderThreeNegativeClass = refl
galoisQuotientInvariant Inertia.orderSixPositiveClass = refl
galoisQuotientInvariant Inertia.orderSixNegativeClass = refl

RetainedGaloisSheetPresentation : Set
RetainedGaloisSheetPresentation =
  Banerjee.GaloisSheet × Inertia.BinaryTetrahedralInversionOrbit

data GaloisSheetIsIndependentSecondQuotientCoordinate : Set where
data RetainedSheetTenIsSourceNativeQuotient : Set where

galoisSheetIsNotIndependentSecondQuotientCoordinate :
  GaloisSheetIsIndependentSecondQuotientCoordinate -> ⊥
galoisSheetIsNotIndependentSecondQuotientCoordinate ()

retainedSheetTenDoesNotBecomeSourceNativeQuotient :
  RetainedSheetTenIsSourceNativeQuotient -> ⊥
retainedSheetTenDoesNotBecomeSourceNativeQuotient ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record BanerjeeGaloisClassOrbitFiveBoundary : Set where
  constructor banerjee-galois-class-orbit-five-boundary
  field
    sevenClassCarrierReused : Bool
    galoisOuterClassActionReconstructed : Bool
    galoisActionEqualsInversionOnClasses : Bool
    galoisOrbitQuotientIsFiveCarrier : Bool
    galoisSheetIndependentOfFiveOrbitQuotient : Bool
    retainedSheetTimesFivePresentationOwned : Bool
    retainedTenPromotedToSourceNativeQuotient : Bool

canonicalBanerjeeGaloisClassOrbitFiveBoundary :
  BanerjeeGaloisClassOrbitFiveBoundary
canonicalBanerjeeGaloisClassOrbitFiveBoundary =
  banerjee-galois-class-orbit-five-boundary
    true true true true false true false
