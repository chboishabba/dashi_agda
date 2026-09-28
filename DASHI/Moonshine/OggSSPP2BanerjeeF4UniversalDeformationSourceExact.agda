module DASHI.Moonshine.OggSSPP2BanerjeeF4UniversalDeformationSourceExact where

------------------------------------------------------------------------
-- p=2 BANERJEE F4 UNIVERSAL-DEFORMATION / G24 ⋊ GAL SOURCE SURFACE
--
-- EXTERNAL SOURCE
--
-- Romie Banerjee,
-- "A modular description of ER(2)",
-- New York Journal of Mathematics 20 (2014), 743-758,
-- arXiv:1212.2069.
--
-- Source facts recorded:
--
--   C : y^2 + y = x^3 over F4;
--   Aut_F4(C) = G24, the binary tetrahedral group of order 24;
--   Def(C,F4) -> Ell^ss_2 is an etale
--       G24 ⋊ Gal(F4/F2)-torsor;
--   Def(C,F4) ~= Spf W(F4)[[a1]];
--   the universal lift is y^2 + a1*x*y + y = x^3.
--
-- DASHI RECONSTRUCTION
--
-- The repository already reconstructs five inversion-orbits from the seven
-- G24 conjugacy classes.  Retaining the binary Gal(F4/F2) sheet gives a
-- same-source 2 x 5 = 10 sector candidate.
--
-- Banerjee does NOT state this five-orbit inversion quotient, the ten-state
-- product, a Gamma0(4) ten-point fibre, or an identification of the Galois
-- sheet with the Goren--Love quadratic-orientation doublet.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Target
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source-native Galois sheet.
------------------------------------------------------------------------

data GaloisSheet : Set where
  identityGaloisSheet : GaloisSheet
  frobeniusGaloisSheet : GaloisSheet

GaloisInertiaState : Set
GaloisInertiaState =
  GaloisSheet × Inertia.BinaryTetrahedralInversionOrbit

------------------------------------------------------------------------
-- 2. Exact finite rechart to the paid p=2 target.
------------------------------------------------------------------------

toTarget :
  GaloisInertiaState ->
  Target.F4StratifiedTargetState
toTarget
  (identityGaloisSheet , Inertia.identityInertiaOrbit) =
  Target.fixedZeroRefinement
toTarget
  (frobeniusGaloisSheet , Inertia.identityInertiaOrbit) =
  Target.fixedOneRefinement
toTarget
  (identityGaloisSheet , Inertia.centralMinusOneInertiaOrbit) =
  Target.conjugateRefinement Compression.lowerSide Target.firstAxisNoncentral
toTarget
  (frobeniusGaloisSheet , Inertia.centralMinusOneInertiaOrbit) =
  Target.conjugateRefinement Compression.upperSide Target.firstAxisNoncentral
toTarget
  (identityGaloisSheet , Inertia.orderFourInertiaOrbit) =
  Target.conjugateRefinement Compression.lowerSide Target.secondAxisNoncentral
toTarget
  (frobeniusGaloisSheet , Inertia.orderFourInertiaOrbit) =
  Target.conjugateRefinement Compression.upperSide Target.secondAxisNoncentral
toTarget
  (identityGaloisSheet , Inertia.orderThreePairInertiaOrbit) =
  Target.conjugateRefinement Compression.lowerSide Target.equalSignNoncentral
toTarget
  (frobeniusGaloisSheet , Inertia.orderThreePairInertiaOrbit) =
  Target.conjugateRefinement Compression.upperSide Target.equalSignNoncentral
toTarget
  (identityGaloisSheet , Inertia.orderSixPairInertiaOrbit) =
  Target.conjugateRefinement Compression.lowerSide Target.oppositeSignNoncentral
toTarget
  (frobeniusGaloisSheet , Inertia.orderSixPairInertiaOrbit) =
  Target.conjugateRefinement Compression.upperSide Target.oppositeSignNoncentral

fromTarget :
  Target.F4StratifiedTargetState ->
  GaloisInertiaState
fromTarget Target.fixedZeroRefinement =
  identityGaloisSheet , Inertia.identityInertiaOrbit
fromTarget Target.fixedOneRefinement =
  frobeniusGaloisSheet , Inertia.identityInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.lowerSide Target.firstAxisNoncentral) =
  identityGaloisSheet , Inertia.centralMinusOneInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.upperSide Target.firstAxisNoncentral) =
  frobeniusGaloisSheet , Inertia.centralMinusOneInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.lowerSide Target.secondAxisNoncentral) =
  identityGaloisSheet , Inertia.orderFourInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.upperSide Target.secondAxisNoncentral) =
  frobeniusGaloisSheet , Inertia.orderFourInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.lowerSide Target.equalSignNoncentral) =
  identityGaloisSheet , Inertia.orderThreePairInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.upperSide Target.equalSignNoncentral) =
  frobeniusGaloisSheet , Inertia.orderThreePairInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.lowerSide Target.oppositeSignNoncentral) =
  identityGaloisSheet , Inertia.orderSixPairInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.upperSide Target.oppositeSignNoncentral) =
  frobeniusGaloisSheet , Inertia.orderSixPairInertiaOrbit

sourceRoundTrip :
  (state : GaloisInertiaState) ->
  fromTarget (toTarget state) ≡ state
sourceRoundTrip
  (identityGaloisSheet , Inertia.identityInertiaOrbit) = refl
sourceRoundTrip
  (frobeniusGaloisSheet , Inertia.identityInertiaOrbit) = refl
sourceRoundTrip
  (identityGaloisSheet , Inertia.centralMinusOneInertiaOrbit) = refl
sourceRoundTrip
  (frobeniusGaloisSheet , Inertia.centralMinusOneInertiaOrbit) = refl
sourceRoundTrip
  (identityGaloisSheet , Inertia.orderFourInertiaOrbit) = refl
sourceRoundTrip
  (frobeniusGaloisSheet , Inertia.orderFourInertiaOrbit) = refl
sourceRoundTrip
  (identityGaloisSheet , Inertia.orderThreePairInertiaOrbit) = refl
sourceRoundTrip
  (frobeniusGaloisSheet , Inertia.orderThreePairInertiaOrbit) = refl
sourceRoundTrip
  (identityGaloisSheet , Inertia.orderSixPairInertiaOrbit) = refl
sourceRoundTrip
  (frobeniusGaloisSheet , Inertia.orderSixPairInertiaOrbit) = refl

targetRoundTrip :
  (state : Target.F4StratifiedTargetState) ->
  toTarget (fromTarget state) ≡ state
targetRoundTrip Target.fixedZeroRefinement = refl
targetRoundTrip Target.fixedOneRefinement = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.lowerSide Target.firstAxisNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.upperSide Target.firstAxisNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.lowerSide Target.secondAxisNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.upperSide Target.secondAxisNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.lowerSide Target.equalSignNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.upperSide Target.equalSignNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.lowerSide Target.oppositeSignNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.upperSide Target.oppositeSignNoncentral) = refl

------------------------------------------------------------------------
-- 3. Typed source receipt.
------------------------------------------------------------------------

record BanerjeeF4UniversalDeformationReceipt : Set where
  constructor banerjee-f4-universal-deformation-receipt
  field
    curveY2PlusYEqualsX3OverF4 : Bool
    automorphismGroupIsG24 : Bool
    universalDeformationIsG24SemidirectGaloisTorsor : Bool
    deformationBaseIsWittF4PowerSeries : Bool
    universalLiftEquationRecorded : Bool
    sourceTitle : String
    sourceLocator : String

canonicalBanerjeeF4UniversalDeformationReceipt :
  BanerjeeF4UniversalDeformationReceipt
canonicalBanerjeeF4UniversalDeformationReceipt =
  banerjee-f4-universal-deformation-receipt
    true true true true true
    "Romie Banerjee, A modular description of ER(2), New York Journal of Mathematics 20 (2014), 743-758"
    "Section 3.1, Proposition 3.1; arXiv:1212.2069"

------------------------------------------------------------------------
-- 4. Promotion firewalls.
------------------------------------------------------------------------

data BanerjeeStatesFiveInversionOrbitQuotient : Set where
data GaloisSheetIsQuadraticOrientation : Set where
data TenSectorsAreTenGamma04LevelPoints : Set where

banerjeeDoesNotStateFiveInversionOrbitQuotient :
  BanerjeeStatesFiveInversionOrbitQuotient -> ⊥
banerjeeDoesNotStateFiveInversionOrbitQuotient ()

galoisSheetDoesNotBecomeQuadraticOrientation :
  GaloisSheetIsQuadraticOrientation -> ⊥
galoisSheetDoesNotBecomeQuadraticOrientation ()

tenSectorsDoNotBecomeGamma04LevelPoints :
  TenSectorsAreTenGamma04LevelPoints -> ⊥
tenSectorsDoNotBecomeGamma04LevelPoints ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record BanerjeeF4UniversalDeformationBoundary : Set where
  constructor banerjee-f4-universal-deformation-boundary
  field
    sourceCurveOverF4Recorded : Bool
    sourceG24ActionRecorded : Bool
    sourceGaloisActionRecorded : Bool
    sourceSameDeformationTorsorRecorded : Bool
    sourceWittF4PowerSeriesBaseRecorded : Bool
    fiveInversionOrbitQuotientIsRepositoryReconstruction : Bool
    exactTwoTimesFiveCarrierConstructed : Bool
    exactRechartToPaidTenStateTarget : Bool
    galoisSheetIdentifiedWithQuadraticOrientation : Bool
    gamma04TenPointIdentityClaimed : Bool

canonicalBanerjeeF4UniversalDeformationBoundary :
  BanerjeeF4UniversalDeformationBoundary
canonicalBanerjeeF4UniversalDeformationBoundary =
  banerjee-f4-universal-deformation-boundary
    true true true true true true true true false false
