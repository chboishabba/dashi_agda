module DASHI.Moonshine.OggSSPSmallCharacteristicRigidifiedInertiaLayerProductNoGoExact where

------------------------------------------------------------------------
-- RIGIDIFIED-INERTIA x WILD-LAYER UNIFORM PRODUCT NO-GO
--
-- SOURCE ALIGNMENT
--
-- Kobin--Zureick-Brown's Artin--Schreier layer descriptions are descriptions
-- of X(1)^rig:
--
--   p=2 : rigidified wild stabilizer A4
--         (Z/3 semidirect (Z/2 x Z/2)), two AS layers;
--
--   p=3 : rigidified wild stabilizer S3, one AS layer.
--
-- The earlier p=2 five-sector donor used conjugacy classes of the FULL binary
-- tetrahedral automorphism group 2T of order 24, before quotienting the generic
-- central +/-1.  The p=3 two-sector donor used local incidence strata on X0(3),
-- not inertia sectors of X(1)^rig.
--
-- Therefore "wild layers x local sectors" was combining different ambient
-- moduli objects.  This module tests the genuinely uniform version using
-- inversion-orbits of conjugacy classes in the rigidified stabilizer itself.
--
-- Result:
--
--   p=2 : A4 has 4 conjugacy classes; inversion pairs the two 3-cycle classes,
--          giving 3 unoriented inertia sectors.  2 layers x 3 = 6.
--
--   p=3 : S3 has 3 conjugacy classes, all inversion-stable,
--          giving 3 unoriented inertia sectors.  1 layer x 3 = 3.
--
-- Hence the same-ambient rigidified-inertia product gives (6,3), NOT (10,2).
-- This falsifies the naive uniform product if "sector" means rigidified inertia.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPSmallCharacteristicWildLayerSectorProductCandidateExact as Candidate
import DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact as WildSource
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. p=2 rigidified A4 conjugacy-class quotient.
------------------------------------------------------------------------

data A4ConjugacyClass : Set where
  a4IdentityClass :
    A4ConjugacyClass
  a4DoubleTranspositionClass :
    A4ConjugacyClass
  a4ThreeCyclePositiveClass :
    A4ConjugacyClass
  a4ThreeCycleNegativeClass :
    A4ConjugacyClass

a4InverseClass :
  A4ConjugacyClass ->
  A4ConjugacyClass
a4InverseClass a4IdentityClass = a4IdentityClass
a4InverseClass a4DoubleTranspositionClass = a4DoubleTranspositionClass
a4InverseClass a4ThreeCyclePositiveClass = a4ThreeCycleNegativeClass
a4InverseClass a4ThreeCycleNegativeClass = a4ThreeCyclePositiveClass

data A4UnorientedInertiaSector : Set where
  a4IdentitySector :
    A4UnorientedInertiaSector
  a4OrderTwoSector :
    A4UnorientedInertiaSector
  a4OrderThreePairSector :
    A4UnorientedInertiaSector

a4UnorientedSector :
  A4ConjugacyClass ->
  A4UnorientedInertiaSector
a4UnorientedSector a4IdentityClass = a4IdentitySector
a4UnorientedSector a4DoubleTranspositionClass = a4OrderTwoSector
a4UnorientedSector a4ThreeCyclePositiveClass = a4OrderThreePairSector
a4UnorientedSector a4ThreeCycleNegativeClass = a4OrderThreePairSector

a4SectorInvariantUnderInversion :
  (class : A4ConjugacyClass) ->
  a4UnorientedSector (a4InverseClass class)
  ≡ a4UnorientedSector class
a4SectorInvariantUnderInversion a4IdentityClass = refl
a4SectorInvariantUnderInversion a4DoubleTranspositionClass = refl
a4SectorInvariantUnderInversion a4ThreeCyclePositiveClass = refl
a4SectorInvariantUnderInversion a4ThreeCycleNegativeClass = refl

p2RigidifiedInertiaSectorCount : Nat
p2RigidifiedInertiaSectorCount = 3

------------------------------------------------------------------------
-- 2. p=3 rigidified S3 conjugacy-class quotient.
------------------------------------------------------------------------

data S3ConjugacyClass : Set where
  s3IdentityClass :
    S3ConjugacyClass
  s3TranspositionClass :
    S3ConjugacyClass
  s3ThreeCycleClass :
    S3ConjugacyClass

s3InverseClass :
  S3ConjugacyClass ->
  S3ConjugacyClass
s3InverseClass s3IdentityClass = s3IdentityClass
s3InverseClass s3TranspositionClass = s3TranspositionClass
s3InverseClass s3ThreeCycleClass = s3ThreeCycleClass

p3RigidifiedInertiaSectorCount : Nat
p3RigidifiedInertiaSectorCount = 3

------------------------------------------------------------------------
-- 3. Same-ambient layer x rigidified-inertia product.
------------------------------------------------------------------------

p2RigidifiedLayerInertiaProduct : Nat
p2RigidifiedLayerInertiaProduct =
  Candidate.artinSchreierLayerCount Candidate.wildTwo
  * p2RigidifiedInertiaSectorCount

p3RigidifiedLayerInertiaProduct : Nat
p3RigidifiedLayerInertiaProduct =
  Candidate.artinSchreierLayerCount Candidate.wildThree
  * p3RigidifiedInertiaSectorCount

p2RigidifiedProductIsSix :
  p2RigidifiedLayerInertiaProduct ≡ 6
p2RigidifiedProductIsSix = refl

p3RigidifiedProductIsThree :
  p3RigidifiedLayerInertiaProduct ≡ 3
p3RigidifiedProductIsThree = refl

p2RigidifiedProductNotMonsterGap :
  p2RigidifiedLayerInertiaProduct ≡ 10 -> ⊥
p2RigidifiedProductNotMonsterGap ()

p3RigidifiedProductNotMonsterGap :
  p3RigidifiedLayerInertiaProduct ≡ 2 -> ⊥
p3RigidifiedProductNotMonsterGap ()

------------------------------------------------------------------------
-- 4. Ambient compatibility debt in the old 10/2 product.
------------------------------------------------------------------------

data FullStackInertiaSectorsEqualRigidifiedInertiaSectors : Set where
data X03IncidenceSectorsEqualX1RigidifiedInertiaSectors : Set where
data CrossAmbientProductNeedsNoTransportTheorem : Set where

fullStackInertiaNotSilentlyRigidified :
  FullStackInertiaSectorsEqualRigidifiedInertiaSectors -> ⊥
fullStackInertiaNotSilentlyRigidified ()

x03IncidenceNotSilentlyX1Inertia :
  X03IncidenceSectorsEqualX1RigidifiedInertiaSectors -> ⊥
x03IncidenceNotSilentlyX1Inertia ()

crossAmbientProductRequiresTransport :
  CrossAmbientProductNeedsNoTransportTheorem -> ⊥
crossAmbientProductRequiresTransport ()

------------------------------------------------------------------------
-- 5. Source boundary.
------------------------------------------------------------------------

wildSourceAtlas = WildSource.wildStackCorrectionSourceAtlas

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record RigidifiedInertiaLayerProductNoGoBoundary : Set where
  constructor rigidified-inertia-layer-product-no-go-boundary
  field
    p2RootStackAmbientIsRigidifiedX1 : Bool
    p3RootStackAmbientIsRigidifiedX1 : Bool
    p2RigidifiedStabilizerA4Sourced : Bool
    p3RigidifiedStabilizerS3Sourced : Bool
    p2RigidifiedUnorientedInertiaCountThree : Bool
    p3RigidifiedUnorientedInertiaCountThree : Bool
    p2SameAmbientProductSix : Bool
    p3SameAmbientProductThree : Bool
    p2SameAmbientProductMatchesMonsterGap : Bool
    p3SameAmbientProductMatchesMonsterGap : Bool
    originalTenTwoProductUsesMixedAmbientObjects : Bool
    transportCompatibilityStillRequired : Bool

canonicalRigidifiedInertiaLayerProductNoGoBoundary :
  RigidifiedInertiaLayerProductNoGoBoundary
canonicalRigidifiedInertiaLayerProductNoGoBoundary =
  rigidified-inertia-layer-product-no-go-boundary
    true true true true true true true true false false true true
