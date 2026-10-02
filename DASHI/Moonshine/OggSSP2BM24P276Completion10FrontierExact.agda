module DASHI.Moonshine.OggSSP2BM24P276Completion10FrontierExact where

------------------------------------------------------------------------
-- M24 DEGREE-276 -> M22 LOCAL -> COMPLETION10 FRONTIER
--
-- External finite-group source:
-- Atlas of Finite Group Representations, M24 permutation representation
-- M24G1-p276B0:
--   degree 276,
--   primitive rank 3,
--   suborbit lengths 1,44,231,
--   character 1+23+252,
--   point stabilizer M22:2.
--
-- DASHI runtime screens:
--   scripts/m24_276_to_m22_f2_composition_screen.g
--   scripts/m22_completion10_involution_screen.g
--
-- Semantic boundary:
-- the ATLAS degree-276 M24 permutation module is a concrete finite candidate
-- carrier.  The Carnahan--Urano 2B Tate multiplicity is a distinct sourced
-- object of the same dimension.  No equality between them is asserted here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as Orbifold
import DASHI.Moonshine.OggP31CompletionTenTwoSevenNineCrossPollinationExact as P279

------------------------------------------------------------------------
-- 1. Sourced finite representation metadata.
------------------------------------------------------------------------

record AtlasM24P276Receipt : Set where
  constructor atlas-m24-p276-receipt
  field
    sourceURL : String
    groupName : String
    degree : Nat
    rank : Nat
    suborbitOne : Nat
    suborbitTwo : Nat
    suborbitThree : Nat
    characterDegreeOne : Nat
    characterDegreeTwentyThree : Nat
    characterDegreeTwoFiftyTwo : Nat
    pointStabilizer : String

open AtlasM24P276Receipt public

canonicalAtlasM24P276Receipt : AtlasM24P276Receipt
canonicalAtlasM24P276Receipt =
  atlas-m24-p276-receipt
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/M24G1-p276B0"
    "M24"
    276
    3
    1
    44
    231
    1
    23
    252
    "M22:2"

atlasDegreeIs276 : degree canonicalAtlasM24P276Receipt ≡ 276
atlasDegreeIs276 = refl

atlasSuborbitsCloseDegree :
  suborbitOne canonicalAtlasM24P276Receipt
  + suborbitTwo canonicalAtlasM24P276Receipt
  + suborbitThree canonicalAtlasM24P276Receipt
  ≡ degree canonicalAtlasM24P276Receipt
atlasSuborbitsCloseDegree = refl

atlasCharacterDegreesCloseDegree :
  characterDegreeOne canonicalAtlasM24P276Receipt
  + characterDegreeTwentyThree canonicalAtlasM24P276Receipt
  + characterDegreeTwoFiftyTwo canonicalAtlasM24P276Receipt
  ≡ degree canonicalAtlasM24P276Receipt
atlasCharacterDegreesCloseDegree = refl

------------------------------------------------------------------------
-- 2. Independent 276 owner already present in the Moonshine weight-two chart.
------------------------------------------------------------------------

orbifoldOffDiagonal276 : Nat
orbifoldOffDiagonal276 = Orbifold.offDiagonalCoordinateCount

orbifoldOffDiagonal276Is276 : orbifoldOffDiagonal276 ≡ 276
orbifoldOffDiagonal276Is276 = refl

shared276Scalar :
  degree canonicalAtlasM24P276Receipt ≡ orbifoldOffDiagonal276
shared276Scalar = refl

-- Pure arithmetic pair count: 24*23 = 2*276.
twentyFourPairDoubleCount : 24 * 23 ≡ 2 * 276
twentyFourPairDoubleCount = refl

------------------------------------------------------------------------
-- 3. Same-number firewalls.
------------------------------------------------------------------------

data AtlasP276IsCarnahanUranoTate276 : Set where
data OrbifoldCoordinate276IsCarnahanUranoTate276 : Set where
data Shared276ConstructsCompletion10 : Set where

atlasP276DoesNotBecomeTate276ByDimension :
  AtlasP276IsCarnahanUranoTate276 → ⊥
atlasP276DoesNotBecomeTate276ByDimension ()

orbifold276DoesNotBecomeTate276ByDimension :
  OrbifoldCoordinate276IsCarnahanUranoTate276 → ⊥
orbifold276DoesNotBecomeTate276ByDimension ()

shared276DoesNotConstructCompletion10 :
  Shared276ConstructsCompletion10 → ⊥
shared276DoesNotConstructCompletion10 ()

------------------------------------------------------------------------
-- 4. Runtime recognition seam.
--
-- The executable MeatAxe screen asks whether the actual M24 p276 module,
-- restricted first to M22:2 and then to M22, has a 10-dimensional F2
-- composition factor.  Independently, the M22 screen asks whether an actual
-- 10-dimensional M22 representation contains an involution with J2^5
-- fingerprint rank(g-I)=5, fixdim=5.
------------------------------------------------------------------------

record M24P276ToCompletion10RuntimeFrontier : Set where
  constructor m24-p276-to-completion10-runtime-frontier
  field
    atlasP276Constructible : Bool
    pointStabilizerM22d2Checked : Bool
    derivedM22Checked : Bool
    modTwoCompositionFactorsComputed : Bool
    tenDimensionalM22FactorObserved : Bool
    m22TenDimensionalInvolutionClassesScreened : Bool
    j2PowerFiveFingerprintObserved : Bool
    atlasP276IdentifiedWithActual2BTate276 : Bool
    completion10SameObjectEmbeddingPaid : Bool
    downstreamP31To279AlreadyOwned : Bool
    nextResidual : String

canonicalM24P276ToCompletion10RuntimeFrontier :
  M24P276ToCompletion10RuntimeFrontier
canonicalM24P276ToCompletion10RuntimeFrontier =
  m24-p276-to-completion10-runtime-frontier
    true
    true
    true
    false
    false
    false
    false
    false
    false
    true
    "consume the generated M22Completion10RuntimeCertificate; if a 10d M22 factor and J2^5 involution are observed, identify that finite factor explicitly, then prove or falsify the independent same-object weld from Carnahan--Urano 2B Tate Hhat0 to the ATLAS M24 p276 module"

------------------------------------------------------------------------
-- 5. Downstream arithmetic remains available only after recognition.
------------------------------------------------------------------------

downstreamCompletion10To279 :
  9 * (1 + 3 * 10) ≡ 279
downstreamCompletion10To279 = P279.completionTenTo279Composite

