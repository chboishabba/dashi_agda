module DASHI.Biology.SquareApollonianPackingComparison where

open import DASHI.Core.Prelude

import DASHI.Biology.RecursiveSpherePerforation as Perforation
import DASHI.Biology.MorphogeneticVisualGenerator as Morphogenesis

------------------------------------------------------------------------
-- Exact square-versus-Apollonian packing comparison.
--
-- Signed curvatures are represented by separating one enclosing negative
-- curvature from the positive inner curvatures.  The finite examples prove
-- exact Descartes and Soddy-Gosset identities by normalization.

data PackingFamily : Set where
  squarePackingFamily : PackingFamily
  apollonianCircleFamily : PackingFamily
  apollonianSphereFamily : PackingFamily
  squareSeededApollonianFamily : PackingFamily

record PackingSignature : Set where
  constructor packingSignature
  field
    globalTranslationPeriodicity : Bool
    orthogonalAxes : Bool
    localTangencyLaw : Bool
    curvedTriangularInterstices : Bool
    branchingGapGenealogy : Bool
    equalFirstGenerationRadii : Bool

open PackingSignature public

packingSignatureOf : PackingFamily → PackingSignature
packingSignatureOf squarePackingFamily =
  packingSignature true true false false false true
packingSignatureOf apollonianCircleFamily =
  packingSignature false false true true true false
packingSignatureOf apollonianSphereFamily =
  packingSignature false false true true true false
packingSignatureOf squareSeededApollonianFamily =
  packingSignature true true true true true true

squareHasGlobalOrthogonalOrder :
  globalTranslationPeriodicity
    (packingSignatureOf squarePackingFamily)
  ≡
  true
  ×
  orthogonalAxes
    (packingSignatureOf squarePackingFamily)
  ≡
  true
squareHasGlobalOrthogonalOrder = refl , refl

apollonianHasLocalTangencyBranching :
  localTangencyLaw
    (packingSignatureOf apollonianSphereFamily)
  ≡
  true
  ×
  branchingGapGenealogy
    (packingSignatureOf apollonianSphereFamily)
  ≡
  true
apollonianHasLocalTangencyBranching = refl , refl

hybridCarriesBothSignatureFamilies :
  globalTranslationPeriodicity
    (packingSignatureOf squareSeededApollonianFamily)
  ≡
  true
  ×
  localTangencyLaw
    (packingSignatureOf squareSeededApollonianFamily)
  ≡
  true
hybridCarriesBothSignatureFamilies = refl , refl

squareAndApollonianSignaturesDiffer :
  packingSignatureOf squarePackingFamily
  ≡
  packingSignatureOf apollonianSphereFamily
  →
  ⊥
squareAndApollonianSignaturesDiffer ()

------------------------------------------------------------------------
-- Descartes circle theorem example.
--
-- Signed curvature quadruple (-1, 2, 2, 3):
--
--   (-1 + 2 + 2 + 3)^2
--   = 2 (1^2 + 2^2 + 2^2 + 3^2)
--   = 36.

squareNat : Nat → Nat
squareNat n = n * n

descartesSignedSum : Nat
descartesSignedSum = (2 + 2 + 3) ∸ 1

descartesSquareSum : Nat
descartesSquareSum =
  squareNat 1
  + squareNat 2
  + squareNat 2
  + squareNat 3

descartesLeftIsThirtySix :
  squareNat descartesSignedSum ≡ 36
descartesLeftIsThirtySix = refl

descartesRightIsThirtySix :
  2 * descartesSquareSum ≡ 36
descartesRightIsThirtySix = refl

descartesCircleIdentity :
  squareNat descartesSignedSum
  ≡
  2 * descartesSquareSum
descartesCircleIdentity = refl

------------------------------------------------------------------------
-- Soddy-Gosset sphere theorem example.
--
-- Signed curvature quintuple (-4, 8, 8, 12, 12):
--
--   (-4 + 8 + 8 + 12 + 12)^2
--   = 3 (4^2 + 8^2 + 8^2 + 12^2 + 12^2)
--   = 1296.

soddyGossetSignedSum : Nat
soddyGossetSignedSum =
  (8 + 8 + 12 + 12) ∸ 4

soddyGossetSquareSum : Nat
soddyGossetSquareSum =
  squareNat 4
  + squareNat 8
  + squareNat 8
  + squareNat 12
  + squareNat 12

soddyGossetLeftIs1296 :
  squareNat soddyGossetSignedSum ≡ 1296
soddyGossetLeftIs1296 = refl

soddyGossetRightIs1296 :
  3 * soddyGossetSquareSum ≡ 1296
soddyGossetRightIs1296 = refl

soddyGossetSphereIdentity :
  squareNat soddyGossetSignedSum
  ≡
  3 * soddyGossetSquareSum
soddyGossetSphereIdentity = refl

------------------------------------------------------------------------
-- Gap and regularity consequences.

squareGapIsFourArc :
  Perforation.dominantGapShape Perforation.squareGridSeed
  ≡
  Perforation.curvedSquareGap
squareGapIsFourArc = refl

apollonianSeedGapIsThreeArc :
  Perforation.dominantGapShape Perforation.tangentTripleSeed
  ≡
  Perforation.curvedTriangularGap
apollonianSeedGapIsThreeArc = refl

apollonianRegularWithoutGlobalPeriodicity :
  Perforation.tangencyRegularity Perforation.apollonianRegularity
  ≡
  true
  ×
  Perforation.periodicRegularity Perforation.apollonianRegularity
  ≡
  false
apollonianRegularWithoutGlobalPeriodicity = refl , refl

hybridMatchesRememberedCueFamily :
  Morphogenesis.globalPeriodicity
    Morphogenesis.hybridMorphogeneticLaw
  ≡
  true
  ×
  Morphogenesis.curvedTriangularGaps
    Morphogenesis.hybridMorphogeneticLaw
  ≡
  true
  ×
  Morphogenesis.branchingCurvedPassages
    Morphogenesis.hybridMorphogeneticLaw
  ≡
  true
hybridMatchesRememberedCueFamily = refl , (refl , refl)

record PackingComparisonBoundary : Set where
  constructor packingComparisonBoundary
  field
    exactCurvatureIdentityRecoversRememberedScene : Bool
    exactCurvatureIdentityRecoversRememberedSceneIsFalse :
      exactCurvatureIdentityRecoversRememberedScene ≡ false

    squareAndApollonianAreMutuallyExclusiveAcrossScale : Bool
    squareAndApollonianAreMutuallyExclusiveAcrossScaleIsFalse :
      squareAndApollonianAreMutuallyExclusiveAcrossScale ≡ false

    signedNatExampleClassifiesAllPackings : Bool
    signedNatExampleClassifiesAllPackingsIsFalse :
      signedNatExampleClassifiesAllPackings ≡ false

open PackingComparisonBoundary public

canonicalPackingComparisonBoundary : PackingComparisonBoundary
canonicalPackingComparisonBoundary =
  packingComparisonBoundary false refl false refl false refl
