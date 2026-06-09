module DASHI.Physics.Closure.CKMV3SpurionTextureFrontierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DHRIntertwinerPSL2F7TextureReceipt as Bilinear
import DASHI.Physics.Closure.PSL2F7RankOneYdTextureReceipt as RankOne

------------------------------------------------------------------------
-- CKM V3 spurion / Yukawa texture frontier receipt.
--
-- This is the corrected frontier receipt.  The character computation says:
--
--   < V3 tensor V3 , 1 > = 0
--   < V3 tensor V3 tensor V3 , 1 > = 1
--
-- The unique triple invariant lies in the exterior determinant channel.
-- Therefore a pure V3 spurion gives a generic antisymmetric rank-2 texture;
-- a third-generation rank-1 texture requires an additional residual selector.
-- No physical Y_d or CKM matrix is promoted here.

data CKMV3SpurionTextureFrontierStatus : Set where
  spurionTexture_rankOneResult_phenomenologyRequired :
    CKMV3SpurionTextureFrontierStatus

data PSL2F7TensorFact : Set where
  V3TensorV3HasNoTrivial :
    PSL2F7TensorFact

  V3TensorV3EqualsV3ConjPlusV6 :
    PSL2F7TensorFact

  V3TensorV3TensorV3HasOneTrivial :
    PSL2F7TensorFact

  V3TensorV3TensorV3EqualsV1PlusV3ConjPlusV7PlusTwoV8 :
    PSL2F7TensorFact

  symmetricCubeV3HasNoTrivial :
    PSL2F7TensorFact

  exteriorCubeV3HasOneTrivial :
    PSL2F7TensorFact

canonicalPSL2F7TensorFacts :
  List PSL2F7TensorFact
canonicalPSL2F7TensorFacts =
  V3TensorV3HasNoTrivial
  ∷ V3TensorV3EqualsV3ConjPlusV6
  ∷ V3TensorV3TensorV3HasOneTrivial
  ∷ V3TensorV3TensorV3EqualsV1PlusV3ConjPlusV7PlusTwoV8
  ∷ symmetricCubeV3HasNoTrivial
  ∷ exteriorCubeV3HasOneTrivial
  ∷ []

data TextureFrontierShape : Set where
  exactBilinearForbidden :
    TextureFrontierShape

  pureV3SpurionAntisymmetricRankTwoGeneric :
    TextureFrontierShape

  residualSelectorRankOneAnsatz :
    TextureFrontierShape

  V6SpurionRouteSeparate :
    TextureFrontierShape

canonicalTextureFrontierShapes :
  List TextureFrontierShape
canonicalTextureFrontierShapes =
  exactBilinearForbidden
  ∷ pureV3SpurionAntisymmetricRankTwoGeneric
  ∷ residualSelectorRankOneAnsatz
  ∷ V6SpurionRouteSeparate
  ∷ []

data FrontierProofObligation : Set where
  constructExteriorInvariantIntertwiner :
    FrontierProofObligation

  constructPureV3SpurionAntisymmetricTexture :
    FrontierProofObligation

  justifyResidualHeavyGenerationSelector :
    FrontierProofObligation

  separateV6SpurionTextureRoute :
    FrontierProofObligation

  supplyExternalYdDynamicsBeforePromotion :
    FrontierProofObligation

canonicalFrontierProofObligations :
  List FrontierProofObligation
canonicalFrontierProofObligations =
  constructExteriorInvariantIntertwiner
  ∷ constructPureV3SpurionAntisymmetricTexture
  ∷ justifyResidualHeavyGenerationSelector
  ∷ separateV6SpurionTextureRoute
  ∷ supplyExternalYdDynamicsBeforePromotion
  ∷ []

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

tripleInvariantStatement :
  String
tripleInvariantStatement =
  "The corrected character computation gives <V3 tensor V3 tensor V3,1>=1, with the invariant in the exterior determinant channel."

rankOneCorrectionStatement :
  String
rankOneCorrectionStatement =
  "A pure V3 spurion does not force a rank-1 heavy-generation projector; the generic pure-V3 texture is antisymmetric of rank 2, and rank 1 requires an additional residual selector."

boundaryStatement :
  String
boundaryStatement =
  "Frontier only: the receipt corrects the V3 spurion route and records obligations; it does not derive Y_d, CKM angles, or physical Yukawa dynamics."

record CKMV3SpurionTextureFrontierReceipt : Set where
  field
    status :
      CKMV3SpurionTextureFrontierStatus

    statusIsCorrectedFrontier :
      status
      ≡
      spurionTexture_rankOneResult_phenomenologyRequired

    bilinearTextureReceipt :
      Bilinear.DHRIntertwinerPSL2F7TextureReceipt

    bilinearTextureReceiptIsCanonical :
      bilinearTextureReceipt
      ≡ Bilinear.canonicalDHRIntertwinerPSL2F7TextureReceipt

    rankOneAnsatzReceipt :
      RankOne.PSL2F7RankOneYdTextureReceipt

    rankOneAnsatzReceiptIsCanonical :
      rankOneAnsatzReceipt
      ≡ RankOne.canonicalPSL2F7RankOneYdTextureReceipt

    tensorFacts :
      List PSL2F7TensorFact

    tensorFactsAreCanonical :
      tensorFacts ≡ canonicalPSL2F7TensorFacts

    bilinearInvariantMultiplicity :
      Nat

    bilinearInvariantMultiplicityIsZero :
      bilinearInvariantMultiplicity ≡ 0

    tripleV3InvariantMultiplicity :
      Nat

    tripleV3InvariantMultiplicityIsOne :
      tripleV3InvariantMultiplicity ≡ 1

    tripleV3InvariantVerified :
      Bool

    tripleV3InvariantVerifiedIsTrue :
      tripleV3InvariantVerified ≡ true

    symmetricCubeInvariantMultiplicity :
      Nat

    symmetricCubeInvariantMultiplicityIsZero :
      symmetricCubeInvariantMultiplicity ≡ 0

    exteriorCubeInvariantMultiplicity :
      Nat

    exteriorCubeInvariantMultiplicityIsOne :
      exteriorCubeInvariantMultiplicity ≡ 1

    tripleInvariantChannel :
      String

    tripleInvariantChannelIsExterior :
      tripleInvariantChannel ≡ "exterior determinant channel"

    pureV3SpurionGenericRank :
      Nat

    pureV3SpurionGenericRankIsTwo :
      pureV3SpurionGenericRank ≡ 2

    rankOneProjectorDerivedFromPSL2F7 :
      Bool

    rankOneProjectorDerivedFromPSL2F7IsFalse :
      rankOneProjectorDerivedFromPSL2F7 ≡ false

    rankOneTextureRequiresResidualSelector :
      Bool

    rankOneTextureRequiresResidualSelectorIsTrue :
      rankOneTextureRequiresResidualSelector ≡ true

    textureFrontierShapes :
      List TextureFrontierShape

    textureFrontierShapesAreCanonical :
      textureFrontierShapes ≡ canonicalTextureFrontierShapes

    proofObligations :
      List FrontierProofObligation

    proofObligationsAreCanonical :
      proofObligations ≡ canonicalFrontierProofObligations

    tripleInvariantSummary :
      String

    tripleInvariantSummaryIsCanonical :
      tripleInvariantSummary ≡ tripleInvariantStatement

    rankOneCorrectionSummary :
      String

    rankOneCorrectionSummaryIsCanonical :
      rankOneCorrectionSummary ≡ rankOneCorrectionStatement

    ydDerived :
      Bool

    ydDerivedIsFalse :
      ydDerived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    promotionFlags :
      List PromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ boundaryStatement

open CKMV3SpurionTextureFrontierReceipt public

canonicalCKMV3SpurionTextureFrontierReceipt :
  CKMV3SpurionTextureFrontierReceipt
canonicalCKMV3SpurionTextureFrontierReceipt =
  record
    { status =
        spurionTexture_rankOneResult_phenomenologyRequired
    ; statusIsCorrectedFrontier =
        refl
    ; bilinearTextureReceipt =
        Bilinear.canonicalDHRIntertwinerPSL2F7TextureReceipt
    ; bilinearTextureReceiptIsCanonical =
        refl
    ; rankOneAnsatzReceipt =
        RankOne.canonicalPSL2F7RankOneYdTextureReceipt
    ; rankOneAnsatzReceiptIsCanonical =
        refl
    ; tensorFacts =
        canonicalPSL2F7TensorFacts
    ; tensorFactsAreCanonical =
        refl
    ; bilinearInvariantMultiplicity =
        0
    ; bilinearInvariantMultiplicityIsZero =
        refl
    ; tripleV3InvariantMultiplicity =
        1
    ; tripleV3InvariantMultiplicityIsOne =
        refl
    ; tripleV3InvariantVerified =
        true
    ; tripleV3InvariantVerifiedIsTrue =
        refl
    ; symmetricCubeInvariantMultiplicity =
        0
    ; symmetricCubeInvariantMultiplicityIsZero =
        refl
    ; exteriorCubeInvariantMultiplicity =
        1
    ; exteriorCubeInvariantMultiplicityIsOne =
        refl
    ; tripleInvariantChannel =
        "exterior determinant channel"
    ; tripleInvariantChannelIsExterior =
        refl
    ; pureV3SpurionGenericRank =
        2
    ; pureV3SpurionGenericRankIsTwo =
        refl
    ; rankOneProjectorDerivedFromPSL2F7 =
        false
    ; rankOneProjectorDerivedFromPSL2F7IsFalse =
        refl
    ; rankOneTextureRequiresResidualSelector =
        true
    ; rankOneTextureRequiresResidualSelectorIsTrue =
        refl
    ; textureFrontierShapes =
        canonicalTextureFrontierShapes
    ; textureFrontierShapesAreCanonical =
        refl
    ; proofObligations =
        canonicalFrontierProofObligations
    ; proofObligationsAreCanonical =
        refl
    ; tripleInvariantSummary =
        tripleInvariantStatement
    ; tripleInvariantSummaryIsCanonical =
        refl
    ; rankOneCorrectionSummary =
        rankOneCorrectionStatement
    ; rankOneCorrectionSummaryIsCanonical =
        refl
    ; ydDerived =
        false
    ; ydDerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        boundaryStatement
    ; receiptBoundaryIsCanonical =
        refl
    }

ckmV3TripleInvariantVerified :
  tripleV3InvariantVerified canonicalCKMV3SpurionTextureFrontierReceipt
  ≡ true
ckmV3TripleInvariantVerified =
  refl

ckmV3RankOneProjectorNotForced :
  rankOneProjectorDerivedFromPSL2F7
    canonicalCKMV3SpurionTextureFrontierReceipt
  ≡ false
ckmV3RankOneProjectorNotForced =
  refl

ckmV3SpurionDoesNotPromoteCKM :
  physicalCKMPromoted canonicalCKMV3SpurionTextureFrontierReceipt
  ≡ false
ckmV3SpurionDoesNotPromoteCKM =
  refl
