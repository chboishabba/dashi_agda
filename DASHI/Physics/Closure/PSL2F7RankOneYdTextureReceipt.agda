module DASHI.Physics.Closure.PSL2F7RankOneYdTextureReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- B2: explicit residual-selector rank-1 3x3 down-type Yukawa texture receipt.
--
-- The texture is the one-parameter residual-projector ansatz:
--
--   Y_d(lambda) = [ 0 0 0
--                   0 0 0
--                   0 0 lambda ]
--
-- It records one free nonzero parameter lambda and no other entries.  This is
-- rank one only after adding a residual heavy-generation selector.  The
-- PSL(2,F7) character computation by itself supplies the alternating
-- determinant channel in V3 tensor V3 tensor V3; a pure V3 spurion gives a
-- generic antisymmetric rank-2 texture, not this rank-1 projector.

data TextureScalar : Set where
  zero :
    TextureScalar

  lambda :
    TextureScalar

data LambdaWitness : Set where
  lambdaIsSingleFreeNonzeroParameter :
    LambdaWitness

data GenerationIndex : Set where
  g1 :
    GenerationIndex

  g2 :
    GenerationIndex

  g3 :
    GenerationIndex

record Matrix3x3 : Set where
  field
    y11 : TextureScalar
    y12 : TextureScalar
    y13 : TextureScalar
    y21 : TextureScalar
    y22 : TextureScalar
    y23 : TextureScalar
    y31 : TextureScalar
    y32 : TextureScalar
    y33 : TextureScalar

open Matrix3x3 public

rankOneYdTextureMatrix :
  Matrix3x3
rankOneYdTextureMatrix =
  record
    { y11 = zero
    ; y12 = zero
    ; y13 = zero
    ; y21 = zero
    ; y22 = zero
    ; y23 = zero
    ; y31 = zero
    ; y32 = zero
    ; y33 = lambda
    }

ydEntry :
  Matrix3x3 →
  GenerationIndex →
  GenerationIndex →
  TextureScalar
ydEntry matrix g1 g1 = y11 matrix
ydEntry matrix g1 g2 = y12 matrix
ydEntry matrix g1 g3 = y13 matrix
ydEntry matrix g2 g1 = y21 matrix
ydEntry matrix g2 g2 = y22 matrix
ydEntry matrix g2 g3 = y23 matrix
ydEntry matrix g3 g1 = y31 matrix
ydEntry matrix g3 g2 = y32 matrix
ydEntry matrix g3 g3 = y33 matrix

data PSL2F7TextureConstraint : Set where
  V3GenerationAssignment :
    PSL2F7TextureConstraint

  fullPSL2F7BilinearV3V3HasNoTrivialInvariant :
    PSL2F7TextureConstraint

  singleV3SpurionSuppliesOneTrivialInvariant :
    PSL2F7TextureConstraint

  V3TripleInvariantIsExteriorDeterminant :
    PSL2F7TextureConstraint

  pureV3SpurionGivesAntisymmetricRankTwoGenericTexture :
    PSL2F7TextureConstraint

  residualStructureSelectsHeavyGenerationProjector :
    PSL2F7TextureConstraint

  allLightAndOffDiagonalEntriesForbiddenAtLeadingOrder :
    PSL2F7TextureConstraint

canonicalPSL2F7TextureConstraints :
  List PSL2F7TextureConstraint
canonicalPSL2F7TextureConstraints =
  V3GenerationAssignment
  ∷ fullPSL2F7BilinearV3V3HasNoTrivialInvariant
  ∷ singleV3SpurionSuppliesOneTrivialInvariant
  ∷ V3TripleInvariantIsExteriorDeterminant
  ∷ pureV3SpurionGivesAntisymmetricRankTwoGenericTexture
  ∷ residualStructureSelectsHeavyGenerationProjector
  ∷ allLightAndOffDiagonalEntriesForbiddenAtLeadingOrder
  ∷ []

data PhenomenologyRequirement : Set where
  downMassRequiresAdditionalBreaking :
    PhenomenologyRequirement

  strangeMassRequiresAdditionalBreaking :
    PhenomenologyRequirement

  CKMMixingRequiresOffDiagonalPerturbations :
    PhenomenologyRequirement

  CPPhaseRequiresAdditionalComplexPerturbation :
    PhenomenologyRequirement

canonicalPhenomenologyRequirements :
  List PhenomenologyRequirement
canonicalPhenomenologyRequirements =
  downMassRequiresAdditionalBreaking
  ∷ strangeMassRequiresAdditionalBreaking
  ∷ CKMMixingRequiresOffDiagonalPerturbations
  ∷ CPPhaseRequiresAdditionalComplexPerturbation
  ∷ []

data YdTexturePromotion : Set where

ydTexturePromotionImpossibleHere :
  YdTexturePromotion →
  ⊥
ydTexturePromotionImpossibleHere ()

textureFormulaStatement :
  String
textureFormulaStatement =
  "Y_d(lambda) is the explicit 3x3 matrix [[0,0,0],[0,0,0],[0,0,lambda]]."

rankOneStatement :
  String
rankOneStatement =
  "For nonzero lambda this residual-selector ansatz is rank one: only the heavy-generation projector is open."

PSL2F7CaveatStatement :
  String
PSL2F7CaveatStatement =
  "PSL2F7 does not force this rank-1 matrix: V3^3 has one invariant in the exterior determinant channel, and a pure V3 spurion gives a generic antisymmetric rank-2 texture."

phenomenologyBoundaryStatement :
  String
phenomenologyBoundaryStatement =
  "The rank-1 texture is not phenomenologically complete; down/strange masses, CKM mixing, and CP phase require additional breaking or perturbations."

record PSL2F7RankOneYdTextureReceipt : Set where
  field
    textureMatrix :
      Matrix3x3

    textureMatrixIsCanonical :
      textureMatrix ≡ rankOneYdTextureMatrix

    freeParameter :
      TextureScalar

    freeParameterIsLambda :
      freeParameter ≡ lambda

    lambdaWitness :
      LambdaWitness

    lambdaWitnessIsSingleFreeNonzeroParameter :
      lambdaWitness ≡ lambdaIsSingleFreeNonzeroParameter

    numberOfFreeParameters :
      Nat

    numberOfFreeParametersIsOne :
      numberOfFreeParameters ≡ 1

    fullPSL2F7BilinearInvariantMultiplicity :
      Nat

    fullPSL2F7BilinearInvariantMultiplicityIsZero :
      fullPSL2F7BilinearInvariantMultiplicity ≡ 0

    V3SpurionInvariantMultiplicity :
      Nat

    V3SpurionInvariantMultiplicityIsOne :
      V3SpurionInvariantMultiplicity ≡ 1

    V3TripleInvariantChannel :
      String

    V3TripleInvariantChannelIsExterior :
      V3TripleInvariantChannel ≡ "exterior determinant channel"

    symmetricCubeInvariantMultiplicity :
      Nat

    symmetricCubeInvariantMultiplicityIsZero :
      symmetricCubeInvariantMultiplicity ≡ 0

    exteriorCubeInvariantMultiplicity :
      Nat

    exteriorCubeInvariantMultiplicityIsOne :
      exteriorCubeInvariantMultiplicity ≡ 1

    pureV3SpurionGenericTextureRank :
      Nat

    pureV3SpurionGenericTextureRankIsTwo :
      pureV3SpurionGenericTextureRank ≡ 2

    rankOneProjectorDerivedFromPSL2F7 :
      Bool

    rankOneProjectorDerivedFromPSL2F7IsFalse :
      rankOneProjectorDerivedFromPSL2F7 ≡ false

    rankOneTextureRequiresResidualSelector :
      Bool

    rankOneTextureRequiresResidualSelectorIsTrue :
      rankOneTextureRequiresResidualSelector ≡ true

    residualHeavyGenerationProjectorAssumed :
      Bool

    residualHeavyGenerationProjectorAssumedIsTrue :
      residualHeavyGenerationProjectorAssumed ≡ true

    constraints :
      List PSL2F7TextureConstraint

    constraintsAreCanonical :
      constraints ≡ canonicalPSL2F7TextureConstraints

    y11IsZero :
      ydEntry textureMatrix g1 g1 ≡ zero

    y12IsZero :
      ydEntry textureMatrix g1 g2 ≡ zero

    y13IsZero :
      ydEntry textureMatrix g1 g3 ≡ zero

    y21IsZero :
      ydEntry textureMatrix g2 g1 ≡ zero

    y22IsZero :
      ydEntry textureMatrix g2 g2 ≡ zero

    y23IsZero :
      ydEntry textureMatrix g2 g3 ≡ zero

    y31IsZero :
      ydEntry textureMatrix g3 g1 ≡ zero

    y32IsZero :
      ydEntry textureMatrix g3 g2 ≡ zero

    y33IsLambda :
      ydEntry textureMatrix g3 g3 ≡ lambda

    rank :
      Nat

    rankIsOne :
      rank ≡ 1

    textureIsRankOne :
      Bool

    textureIsRankOneIsTrue :
      textureIsRankOne ≡ true

    textureFormula :
      String

    textureFormulaIsCanonical :
      textureFormula ≡ textureFormulaStatement

    rankStatementSummary :
      String

    rankStatementSummaryIsCanonical :
      rankStatementSummary ≡ rankOneStatement

    PSL2F7CaveatSummary :
      String

    PSL2F7CaveatSummaryIsCanonical :
      PSL2F7CaveatSummary ≡ PSL2F7CaveatStatement

    phenomenologyComplete :
      Bool

    phenomenologyCompleteIsFalse :
      phenomenologyComplete ≡ false

    requiredPerturbations :
      List PhenomenologyRequirement

    requiredPerturbationsAreCanonical :
      requiredPerturbations ≡ canonicalPhenomenologyRequirements

    phenomenologyBoundary :
      String

    phenomenologyBoundaryIsCanonical :
      phenomenologyBoundary ≡ phenomenologyBoundaryStatement

    physicalYukawaPromoted :
      Bool

    physicalYukawaPromotedIsFalse :
      physicalYukawaPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    promotionFlags :
      List YdTexturePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open PSL2F7RankOneYdTextureReceipt public

canonicalPSL2F7RankOneYdTextureReceipt :
  PSL2F7RankOneYdTextureReceipt
canonicalPSL2F7RankOneYdTextureReceipt =
  record
    { textureMatrix =
        rankOneYdTextureMatrix
    ; textureMatrixIsCanonical =
        refl
    ; freeParameter =
        lambda
    ; freeParameterIsLambda =
        refl
    ; lambdaWitness =
        lambdaIsSingleFreeNonzeroParameter
    ; lambdaWitnessIsSingleFreeNonzeroParameter =
        refl
    ; numberOfFreeParameters =
        1
    ; numberOfFreeParametersIsOne =
        refl
    ; fullPSL2F7BilinearInvariantMultiplicity =
        0
    ; fullPSL2F7BilinearInvariantMultiplicityIsZero =
        refl
    ; V3SpurionInvariantMultiplicity =
        1
    ; V3SpurionInvariantMultiplicityIsOne =
        refl
    ; V3TripleInvariantChannel =
        "exterior determinant channel"
    ; V3TripleInvariantChannelIsExterior =
        refl
    ; symmetricCubeInvariantMultiplicity =
        0
    ; symmetricCubeInvariantMultiplicityIsZero =
        refl
    ; exteriorCubeInvariantMultiplicity =
        1
    ; exteriorCubeInvariantMultiplicityIsOne =
        refl
    ; pureV3SpurionGenericTextureRank =
        2
    ; pureV3SpurionGenericTextureRankIsTwo =
        refl
    ; rankOneProjectorDerivedFromPSL2F7 =
        false
    ; rankOneProjectorDerivedFromPSL2F7IsFalse =
        refl
    ; rankOneTextureRequiresResidualSelector =
        true
    ; rankOneTextureRequiresResidualSelectorIsTrue =
        refl
    ; residualHeavyGenerationProjectorAssumed =
        true
    ; residualHeavyGenerationProjectorAssumedIsTrue =
        refl
    ; constraints =
        canonicalPSL2F7TextureConstraints
    ; constraintsAreCanonical =
        refl
    ; y11IsZero =
        refl
    ; y12IsZero =
        refl
    ; y13IsZero =
        refl
    ; y21IsZero =
        refl
    ; y22IsZero =
        refl
    ; y23IsZero =
        refl
    ; y31IsZero =
        refl
    ; y32IsZero =
        refl
    ; y33IsLambda =
        refl
    ; rank =
        1
    ; rankIsOne =
        refl
    ; textureIsRankOne =
        true
    ; textureIsRankOneIsTrue =
        refl
    ; textureFormula =
        textureFormulaStatement
    ; textureFormulaIsCanonical =
        refl
    ; rankStatementSummary =
        rankOneStatement
    ; rankStatementSummaryIsCanonical =
        refl
    ; PSL2F7CaveatSummary =
        PSL2F7CaveatStatement
    ; PSL2F7CaveatSummaryIsCanonical =
        refl
    ; phenomenologyComplete =
        false
    ; phenomenologyCompleteIsFalse =
        refl
    ; requiredPerturbations =
        canonicalPhenomenologyRequirements
    ; requiredPerturbationsAreCanonical =
        refl
    ; phenomenologyBoundary =
        phenomenologyBoundaryStatement
    ; phenomenologyBoundaryIsCanonical =
        refl
    ; physicalYukawaPromoted =
        false
    ; physicalYukawaPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

rankOneYdTextureHasOneFreeParameter :
  numberOfFreeParameters canonicalPSL2F7RankOneYdTextureReceipt ≡ 1
rankOneYdTextureHasOneFreeParameter =
  refl

rankOneYdTextureOnlyHasHeavyEntry :
  ydEntry
    (textureMatrix canonicalPSL2F7RankOneYdTextureReceipt)
    g3
    g3
  ≡ lambda
rankOneYdTextureOnlyHasHeavyEntry =
  refl

rankOneYdTextureRankIsOne :
  rank canonicalPSL2F7RankOneYdTextureReceipt ≡ 1
rankOneYdTextureRankIsOne =
  refl

rankOneProjectorNotForcedByPSL2F7 :
  rankOneProjectorDerivedFromPSL2F7
    canonicalPSL2F7RankOneYdTextureReceipt
  ≡ false
rankOneProjectorNotForcedByPSL2F7 =
  refl

rankOneYdTexturePhenomenologyRequiresPerturbations :
  phenomenologyComplete canonicalPSL2F7RankOneYdTextureReceipt ≡ false
rankOneYdTexturePhenomenologyRequiresPerturbations =
  refl

rankOneYdTextureDoesNotPromoteCKM :
  physicalCKMPromoted canonicalPSL2F7RankOneYdTextureReceipt ≡ false
rankOneYdTextureDoesNotPromoteCKM =
  refl

rankOneYdTextureNoPromotion :
  YdTexturePromotion →
  ⊥
rankOneYdTextureNoPromotion =
  ydTexturePromotionImpossibleHere
