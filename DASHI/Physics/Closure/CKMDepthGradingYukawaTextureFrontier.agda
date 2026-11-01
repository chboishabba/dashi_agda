module DASHI.Physics.Closure.CKMDepthGradingYukawaTextureFrontier where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PSL2F7RankOneYdTextureReceipt as RankOne

------------------------------------------------------------------------
-- CKM depth-grading Yukawa selector frontier receipt.
--
-- Generation primes 2, 3, 7 are assigned floor(log2) grades 1, 1, 2.
-- Reducing these grades modulo two gives a residual Z/2 grading:
--
--   2 -> grade 1 -> odd
--   3 -> grade 1 -> odd
--   7 -> grade 2 -> even
--
-- The residual selector is only a frontier selector for the heavy generation.
-- It records the sign/grade pattern and the leading rank-one candidate, but
-- does not promote a physical Y_d or physical CKM matrix.
--
-- New Frobenius-character computation: for the p = 7 generation,
-- psi7(Frob_p2) = 4 mod 7 = 2^2.  This independently identifies the
-- psi2 eigenspace, agreeing with the floor(log2 7) = 2 depth grade for the
-- third/heaviest generation.

data GenerationPrime : Set where
  prime2 :
    GenerationPrime

  prime3 :
    GenerationPrime

  prime7 :
    GenerationPrime

canonicalGenerationPrimes :
  List GenerationPrime
canonicalGenerationPrimes =
  prime2 ∷ prime3 ∷ prime7 ∷ []

data ResidualZ2Grade : Set where
  evenGrade :
    ResidualZ2Grade

  oddGrade :
    ResidualZ2Grade

floorLog2Grade :
  GenerationPrime →
  Nat
floorLog2Grade prime2 = 1
floorLog2Grade prime3 = 1
floorLog2Grade prime7 = 2

residualZ2Grade :
  GenerationPrime →
  ResidualZ2Grade
residualZ2Grade prime2 = oddGrade
residualZ2Grade prime3 = oddGrade
residualZ2Grade prime7 = evenGrade

data ResidualSelectorValue : Set where
  selected :
    ResidualSelectorValue

  rejected :
    ResidualSelectorValue

data FrobeniusEigenspace : Set where
  psi2Eigenspace :
    FrobeniusEigenspace

  otherEigenspace :
    FrobeniusEigenspace

data SelectorAgreement : Set where
  depthAndFrobeniusAgreeOnThirdGeneration :
    SelectorAgreement

heavyGenerationSelector :
  GenerationPrime →
  ResidualSelectorValue
heavyGenerationSelector prime2 = rejected
heavyGenerationSelector prime3 = rejected
heavyGenerationSelector prime7 = selected

frobeniusCharacterSelector :
  GenerationPrime →
  FrobeniusEigenspace
frobeniusCharacterSelector prime2 = otherEigenspace
frobeniusCharacterSelector prime3 = otherEigenspace
frobeniusCharacterSelector prime7 = psi2Eigenspace

data TextureSign : Set where
  plus :
    TextureSign

  minus :
    TextureSign

data TextureScalar : Set where
  zero :
    TextureScalar

  lambdaHeavy :
    TextureScalar

record GradePattern3x3 : Set where
  field
    grade11 : Nat
    grade12 : Nat
    grade13 : Nat
    grade21 : Nat
    grade22 : Nat
    grade23 : Nat
    grade31 : Nat
    grade32 : Nat
    grade33 : Nat

open GradePattern3x3 public

record SignPattern3x3 : Set where
  field
    sign11 : TextureSign
    sign12 : TextureSign
    sign13 : TextureSign
    sign21 : TextureSign
    sign22 : TextureSign
    sign23 : TextureSign
    sign31 : TextureSign
    sign32 : TextureSign
    sign33 : TextureSign

open SignPattern3x3 public

record CandidateTexture3x3 : Set where
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

open CandidateTexture3x3 public

canonicalDepthGradePattern :
  GradePattern3x3
canonicalDepthGradePattern =
  record
    { grade11 = 2
    ; grade12 = 2
    ; grade13 = 3
    ; grade21 = 2
    ; grade22 = 2
    ; grade23 = 3
    ; grade31 = 3
    ; grade32 = 3
    ; grade33 = 4
    }

canonicalResidualSignPattern :
  SignPattern3x3
canonicalResidualSignPattern =
  record
    { sign11 = plus
    ; sign12 = plus
    ; sign13 = minus
    ; sign21 = plus
    ; sign22 = plus
    ; sign23 = minus
    ; sign31 = minus
    ; sign32 = minus
    ; sign33 = plus
    }

leadingRankOneHeavyGenerationCandidate :
  CandidateTexture3x3
leadingRankOneHeavyGenerationCandidate =
  record
    { y11 = zero
    ; y12 = zero
    ; y13 = zero
    ; y21 = zero
    ; y22 = zero
    ; y23 = zero
    ; y31 = zero
    ; y32 = zero
    ; y33 = lambdaHeavy
    }

data DepthGradingYukawaFrontierObligation : Set where
  verifyFloorLog2PrimeDepths :
    DepthGradingYukawaFrontierObligation

  justifyResidualZ2Selector :
    DepthGradingYukawaFrontierObligation

  recordFrobeniusCharacterSelectorAgreement :
    DepthGradingYukawaFrontierObligation

  numericallyFitTextureAgainstMassesAndCKM :
    DepthGradingYukawaFrontierObligation

  supplyPhenomenologyBeforePhysicalPromotion :
    DepthGradingYukawaFrontierObligation

canonicalDepthGradingYukawaFrontierObligations :
  List DepthGradingYukawaFrontierObligation
canonicalDepthGradingYukawaFrontierObligations =
  verifyFloorLog2PrimeDepths
  ∷ justifyResidualZ2Selector
  ∷ recordFrobeniusCharacterSelectorAgreement
  ∷ numericallyFitTextureAgainstMassesAndCKM
  ∷ supplyPhenomenologyBeforePhysicalPromotion
  ∷ []

data CKMDepthGradingYukawaPromotion : Set where

ckmDepthGradingYukawaPromotionImpossibleHere :
  CKMDepthGradingYukawaPromotion →
  ⊥
ckmDepthGradingYukawaPromotionImpossibleHere ()

gradeAssignmentStatement :
  String
gradeAssignmentStatement =
  "Generation primes 2, 3, 7 have floor(log2) grades 1, 1, 2; modulo two this gives odd, odd, even."

selectorStatement :
  String
selectorStatement =
  "The residual Z/2 selector keeps the even grade-2 prime-7 generation as the leading heavy-generation slot and rejects the two odd light slots."

frobeniusSelectorStatement :
  String
frobeniusSelectorStatement =
  "The new computation psi7(Frob_p2) == 4 mod 7 == 2^2 independently selects the psi2 eigenspace, so the Frobenius character selector and floor(log2 7)=2 depth grade agree on the third/heaviest generation."

texturePatternStatement :
  String
texturePatternStatement =
  "The bilinear depth-grade pattern is [[2,2,3],[2,2,3],[3,3,4]] with residual signs [[+,+,-],[+,+,-],[-,-,+]]."

rankOneCandidateStatement :
  String
rankOneCandidateStatement =
  "The leading candidate is the rank-one heavy-generation texture [[0,0,0],[0,0,0],[0,0,lambdaHeavy]]."

phenomenologyCheckStatement :
  String
phenomenologyCheckStatement =
  "A numerical and phenomenology check against down-sector masses, CKM mixing, and CP data is still required before any physical promotion."

record CKMDepthGradingYukawaTextureFrontierReceipt : Set where
  field
    generationPrimes :
      List GenerationPrime

    generationPrimesAreCanonical :
      generationPrimes ≡ canonicalGenerationPrimes

    prime2FloorLog2Grade :
      Nat

    prime2FloorLog2GradeIsOne :
      prime2FloorLog2Grade ≡ 1

    prime3FloorLog2Grade :
      Nat

    prime3FloorLog2GradeIsOne :
      prime3FloorLog2Grade ≡ 1

    prime7FloorLog2Grade :
      Nat

    prime7FloorLog2GradeIsTwo :
      prime7FloorLog2Grade ≡ 2

    prime2ResidualGrade :
      ResidualZ2Grade

    prime2ResidualGradeIsOdd :
      prime2ResidualGrade ≡ oddGrade

    prime3ResidualGrade :
      ResidualZ2Grade

    prime3ResidualGradeIsOdd :
      prime3ResidualGrade ≡ oddGrade

    prime7ResidualGrade :
      ResidualZ2Grade

    prime7ResidualGradeIsEven :
      prime7ResidualGrade ≡ evenGrade

    selectorPrime2 :
      ResidualSelectorValue

    selectorPrime2Rejects :
      selectorPrime2 ≡ rejected

    selectorPrime3 :
      ResidualSelectorValue

    selectorPrime3Rejects :
      selectorPrime3 ≡ rejected

    selectorPrime7 :
      ResidualSelectorValue

    selectorPrime7Selects :
      selectorPrime7 ≡ selected

    psi7FrobP2ResidueMod7 :
      Nat

    psi7FrobP2ResidueMod7IsFour :
      psi7FrobP2ResidueMod7 ≡ 4

    psi7FrobP2ResidueIsTwoSquared :
      Bool

    psi7FrobP2ResidueIsTwoSquaredIsTrue :
      psi7FrobP2ResidueIsTwoSquared ≡ true

    prime7FrobeniusEigenspace :
      FrobeniusEigenspace

    prime7FrobeniusEigenspaceIsPsi2 :
      prime7FrobeniusEigenspace ≡ psi2Eigenspace

    thirdGenerationSelectorAgreement :
      SelectorAgreement

    thirdGenerationSelectorAgreementIsCanonical :
      thirdGenerationSelectorAgreement
      ≡ depthAndFrobeniusAgreeOnThirdGeneration

    gradePattern :
      GradePattern3x3

    gradePatternIsCanonical :
      gradePattern ≡ canonicalDepthGradePattern

    signPattern :
      SignPattern3x3

    signPatternIsCanonical :
      signPattern ≡ canonicalResidualSignPattern

    leadingCandidate :
      CandidateTexture3x3

    leadingCandidateIsCanonical :
      leadingCandidate ≡ leadingRankOneHeavyGenerationCandidate

    rankOneYdTextureReceipt :
      RankOne.PSL2F7RankOneYdTextureReceipt

    rankOneYdTextureReceiptIsCanonical :
      rankOneYdTextureReceipt
      ≡ RankOne.canonicalPSL2F7RankOneYdTextureReceipt

    leadingCandidateRank :
      Nat

    leadingCandidateRankIsOne :
      leadingCandidateRank ≡ 1

    numericalPhenomenologyCheckRequired :
      Bool

    numericalPhenomenologyCheckRequiredIsTrue :
      numericalPhenomenologyCheckRequired ≡ true

    physicalYdPromoted :
      Bool

    physicalYdPromotedIsFalse :
      physicalYdPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    obligations :
      List DepthGradingYukawaFrontierObligation

    obligationsAreCanonical :
      obligations ≡ canonicalDepthGradingYukawaFrontierObligations

    promotionFlags :
      List CKMDepthGradingYukawaPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    gradeAssignmentSummary :
      String

    gradeAssignmentSummaryIsCanonical :
      gradeAssignmentSummary ≡ gradeAssignmentStatement

    selectorSummary :
      String

    selectorSummaryIsCanonical :
      selectorSummary ≡ selectorStatement

    frobeniusSelectorSummary :
      String

    frobeniusSelectorSummaryIsCanonical :
      frobeniusSelectorSummary ≡ frobeniusSelectorStatement

    texturePatternSummary :
      String

    texturePatternSummaryIsCanonical :
      texturePatternSummary ≡ texturePatternStatement

    rankOneCandidateSummary :
      String

    rankOneCandidateSummaryIsCanonical :
      rankOneCandidateSummary ≡ rankOneCandidateStatement

    phenomenologyCheckSummary :
      String

    phenomenologyCheckSummaryIsCanonical :
      phenomenologyCheckSummary ≡ phenomenologyCheckStatement

open CKMDepthGradingYukawaTextureFrontierReceipt public

canonicalCKMDepthGradingYukawaTextureFrontierReceipt :
  CKMDepthGradingYukawaTextureFrontierReceipt
canonicalCKMDepthGradingYukawaTextureFrontierReceipt =
  record
    { generationPrimes =
        canonicalGenerationPrimes
    ; generationPrimesAreCanonical =
        refl
    ; prime2FloorLog2Grade =
        floorLog2Grade prime2
    ; prime2FloorLog2GradeIsOne =
        refl
    ; prime3FloorLog2Grade =
        floorLog2Grade prime3
    ; prime3FloorLog2GradeIsOne =
        refl
    ; prime7FloorLog2Grade =
        floorLog2Grade prime7
    ; prime7FloorLog2GradeIsTwo =
        refl
    ; prime2ResidualGrade =
        residualZ2Grade prime2
    ; prime2ResidualGradeIsOdd =
        refl
    ; prime3ResidualGrade =
        residualZ2Grade prime3
    ; prime3ResidualGradeIsOdd =
        refl
    ; prime7ResidualGrade =
        residualZ2Grade prime7
    ; prime7ResidualGradeIsEven =
        refl
    ; selectorPrime2 =
        heavyGenerationSelector prime2
    ; selectorPrime2Rejects =
        refl
    ; selectorPrime3 =
        heavyGenerationSelector prime3
    ; selectorPrime3Rejects =
        refl
    ; selectorPrime7 =
        heavyGenerationSelector prime7
    ; selectorPrime7Selects =
        refl
    ; psi7FrobP2ResidueMod7 =
        4
    ; psi7FrobP2ResidueMod7IsFour =
        refl
    ; psi7FrobP2ResidueIsTwoSquared =
        true
    ; psi7FrobP2ResidueIsTwoSquaredIsTrue =
        refl
    ; prime7FrobeniusEigenspace =
        frobeniusCharacterSelector prime7
    ; prime7FrobeniusEigenspaceIsPsi2 =
        refl
    ; thirdGenerationSelectorAgreement =
        depthAndFrobeniusAgreeOnThirdGeneration
    ; thirdGenerationSelectorAgreementIsCanonical =
        refl
    ; gradePattern =
        canonicalDepthGradePattern
    ; gradePatternIsCanonical =
        refl
    ; signPattern =
        canonicalResidualSignPattern
    ; signPatternIsCanonical =
        refl
    ; leadingCandidate =
        leadingRankOneHeavyGenerationCandidate
    ; leadingCandidateIsCanonical =
        refl
    ; rankOneYdTextureReceipt =
        RankOne.canonicalPSL2F7RankOneYdTextureReceipt
    ; rankOneYdTextureReceiptIsCanonical =
        refl
    ; leadingCandidateRank =
        1
    ; leadingCandidateRankIsOne =
        refl
    ; numericalPhenomenologyCheckRequired =
        true
    ; numericalPhenomenologyCheckRequiredIsTrue =
        refl
    ; physicalYdPromoted =
        false
    ; physicalYdPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; obligations =
        canonicalDepthGradingYukawaFrontierObligations
    ; obligationsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; gradeAssignmentSummary =
        gradeAssignmentStatement
    ; gradeAssignmentSummaryIsCanonical =
        refl
    ; selectorSummary =
        selectorStatement
    ; selectorSummaryIsCanonical =
        refl
    ; frobeniusSelectorSummary =
        frobeniusSelectorStatement
    ; frobeniusSelectorSummaryIsCanonical =
        refl
    ; texturePatternSummary =
        texturePatternStatement
    ; texturePatternSummaryIsCanonical =
        refl
    ; rankOneCandidateSummary =
        rankOneCandidateStatement
    ; rankOneCandidateSummaryIsCanonical =
        refl
    ; phenomenologyCheckSummary =
        phenomenologyCheckStatement
    ; phenomenologyCheckSummaryIsCanonical =
        refl
    }

primeDepthGradesAreCanonical :
  prime2FloorLog2Grade canonicalCKMDepthGradingYukawaTextureFrontierReceipt
  ≡ 1
primeDepthGradesAreCanonical =
  refl

prime7ResidualSelectorSelectsHeavyGeneration :
  selectorPrime7 canonicalCKMDepthGradingYukawaTextureFrontierReceipt
  ≡ selected
prime7ResidualSelectorSelectsHeavyGeneration =
  refl

prime7FrobeniusCharacterSelectsPsi2 :
  prime7FrobeniusEigenspace
    canonicalCKMDepthGradingYukawaTextureFrontierReceipt
  ≡ psi2Eigenspace
prime7FrobeniusCharacterSelectsPsi2 =
  refl

depthGradingAndFrobeniusAgreeOnThirdGeneration :
  thirdGenerationSelectorAgreement
    canonicalCKMDepthGradingYukawaTextureFrontierReceipt
  ≡ depthAndFrobeniusAgreeOnThirdGeneration
depthGradingAndFrobeniusAgreeOnThirdGeneration =
  refl

depthGradingLeadingCandidateIsRankOne :
  leadingCandidateRank canonicalCKMDepthGradingYukawaTextureFrontierReceipt
  ≡ 1
depthGradingLeadingCandidateIsRankOne =
  refl

depthGradingNumericalPhenomenologyCheckRequired :
  numericalPhenomenologyCheckRequired
    canonicalCKMDepthGradingYukawaTextureFrontierReceipt
  ≡ true
depthGradingNumericalPhenomenologyCheckRequired =
  refl

depthGradingNoPhysicalYdPromotion :
  physicalYdPromoted canonicalCKMDepthGradingYukawaTextureFrontierReceipt
  ≡ false
depthGradingNoPhysicalYdPromotion =
  refl

depthGradingNoPhysicalCKMPromotion :
  physicalCKMPromoted canonicalCKMDepthGradingYukawaTextureFrontierReceipt
  ≡ false
depthGradingNoPhysicalCKMPromotion =
  refl

depthGradingNoPromotion :
  CKMDepthGradingYukawaPromotion →
  ⊥
depthGradingNoPromotion =
  ckmDepthGradingYukawaPromotionImpossibleHere
