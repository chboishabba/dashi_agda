module DASHI.Foundations.TernaryGolay.CodeBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)

open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)
open import DASHI.Foundations.SSPTritCarrier using
  ( SSPTrit ; sspNegOne ; sspZero ; sspPosOne ; toTriTruth )
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Ternary Golay theorem boundary.
--
-- The standard parameters are recorded exactly, but an actual code theorem
-- requires an explicit generator/check matrix and proof receipts.  A citation
-- or parameter tuple alone does not become a machine-checked code.
------------------------------------------------------------------------

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

threePowerSix : pow 3 6 ≡ 729
threePowerSix = refl

record Vec6 (A : Set) : Set where
  constructor vec6
  field
    c0 c1 c2 c3 c4 c5 : A

record Vec11 (A : Set) : Set where
  constructor vec11
  field
    d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 : A

record Vec12 (A : Set) : Set where
  constructor vec12
  field
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : A

Message6 : Set
Message6 = Vec6 TriTruth

Word11 : Set
Word11 = Vec11 TriTruth

Word12 : Set
Word12 = Vec12 TriTruth

triToBalancedTrit : TriTruth → SSPTrit
triToBalancedTrit tri-low = sspZero
triToBalancedTrit tri-mid = sspPosOne
triToBalancedTrit tri-high = sspNegOne

balancedTritRoundTrip :
  (x : TriTruth) → toTriTruth (triToBalancedTrit x) ≡ x
balancedTritRoundTrip tri-low = refl
balancedTritRoundTrip tri-mid = refl
balancedTritRoundTrip tri-high = refl

record LinearTernaryCode12 : Set₁ where
  field
    encode : Message6 → Word12
    zeroMessage : Message6
    addMessage : Message6 → Message6 → Message6
    zeroWord : Word12
    addWord : Word12 → Word12 → Word12
    encodeZero : encode zeroMessage ≡ zeroWord
    encodeAdd :
      (left right : Message6) →
      encode (addMessage left right)
      ≡ addWord (encode left) (encode right)

open LinearTernaryCode12 public

record ExtendedTernaryGolayCertificate
    (code : LinearTernaryCode12) : Set₁ where
  field
    InjectiveEncoding : Set
    injectiveEncoding : InjectiveEncoding
    Exactly729Codewords : Set
    exactly729Codewords : Exactly729Codewords
    SelfOrthogonal : Set
    selfOrthogonal : SelfOrthogonal
    SelfDual : Set
    selfDual : SelfDual
    MinimumHammingWeightSix : Set
    minimumHammingWeightSix : MinimumHammingWeightSix
    WeightSixSupportsFormSmallWittDesign : Set
    weightSixSupportsFormSmallWittDesign :
      WeightSixSupportsFormSmallWittDesign

open ExtendedTernaryGolayCertificate public

record PunctureExtensionCertificate
    (extended : LinearTernaryCode12) : Set₁ where
  field
    puncture : Word12 → Word11
    extend : Word11 → Word12
    PuncturedImageIsTernaryGolay11 : Set
    puncturedImageIsTernaryGolay11 :
      PuncturedImageIsTernaryGolay11
    PuncturedMinimumDistanceFive : Set
    puncturedMinimumDistanceFive : PuncturedMinimumDistanceFive
    PerfectTwoErrorCorrection : Set
    perfectTwoErrorCorrection : PerfectTwoErrorCorrection
    ExtensionRecoversExtendedCode : Set
    extensionRecoversExtendedCode : ExtensionRecoversExtendedCode

open PunctureExtensionCertificate public

record MathieuActionCertificate
    (code : LinearTernaryCode12) : Set₁ where
  field
    M12 : Set
    MonomialAutomorphismGroup : Set
    actsOnCoordinates : M12 → Word12 → Word12
    preservesCode : Set
    preservesCodeWitness : preservesCode
    kernelOrder : Nat
    kernelOrderIsTwo : kernelOrder ≡ 2
    quotientIsM12 : Set
    quotientIsM12Witness : quotientIsM12

open MathieuActionCertificate public

record TernaryGolayParameterReceipt : Set where
  constructor ternaryGolayParameterReceipt
  field
    alphabetCardinality : Nat
    length : Nat
    dimension : Nat
    minimumDistance : Nat
    codewordCount : Nat
    alphabetCardinalityIsThree : alphabetCardinality ≡ 3
    lengthIsTwelve : length ≡ 12
    dimensionIsSix : dimension ≡ 6
    minimumDistanceIsSix : minimumDistance ≡ 6
    codewordCountIs729 : codewordCount ≡ 729
    codewordCountIsThreePowerSix : pow 3 6 ≡ codewordCount
    actualGeneratorMatrixSuppliedHere : Bool
    actualGeneratorMatrixSuppliedHereIsFalse :
      actualGeneratorMatrixSuppliedHere ≡ false
    minimumDistanceMachineCheckedHere : Bool
    minimumDistanceMachineCheckedHereIsFalse :
      minimumDistanceMachineCheckedHere ≡ false
    theoremImportRequired : Bool
    theoremImportRequiredIsTrue : theoremImportRequired ≡ true
    sourceTitle : String
    sourceAuthor : String

open TernaryGolayParameterReceipt public

canonicalTernaryGolayParameters : TernaryGolayParameterReceipt
canonicalTernaryGolayParameters =
  ternaryGolayParameterReceipt
    3 12 6 6 729
    refl refl refl refl refl
    threePowerSix
    false refl
    false refl
    true refl
    (Sources.title Sources.macWilliamsSloaneEntry)
    (Sources.author Sources.macWilliamsSloaneEntry)

record SixRoleSeparation : Set where
  constructor sixRoleSeparation
  field
    informationDimensionIsSix : Bool
    informationDimensionIsSixIsTrue : informationDimensionIsSix ≡ true
    minimumDistanceIsSix : Bool
    minimumDistanceIsSixIsTrue : minimumDistanceIsSix ≡ true
    smallWittBlockSizeIsSix : Bool
    smallWittBlockSizeIsSixIsTrue : smallWittBlockSizeIsSix ≡ true
    sixIsOneHexTruthCoefficient : Bool
    sixIsOneHexTruthCoefficientIsFalse :
      sixIsOneHexTruthCoefficient ≡ false
    correctInformationCarrierReading : String

canonicalSixRoleSeparation : SixRoleSeparation
canonicalSixRoleSeparation =
  sixRoleSeparation
    true refl
    true refl
    true refl
    false refl
    "the information carrier is TriTruth^6; HexTruth may index six positions but is not the six-dimensional vector space"

ternaryGolayBoundaryReceipt : GenericReceipt.GenericReceipt
ternaryGolayBoundaryReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "ternary Golay code boundary"
    "DASHI.Foundations.TernaryGolay.CodeBoundary"
    "canonicalTernaryGolayParameters"
    "the [12,6,6]_3 parameter surface, 729 count, balanced-trit bridge, puncture/extension obligations, and M12 action interface are attached"
    "generator matrix, self-duality, minimum distance, perfect decoding, Witt design, and automorphism theorems still require explicit proof terms"
    "agda -i . DASHI/Foundations/TernaryGolay/CodeBoundary.agda"

ternaryGolayBoundaryReceiptNonPromoting :
  GenericReceipt.promotesClaim ternaryGolayBoundaryReceipt ≡ false
ternaryGolayBoundaryReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse ternaryGolayBoundaryReceipt
