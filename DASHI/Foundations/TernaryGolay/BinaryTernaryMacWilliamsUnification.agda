module DASHI.Foundations.TernaryGolay.BinaryTernaryMacWilliamsUnification where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_*_; _+_)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Explicit
import DASHI.Foundations.TernaryGolay.SmallWittHexadCount as SmallWitt
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Common MacWilliams coefficient surface.
--
-- MacWilliams' identity is naturally q-ary. Rather than duplicating a
-- binary-octad calculation and a ternary-hexad calculation, this module gives
-- one coefficient-level interface and attaches both specialisations.
--
-- The general transform theorem is not silently postulated: a concrete code
-- must supply the coefficient numerator and the equality below. The ternary
-- specialisation is already backed by exhaustive local enumeration; the
-- binary 759-octad equation remains a named theorem-import boundary.
------------------------------------------------------------------------

record QaryWeightDistribution : Set₁ where
  constructor qaryWeightDistribution
  field
    alphabetSize : Nat
    blockLength : Nat
    codeSize : Nat
    weightCount : Nat → Nat

open QaryWeightDistribution public

record MacWilliamsCoefficientIdentity
    (distribution dualDistribution : QaryWeightDistribution) : Set₁ where
  field
    transformNumerator : Nat → Nat
    coefficientLaw :
      (weight : Nat) →
      codeSize distribution * weightCount dualDistribution weight
      ≡ transformNumerator weight

open MacWilliamsCoefficientIdentity public

record SelfDualMacWilliamsIdentity
    (distribution : QaryWeightDistribution) : Set₁ where
  field
    transform : MacWilliamsCoefficientIdentity distribution distribution
    selfDualReading : String
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String

open SelfDualMacWilliamsIdentity public

ternaryGolayDistribution : QaryWeightDistribution
ternaryGolayDistribution =
  qaryWeightDistribution
    3
    12
    729
    (λ weight → Explicit.countWeight weight Explicit.allCodewords)

ternaryWeightCount0 :
  weightCount ternaryGolayDistribution 0 ≡ 1
ternaryWeightCount0 = Explicit.weight0Count

ternaryWeightCount6 :
  weightCount ternaryGolayDistribution 6 ≡ 264
ternaryWeightCount6 = Explicit.weight6Count

ternaryWeightCount9 :
  weightCount ternaryGolayDistribution 9 ≡ 440
ternaryWeightCount9 = Explicit.weight9Count

ternaryWeightCount12 :
  weightCount ternaryGolayDistribution 12 ≡ 24
ternaryWeightCount12 = Explicit.weight12Count

record MacWilliamsGeneralTheoremStatus : Set where
  constructor macWilliamsGeneralTheoremStatus
  field
    theoremAuthor : String
    theoremTitle : String
    theoremDOI : String
    theoremURL : String
    qAryTransformInterfacePresent : Bool
    qAryTransformInterfacePresentIsTrue :
      qAryTransformInterfacePresent ≡ true
    generalPolynomialProofImportedHere : Bool
    generalPolynomialProofImportedHereIsFalse :
      generalPolynomialProofImportedHere ≡ false
    ternarySpecialisationComputedLocally : Bool
    ternarySpecialisationComputedLocallyIsTrue :
      ternarySpecialisationComputedLocally ≡ true

canonicalMacWilliamsGeneralTheoremStatus :
  MacWilliamsGeneralTheoremStatus
canonicalMacWilliamsGeneralTheoremStatus =
  macWilliamsGeneralTheoremStatus
    (Sources.author Sources.macWilliamsSystematicWeightEntry)
    (Sources.title Sources.macWilliamsSystematicWeightEntry)
    "10.1002/j.1538-7305.1963.tb04003.x"
    (Sources.canonicalURL Sources.macWilliamsSystematicWeightEntry)
    true refl
    false refl
    true refl

------------------------------------------------------------------------
-- Binary and ternary exceptional specialisations.
------------------------------------------------------------------------

record BinaryGolayOctadCoefficientReceipt : Set where
  constructor binaryGolayOctadCoefficientReceipt
  field
    octadCount : Nat
    reducedCoefficientEquation :
      64 * octadCount ≡ 48576
    octadCountIs759 : octadCount ≡ 759
    binaryMacWilliamsDerivationImportedHere : Bool
    binaryMacWilliamsDerivationImportedHereIsFalse :
      binaryMacWilliamsDerivationImportedHere ≡ false

canonicalBinaryGolayOctadCoefficientReceipt :
  BinaryGolayOctadCoefficientReceipt
canonicalBinaryGolayOctadCoefficientReceipt =
  binaryGolayOctadCoefficientReceipt
    759
    refl
    refl
    false refl

record TernaryGolayHexadCoefficientReceipt : Set where
  constructor ternaryGolayHexadCoefficientReceipt
  field
    weightSixCodewordCount : Nat
    signOrbitSize : Nat
    distinctHexadCount : Nat
    weightSixCodewordCountIs264 :
      weightSixCodewordCount ≡ 264
    signOrbitSizeIsTwo :
      signOrbitSize ≡ 2
    distinctHexadCountIs132 :
      distinctHexadCount ≡ 132
    orbitArithmetic :
      signOrbitSize * distinctHexadCount ≡ weightSixCodewordCount
    distinctSupportCountComputed :
      Explicit.listCount SmallWitt.hexadSupports ≡ distinctHexadCount

canonicalTernaryGolayHexadCoefficientReceipt :
  TernaryGolayHexadCoefficientReceipt
canonicalTernaryGolayHexadCoefficientReceipt =
  ternaryGolayHexadCoefficientReceipt
    264
    2
    132
    refl
    refl
    refl
    refl
    SmallWitt.hexadSupportCountIs132

record BinaryTernaryMacWilliamsBridgeStatus : Set where
  constructor binaryTernaryMacWilliamsBridgeStatus
  field
    sameQaryTransformSchema : Bool
    sameQaryTransformSchemaIsTrue :
      sameQaryTransformSchema ≡ true
    binaryOctadCountAttached : Bool
    binaryOctadCountAttachedIsTrue :
      binaryOctadCountAttached ≡ true
    ternaryEnumeratorComputed : Bool
    ternaryEnumeratorComputedIsTrue :
      ternaryEnumeratorComputed ≡ true
    ternaryHexadDesignComputed : Bool
    ternaryHexadDesignComputedIsTrue :
      ternaryHexadDesignComputed ≡ true
    oneProofAutomaticallyCoversBothFields : Bool
    oneProofAutomaticallyCoversBothFieldsIsFalse :
      oneProofAutomaticallyCoversBothFields ≡ false
    reading : String

canonicalBinaryTernaryMacWilliamsBridgeStatus :
  BinaryTernaryMacWilliamsBridgeStatus
canonicalBinaryTernaryMacWilliamsBridgeStatus =
  binaryTernaryMacWilliamsBridgeStatus
    true refl
    true refl
    true refl
    true refl
    false refl
    "binary and ternary Golay enumerators share the q-ary MacWilliams schema, but q=2 and q=3 coefficient kernels remain distinct specialisations; the ternary lane is locally exhaustive while the binary coefficient derivation is an attributed import boundary"

macWilliamsUnificationGenericReceipt : GenericReceipt.GenericReceipt
macWilliamsUnificationGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "binary/ternary MacWilliams unification"
    "DASHI.Foundations.TernaryGolay.BinaryTernaryMacWilliamsUnification"
    "canonicalBinaryTernaryMacWilliamsBridgeStatus"
    "a common q-ary coefficient interface, the binary 759-octad reduced equation, the exact ternary 1/264/440/24 distribution, and the 132-hexad sign-orbit calculation are attached"
    "the common schema does not erase the q=2/q=3 specialisation proofs; the general polynomial transform and binary derivation remain named source obligations"
    "agda -i . DASHI/Foundations/TernaryGolay/BinaryTernaryMacWilliamsUnification.agda"

macWilliamsUnificationGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim macWilliamsUnificationGenericReceipt ≡ false
macWilliamsUnificationGenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse macWilliamsUnificationGenericReceipt
