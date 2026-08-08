module DASHI.Moonshine.Monster3BActualKernelCharacterPromotionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- R. A. Wilson, P. Walsh, R. A. Parker and S. Linton,
-- "A computer construction of the Monster",
-- Journal of Group Theory 1 (1998), 307--337.
-- DOI: 10.1515/jgth.1998.023.
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Separate the now-computable actual-kernel structure from the remaining
-- character recognition.  Once the actual restricted character is matched to
-- the extraspecial four-class signature, every named consequence below is
-- derived, including noncentral vanishing and multiplicity ninety.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Moonshine.Monster3BExtraspecialCharacterSignatureExact as Signature

------------------------------------------------------------------------
-- Actual AtlasRep/CTblLib structure certificate shape.
------------------------------------------------------------------------

record ActualMN3BKernelStructure : Set where
  constructor actual-mn3b-kernel-structure
  field
    normalizerOrder : Nat
    kernelOrder : Nat
    kernelExponent : Nat
    centreOrder : Nat
    derivedOrder : Nat
    quotientOrder : Nat
    centreOrbitSize : Nat
    mn3bCentralClassPosition : Nat
    monsterThreeBClassPosition : Nat

    normalizerOrderExact : normalizerOrder ≡ 2859230155080499200
    kernelOrderExact : kernelOrder ≡ 1594323
    kernelExponentExact : kernelExponent ≡ 3
    centreOrderExact : centreOrder ≡ 3
    derivedOrderExact : derivedOrder ≡ 3
    quotientOrderExact : quotientOrder ≡ 531441
    centreOrbitSizeExact : centreOrbitSize ≡ 2

open ActualMN3BKernelStructure public

------------------------------------------------------------------------
-- Character-level recognition of the actual zeta sector.
------------------------------------------------------------------------

record ActualKernelCharacterPromotion : Set₁ where
  constructor actual-kernel-character-promotion
  field
    kernelStructure : ActualMN3BKernelStructure
    ActualKernelClass : Set
    classifyKernelClass :
      ActualKernelClass → Signature.ExtraspecialClassKind
    actualRestrictedCharacter :
      ActualKernelClass → Signature.C3Trace

    actualCharacterRecognized :
      (class : ActualKernelClass) →
      actualRestrictedCharacter class
      ≡ Signature.ninetyHeisenbergCharacter
          (classifyKernelClass class)

open ActualKernelCharacterPromotion public

actualKernelCharacterIdentity :
  (promotion : ActualKernelCharacterPromotion) →
  (class : ActualKernelClass promotion) →
  actualRestrictedCharacter promotion class
  ≡ Signature.ninetyHeisenbergCharacter
      (classifyKernelClass promotion class)
actualKernelCharacterIdentity = actualCharacterRecognized

record ClassifiedKernelClass
  (promotion : ActualKernelCharacterPromotion)
  (kind : Signature.ExtraspecialClassKind) : Set where
  constructor classified-kernel-class
  field
    class : ActualKernelClass promotion
    classification : classifyKernelClass promotion class ≡ kind

open ClassifiedKernelClass public

actualKernelNoncentralCharacterVanishes :
  (promotion : ActualKernelCharacterPromotion) →
  (classified : ClassifiedKernelClass promotion Signature.noncentralClass) →
  actualRestrictedCharacter promotion (class classified)
  ≡ Signature.zeroTrace
actualKernelNoncentralCharacterVanishes promotion classified
  rewrite actualKernelCharacterIdentity promotion (class classified)
        | classification classified = refl

actualKernelCentralCharacterIsZeta :
  (promotion : ActualKernelCharacterPromotion) →
  (classified :
    ClassifiedKernelClass promotion Signature.centralZetaClass) →
  Signature.zetaCoefficient
    (actualRestrictedCharacter promotion (class classified))
  ≡ 65610
actualKernelCentralCharacterIsZeta promotion classified
  rewrite actualKernelCharacterIdentity promotion (class classified)
        | classification classified = refl

record NinetyHeisenbergCharacterIsotypy
  (promotion : ActualKernelCharacterPromotion) : Set₁ where
  constructor ninety-heisenberg-character-isotypy
  field
    multiplicity : Nat
    multiplicityIsNinety : multiplicity ≡ 90
    characterEquality :
      (class : ActualKernelClass promotion) →
      actualRestrictedCharacter promotion class
      ≡ Signature.scaleTrace multiplicity
          (Signature.heisenbergZetaCharacter
            (classifyKernelClass promotion class))

open NinetyHeisenbergCharacterIsotypy public

actualZetaSectorIsNinetyHeisenbergCopies :
  (promotion : ActualKernelCharacterPromotion) →
  NinetyHeisenbergCharacterIsotypy promotion
actualZetaSectorIsNinetyHeisenbergCopies promotion =
  ninety-heisenberg-character-isotypy
    90
    refl
    (actualCharacterRecognized promotion)

------------------------------------------------------------------------
-- Exact boundary after this tranche.
------------------------------------------------------------------------

record ActualKernelPromotionStatus : Set where
  constructor actual-kernel-promotion-status
  field
    atlasKernelStructureProducerImplemented : Bool
    atlasKernelStructureProducerImplementedIsTrue :
      atlasKernelStructureProducerImplemented ≡ true
    characterSignatureTheoremImplemented : Bool
    characterSignatureTheoremImplementedIsTrue :
      characterSignatureTheoremImplemented ≡ true
    actualKernelCharacterCertificateObserved : Bool
    actualKernelCharacterCertificateObservedIsFalse :
      actualKernelCharacterCertificateObserved ≡ false
    actualMultiplicityCharacterComputed : Bool
    actualMultiplicityCharacterComputedIsFalse :
      actualMultiplicityCharacterComputed ≡ false

canonicalActualKernelPromotionStatus : ActualKernelPromotionStatus
canonicalActualKernelPromotionStatus =
  actual-kernel-promotion-status
    true refl
    true refl
    false refl
    false refl
