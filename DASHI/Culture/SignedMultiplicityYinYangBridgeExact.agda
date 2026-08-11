module DASHI.Culture.SignedMultiplicityYinYangBridgeExact where

------------------------------------------------------------------------
-- DASHI CROSS-POLLINATION
--
-- This file connects an exact algebraic three-way sign quotient to the
-- repository's EXISTING candidate-only yin/yang polarity vocabulary.  The
-- mathematics lives in SignedMultiplicityObstructionExact; the cultural labels
-- remain interpretive vocabulary guarded by YinYangPolarityBoundary's
-- fail-closed authority bits.
--
-- No theorem about Taoism, Chinese philosophy, politics, psychology, or
-- empirical social systems is inferred from the formal correspondence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.SignedMultiplicityObstructionExact as Defect
import DASHI.Culture.YinYangPolarityBoundary as YinYang

polarityOfDefect : Defect.DefectOrientation → YinYang.PolarityTerm
polarityOfDefect Defect.negativeDefect = YinYang.yinPole
polarityOfDefect Defect.balancedDefect = YinYang.balancedMiddle
polarityOfDefect Defect.positiveDefect = YinYang.yangPole

reversePolarity : YinYang.PolarityTerm → YinYang.PolarityTerm
reversePolarity YinYang.yinPole = YinYang.yangPole
reversePolarity YinYang.yangPole = YinYang.yinPole
reversePolarity YinYang.balancedMiddle = YinYang.balancedMiddle
reversePolarity term = term

reversePolarityOnDefectImage :
  (orientation : Defect.DefectOrientation) →
  reversePolarity (polarityOfDefect orientation)
  ≡ polarityOfDefect (Defect.reverseOrientation orientation)
reversePolarityOnDefectImage Defect.negativeDefect = refl
reversePolarityOnDefectImage Defect.balancedDefect = refl
reversePolarityOnDefectImage Defect.positiveDefect = refl

swapMultiplicityReversesCandidatePolarity :
  ∀ {I} (A B : Defect.Multiplicity I) (i : I) →
  polarityOfDefect
    (Defect.orientationOfInteger (Defect.delta B A i))
  ≡
  reversePolarity
    (polarityOfDefect
      (Defect.orientationOfInteger (Defect.delta A B i)))
swapMultiplicityReversesCandidatePolarity A B i
  rewrite Defect.orientationSwap A B i =
  sym
    (reversePolarityOnDefectImage
      (Defect.orientationOfInteger (Defect.delta A B i)))

-- The middle is the fixed locus of this restricted polarity inversion.
balancedMiddleFixed :
  reversePolarity YinYang.balancedMiddle ≡ YinYang.balancedMiddle
balancedMiddleFixed = refl

-- Re-export the pre-existing fail-closed authority certificate rather than
-- manufacturing a new authority claim in this bridge.
existingYinYangAuthorityBoundary : YinYang.YinYangAuthorityFailClosed
existingYinYangAuthorityBoundary = YinYang.canonicalYinYangAuthorityFailClosed

record SignedMultiplicityYinYangClaimScope : Set where
  constructor signedMultiplicityYinYangClaimScope
  field
    algebraicSignPolarityBridgeConstructed : Bool
    algebraicSignPolarityBridgeConstructedIsTrue :
      algebraicSignPolarityBridgeConstructed ≡ true

    culturalVocabularyPromotedToMathematicalAuthority : Bool
    culturalVocabularyPromotedToMathematicalAuthorityIsFalse :
      culturalVocabularyPromotedToMathematicalAuthority ≡ false

    politicalOrEmpiricalTheoryProved : Bool
    politicalOrEmpiricalTheoryProvedIsFalse :
      politicalOrEmpiricalTheoryProved ≡ false

canonicalSignedMultiplicityYinYangClaimScope :
  SignedMultiplicityYinYangClaimScope
canonicalSignedMultiplicityYinYangClaimScope =
  signedMultiplicityYinYangClaimScope true refl false refl false refl
