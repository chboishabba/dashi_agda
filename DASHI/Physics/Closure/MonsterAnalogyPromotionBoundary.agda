module DASHI.Physics.Closure.MonsterAnalogyPromotionBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CRTMonsterFixedPointCompactificationBoundary as CRTMonster

------------------------------------------------------------------------
-- Monster analogy promotion boundary.
--
-- This surface consumes the checked CRT/J/196884/Monster boundary but does
-- not promote numerological or analogy rows into Monster theorem facts.

data MonsterAnalogyPromotionBoundaryStatus : Set where
  checkedCRTJ196884BoundaryAnalogyOnlyNoPromotion :
    MonsterAnalogyPromotionBoundaryStatus

data MonsterAnalogyPromotionBoundaryRow : Set where
  rowExactArithmeticLinkConsumed :
    MonsterAnalogyPromotionBoundaryRow

  row196884AnalogyOnly :
    MonsterAnalogyPromotionBoundaryRow

  rowElevenFirstGenuinelyNewBlocked :
    MonsterAnalogyPromotionBoundaryRow

  rowNoMonsterTheoremPromotion :
    MonsterAnalogyPromotionBoundaryRow

  rowNoSocialTopologicalAnalogyPromotion :
    MonsterAnalogyPromotionBoundaryRow

  rowNoTerminalPromotion :
    MonsterAnalogyPromotionBoundaryRow

canonicalMonsterAnalogyPromotionBoundaryRows :
  List MonsterAnalogyPromotionBoundaryRow
canonicalMonsterAnalogyPromotionBoundaryRows =
  rowExactArithmeticLinkConsumed
  ∷ row196884AnalogyOnly
  ∷ rowElevenFirstGenuinelyNewBlocked
  ∷ rowNoMonsterTheoremPromotion
  ∷ rowNoSocialTopologicalAnalogyPromotion
  ∷ rowNoTerminalPromotion
  ∷ []

data FirstGenuinelyNewElevenClaimToken : Set where

data Analogy196884TheoremFactToken : Set where

data SocialTopologicalAnalogyPromotionToken : Set where

data TerminalAnalogyPromotionToken : Set where

noFirstGenuinelyNewElevenClaimHere :
  FirstGenuinelyNewElevenClaimToken →
  ⊥
noFirstGenuinelyNewElevenClaimHere ()

noAnalogy196884TheoremFactHere :
  Analogy196884TheoremFactToken →
  ⊥
noAnalogy196884TheoremFactHere ()

noSocialTopologicalAnalogyPromotionHere :
  SocialTopologicalAnalogyPromotionToken →
  ⊥
noSocialTopologicalAnalogyPromotionHere ()

noTerminalAnalogyPromotionHere :
  TerminalAnalogyPromotionToken →
  ⊥
noTerminalAnalogyPromotionHere ()

record AnalogyOnly196884Row : Setω where
  field
    exactArithmeticLink :
      CRTMonster.Arithmetic196884EqualityLink

    exactArithmeticLinkIsCanonical :
      exactArithmeticLink
      ≡
      CRTMonster.canonicalArithmetic196884EqualityLink

    exactArithmeticScalar :
      Nat

    exactArithmeticScalarIsConsumed :
      exactArithmeticScalar
      ≡
      CRTMonster.arithmeticScalar exactArithmeticLink

    exactArithmeticScalarIs196884 :
      exactArithmeticScalar ≡ 196884

    analogyOnlyScalar :
      Nat

    analogyOnlyScalarIsExactArithmeticScalar :
      analogyOnlyScalar ≡ exactArithmeticScalar

    analogyOnlyScalarIs196884 :
      analogyOnlyScalar ≡ 196884

    monsterAuthorityRequiredForTheoremFact :
      Bool

    monsterAuthorityRequiredForTheoremFactIsTrue :
      monsterAuthorityRequiredForTheoremFact ≡ true

    monsterAuthoritySuppliedHere :
      Bool

    monsterAuthoritySuppliedHereIsFalse :
      monsterAuthoritySuppliedHere ≡ false

    analogyPromotedToMonsterTheoremFact :
      Bool

    analogyPromotedToMonsterTheoremFactIsFalse :
      analogyPromotedToMonsterTheoremFact ≡ false

open AnalogyOnly196884Row public

canonicalAnalogyOnly196884Row :
  AnalogyOnly196884Row
canonicalAnalogyOnly196884Row =
  record
    { exactArithmeticLink =
        CRTMonster.canonicalArithmetic196884EqualityLink
    ; exactArithmeticLinkIsCanonical =
        refl
    ; exactArithmeticScalar =
        CRTMonster.arithmeticScalar
          CRTMonster.canonicalArithmetic196884EqualityLink
    ; exactArithmeticScalarIsConsumed =
        refl
    ; exactArithmeticScalarIs196884 =
        refl
    ; analogyOnlyScalar =
        CRTMonster.arithmeticScalar
          CRTMonster.canonicalArithmetic196884EqualityLink
    ; analogyOnlyScalarIsExactArithmeticScalar =
        refl
    ; analogyOnlyScalarIs196884 =
        refl
    ; monsterAuthorityRequiredForTheoremFact =
        true
    ; monsterAuthorityRequiredForTheoremFactIsTrue =
        refl
    ; monsterAuthoritySuppliedHere =
        false
    ; monsterAuthoritySuppliedHereIsFalse =
        refl
    ; analogyPromotedToMonsterTheoremFact =
        false
    ; analogyPromotedToMonsterTheoremFactIsFalse =
        refl
    }

record ElevenFirstNewClaimBoundaryRow : Set where
  field
    elevenIndex :
      Nat

    elevenIndexIsEleven :
      elevenIndex ≡ 11

    firstGenuinelyNewClaimedHere :
      Bool

    firstGenuinelyNewClaimedHereIsFalse :
      firstGenuinelyNewClaimedHere ≡ false

    firstGenuinelyNewRequiresExternalAuthority :
      Bool

    firstGenuinelyNewRequiresExternalAuthorityIsTrue :
      firstGenuinelyNewRequiresExternalAuthority ≡ true

open ElevenFirstNewClaimBoundaryRow public

canonicalElevenFirstNewClaimBoundaryRow :
  ElevenFirstNewClaimBoundaryRow
canonicalElevenFirstNewClaimBoundaryRow =
  record
    { elevenIndex =
        11
    ; elevenIndexIsEleven =
        refl
    ; firstGenuinelyNewClaimedHere =
        false
    ; firstGenuinelyNewClaimedHereIsFalse =
        refl
    ; firstGenuinelyNewRequiresExternalAuthority =
        true
    ; firstGenuinelyNewRequiresExternalAuthorityIsTrue =
        refl
    }

record MonsterAnalogyPromotionBoundaryReceipt : Setω where
  field
    status :
      MonsterAnalogyPromotionBoundaryStatus

    upstreamCRTMonsterBoundaryReceipt :
      CRTMonster.CRTMonsterFixedPointCompactificationBoundaryReceipt

    upstreamCRTMonsterBoundaryReceiptCanonical :
      Bool

    upstreamCRTMonsterBoundaryReceiptCanonicalIsTrue :
      upstreamCRTMonsterBoundaryReceiptCanonical ≡ true

    consumedExactClosureChain :
      CRTMonster.CRTMonsterExactClosureChain

    consumedExactClosureChainFromUpstream :
      Bool

    consumedExactClosureChainFromUpstreamIsTrue :
      consumedExactClosureChainFromUpstream ≡ true

    consumedExactArithmeticLink :
      CRTMonster.Arithmetic196884EqualityLink

    consumedExactArithmeticLinkIsChainLink :
      consumedExactArithmeticLink
      ≡
      CRTMonster.arithmeticEqualityLink consumedExactClosureChain

    consumedExactArithmeticScalar :
      Nat

    consumedExactArithmeticScalarIsLinkScalar :
      consumedExactArithmeticScalar
      ≡
      CRTMonster.arithmeticScalar consumedExactArithmeticLink

    consumedExactArithmeticScalarIs196884 :
      consumedExactArithmeticScalar ≡ 196884

    analogyOnlyRow :
      AnalogyOnly196884Row

    analogyOnlyRowCanonical :
      Bool

    analogyOnlyRowCanonicalIsTrue :
      analogyOnlyRowCanonical ≡ true

    elevenFirstNewBoundaryRow :
      ElevenFirstNewClaimBoundaryRow

    elevenFirstNewBoundaryRowIsCanonical :
      elevenFirstNewBoundaryRow
      ≡
      canonicalElevenFirstNewClaimBoundaryRow

    monsterTheoremPromoted :
      Bool

    monsterTheoremPromotedIsFalse :
      monsterTheoremPromoted ≡ false

    socialTopologicalAnalogyPromoted :
      Bool

    socialTopologicalAnalogyPromotedIsFalse :
      socialTopologicalAnalogyPromoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    rows :
      List MonsterAnalogyPromotionBoundaryRow

    rowsAreCanonical :
      rows ≡ canonicalMonsterAnalogyPromotionBoundaryRows

    noMonsterTheoremPromotion :
      CRTMonster.MonsterTheoremPromotionToken →
      ⊥

    noFirstGenuinelyNewElevenClaim :
      FirstGenuinelyNewElevenClaimToken →
      ⊥

    noAnalogy196884TheoremFact :
      Analogy196884TheoremFactToken →
      ⊥

    noSocialTopologicalAnalogyPromotion :
      SocialTopologicalAnalogyPromotionToken →
      ⊥

    noTerminalPromotion :
      TerminalAnalogyPromotionToken →
      ⊥

    receiptBoundary :
      List String

open MonsterAnalogyPromotionBoundaryReceipt public

canonicalMonsterAnalogyPromotionBoundaryReceipt :
  MonsterAnalogyPromotionBoundaryReceipt
canonicalMonsterAnalogyPromotionBoundaryReceipt =
  record
    { status =
        checkedCRTJ196884BoundaryAnalogyOnlyNoPromotion
    ; upstreamCRTMonsterBoundaryReceipt =
        CRTMonster.canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt
    ; upstreamCRTMonsterBoundaryReceiptCanonical =
        true
    ; upstreamCRTMonsterBoundaryReceiptCanonicalIsTrue =
        refl
    ; consumedExactClosureChain =
        CRTMonster.exactClosureChain
          CRTMonster.canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt
    ; consumedExactClosureChainFromUpstream =
        true
    ; consumedExactClosureChainFromUpstreamIsTrue =
        refl
    ; consumedExactArithmeticLink =
        CRTMonster.arithmeticEqualityLink
          (CRTMonster.exactClosureChain
            CRTMonster.canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt)
    ; consumedExactArithmeticLinkIsChainLink =
        refl
    ; consumedExactArithmeticScalar =
        CRTMonster.arithmeticScalar
          (CRTMonster.arithmeticEqualityLink
            (CRTMonster.exactClosureChain
              CRTMonster.canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt))
    ; consumedExactArithmeticScalarIsLinkScalar =
        refl
    ; consumedExactArithmeticScalarIs196884 =
        refl
    ; analogyOnlyRow =
        canonicalAnalogyOnly196884Row
    ; analogyOnlyRowCanonical =
        true
    ; analogyOnlyRowCanonicalIsTrue =
        refl
    ; elevenFirstNewBoundaryRow =
        canonicalElevenFirstNewClaimBoundaryRow
    ; elevenFirstNewBoundaryRowIsCanonical =
        refl
    ; monsterTheoremPromoted =
        false
    ; monsterTheoremPromotedIsFalse =
        refl
    ; socialTopologicalAnalogyPromoted =
        false
    ; socialTopologicalAnalogyPromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; rows =
        canonicalMonsterAnalogyPromotionBoundaryRows
    ; rowsAreCanonical =
        refl
    ; noMonsterTheoremPromotion =
        CRTMonster.noMonsterTheoremPromotionTokenHere
    ; noFirstGenuinelyNewElevenClaim =
        noFirstGenuinelyNewElevenClaimHere
    ; noAnalogy196884TheoremFact =
        noAnalogy196884TheoremFactHere
    ; noSocialTopologicalAnalogyPromotion =
        noSocialTopologicalAnalogyPromotionHere
    ; noTerminalPromotion =
        noTerminalAnalogyPromotionHere
    ; receiptBoundary =
        "Consumes the checked CRT/J/196884 arithmetic link from CRTMonsterFixedPointCompactificationBoundary." ∷
        "Records 196884 analogy rows as analogy-only unless separate Monster authority is supplied." ∷
        "Blocks the local claim that 11 is the first genuinely new row." ∷
        "Blocks social or topological analogy promotion into theorem facts." ∷
        "Monster theorem promotion and terminal promotion remain false." ∷
        []
    }

canonicalMonsterAnalogyConsumes196884 :
  consumedExactArithmeticScalar
    canonicalMonsterAnalogyPromotionBoundaryReceipt
  ≡
  196884
canonicalMonsterAnalogyConsumes196884 =
  refl

canonicalMonsterAnalogyOnlyNotTheoremFact :
  analogyPromotedToMonsterTheoremFact
    (analogyOnlyRow canonicalMonsterAnalogyPromotionBoundaryReceipt)
  ≡
  false
canonicalMonsterAnalogyOnlyNotTheoremFact =
  refl

canonicalMonsterAnalogyBlocksElevenFirstNew :
  firstGenuinelyNewClaimedHere
    (elevenFirstNewBoundaryRow
      canonicalMonsterAnalogyPromotionBoundaryReceipt)
  ≡
  false
canonicalMonsterAnalogyBlocksElevenFirstNew =
  refl

canonicalMonsterAnalogyNoMonsterTheoremPromotion :
  monsterTheoremPromoted
    canonicalMonsterAnalogyPromotionBoundaryReceipt
  ≡
  false
canonicalMonsterAnalogyNoMonsterTheoremPromotion =
  refl

canonicalMonsterAnalogyNoSocialTopologicalPromotion :
  socialTopologicalAnalogyPromoted
    canonicalMonsterAnalogyPromotionBoundaryReceipt
  ≡
  false
canonicalMonsterAnalogyNoSocialTopologicalPromotion =
  refl

canonicalMonsterAnalogyNoTerminalPromotion :
  terminalPromoted
    canonicalMonsterAnalogyPromotionBoundaryReceipt
  ≡
  false
canonicalMonsterAnalogyNoTerminalPromotion =
  refl
