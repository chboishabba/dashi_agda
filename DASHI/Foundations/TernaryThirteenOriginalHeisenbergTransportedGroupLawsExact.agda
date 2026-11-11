module DASHI.Foundations.TernaryThirteenOriginalHeisenbergTransportedGroupLawsExact where

------------------------------------------------------------------------
-- All actual finite Heisenberg group laws on the original transported
-- thirteen-word carrier, using the original cocycle multiplication.
-- This is neither the abelian product on 13 F3 coordinates nor a
-- semantic identification with Monster/ITIR/appraisal world states.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.TernaryThirteenOriginalHeisenbergGroupCarrierExact as Bridge
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Word
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BF3AlgebraExact as F3
import DASHI.Moonshine.Monster3BFiniteHeisenbergAssociativityExact as Assoc
import DASHI.Moonshine.Monster3BFiniteHeisenbergInverseExact as Inv

-- A direct original group-side identity, proved over every one of
-- the 12 source F3 coordinates and the cocycle's central phase.
originalLeftIdentity :
  (g : H.Heisenberg6) → H.compose H.identityH g ≡ g
originalLeftIdentity
  (H.heisenberg6
    (H.symplectic12 (G.x6 a b c d e f)
                    (G.x6 u v w x y z)) phase)
  rewrite F3.plusRightZero phase = refl

-- Source associativity, left inverse and right inverse complete
-- the right-identity law without an independent dot-right-zero
-- assumption or any hidden commutativity premise.
originalRightIdentity :
  (g : H.Heisenberg6) → H.compose g H.identityH ≡ g
originalRightIdentity g =
  trans
    (sym (cong (H.compose g) (Inv.leftInverse g)))
    (trans
      (sym (Assoc.composeAssociative g (Inv.inverseH g) g))
      (trans
        (cong (λ h → H.compose h g) (Inv.rightInverse g))
        (originalLeftIdentity g)))

-- Existing exact coding is a two-sided inverse of full FINITE
-- records, so all transported group identities are propositional
-- equalities of the original TritWord13, not just axiswise claims.
decodedWordIdentity :
  Bridge.wordToOriginalGroup Bridge.wordIdentity ≡ H.identityH
decodedWordIdentity = Bridge.originalIdentityRespected

decodedWordInverse :
  (code : Word.TritWord 13) →
  Bridge.wordToOriginalGroup (Bridge.wordInverse code)
  ≡ Inv.inverseH (Bridge.wordToOriginalGroup code)
decodedWordInverse code =
  Bridge.originalGroupRoundTrip
    (Inv.inverseH (Bridge.wordToOriginalGroup code))

wordAssoc :
  (a b c : Word.TritWord 13) →
  Bridge.wordCompose (Bridge.wordCompose a b) c
  ≡ Bridge.wordCompose a (Bridge.wordCompose b c)
wordAssoc a b c =
  trans
    (cong
      (λ q → Bridge.originalGroupToWord
        (H.compose q (Bridge.wordToOriginalGroup c)))
      (Bridge.wordMultiplicationDecoded a b))
    (trans
      (cong Bridge.originalGroupToWord
        (Assoc.composeAssociative
          (Bridge.wordToOriginalGroup a)
          (Bridge.wordToOriginalGroup b)
          (Bridge.wordToOriginalGroup c)))
      (sym
        (cong
          (λ q → Bridge.originalGroupToWord
            (H.compose (Bridge.wordToOriginalGroup a) q))
          (Bridge.wordMultiplicationDecoded b c))))

wordLeftIdentity :
  (a : Word.TritWord 13) →
  Bridge.wordCompose Bridge.wordIdentity a ≡ a
wordLeftIdentity a =
  trans
    (cong
      (λ q → Bridge.originalGroupToWord
        (H.compose q (Bridge.wordToOriginalGroup a)))
      decodedWordIdentity)
    (trans
      (cong Bridge.originalGroupToWord
        (originalLeftIdentity (Bridge.wordToOriginalGroup a)))
      (Bridge.originalWordRoundTrip a))

wordRightIdentity :
  (a : Word.TritWord 13) →
  Bridge.wordCompose a Bridge.wordIdentity ≡ a
wordRightIdentity a =
  trans
    (cong
      (λ q → Bridge.originalGroupToWord
        (H.compose (Bridge.wordToOriginalGroup a) q))
      decodedWordIdentity)
    (trans
      (cong Bridge.originalGroupToWord
        (originalRightIdentity (Bridge.wordToOriginalGroup a)))
      (Bridge.originalWordRoundTrip a))

wordLeftInverse :
  (a : Word.TritWord 13) →
  Bridge.wordCompose (Bridge.wordInverse a) a
  ≡ Bridge.wordIdentity
wordLeftInverse a =
  trans
    (cong
      (λ q → Bridge.originalGroupToWord
        (H.compose q (Bridge.wordToOriginalGroup a)))
      (decodedWordInverse a))
    (cong Bridge.originalGroupToWord
      (Inv.leftInverse (Bridge.wordToOriginalGroup a)))

wordRightInverse :
  (a : Word.TritWord 13) →
  Bridge.wordCompose a (Bridge.wordInverse a)
  ≡ Bridge.wordIdentity
wordRightInverse a =
  trans
    (cong
      (λ q → Bridge.originalGroupToWord
        (H.compose (Bridge.wordToOriginalGroup a) q))
      (decodedWordInverse a))
    (cong Bridge.originalGroupToWord
      (Inv.rightInverse (Bridge.wordToOriginalGroup a)))

record OriginalTransportedFiniteGroup : Set where
  constructor original-transported-finite-group
  field
    associative :
      (a b c : Word.TritWord 13) →
      Bridge.wordCompose (Bridge.wordCompose a b) c
      ≡ Bridge.wordCompose a (Bridge.wordCompose b c)
    leftUnit :
      (a : Word.TritWord 13) →
      Bridge.wordCompose Bridge.wordIdentity a ≡ a
    rightUnit :
      (a : Word.TritWord 13) →
      Bridge.wordCompose a Bridge.wordIdentity ≡ a
    leftInverse :
      (a : Word.TritWord 13) →
      Bridge.wordCompose (Bridge.wordInverse a) a
      ≡ Bridge.wordIdentity
    rightInverse :
      (a : Word.TritWord 13) →
      Bridge.wordCompose a (Bridge.wordInverse a)
      ≡ Bridge.wordIdentity
    noncommutative :
      Bridge.wordCompose
        (Bridge.originalGroupToWord Bridge.sourceTranslation)
        (Bridge.originalGroupToWord Bridge.sourceModulation)
      ≡ Bridge.wordCompose
        (Bridge.originalGroupToWord Bridge.sourceModulation)
        (Bridge.originalGroupToWord Bridge.sourceTranslation) → ⊥

originalTransportedFiniteGroup : OriginalTransportedFiniteGroup
originalTransportedFiniteGroup =
  original-transported-finite-group
    wordAssoc wordLeftIdentity wordRightIdentity
    wordLeftInverse wordRightInverse
    Bridge.wordGeneratorOrderMatters

------------------------------------------------------------------------
-- H1.01 semantic *admission obstruction*:
-- no commutative law on a 13-coordinate representation can be
-- simultaneously identical to the existing source H_6 group law.
-- A proposed independently intended relational completion must
-- retain this nontrivial cocycle/noncommuting source action.
------------------------------------------------------------------------

commutativeSemanticCompletionCannotAgree :
  (candidate :
    Word.TritWord 13 →
    Word.TritWord 13 →
    Word.TritWord 13) →
  ((a b : Word.TritWord 13) →
    candidate a b ≡ candidate b a) →
  ((g h : H.Heisenberg6) →
    candidate (Bridge.originalGroupToWord g)
              (Bridge.originalGroupToWord h)
    ≡ Bridge.wordCompose
        (Bridge.originalGroupToWord g)
        (Bridge.originalGroupToWord h)) →
  ⊥
commutativeSemanticCompletionCannotAgree candidate commutative agrees =
  Bridge.wordGeneratorOrderMatters
    (trans
      (sym (agrees Bridge.sourceTranslation Bridge.sourceModulation))
      (trans
        (commutative
          (Bridge.originalGroupToWord Bridge.sourceTranslation)
          (Bridge.originalGroupToWord Bridge.sourceModulation))
        (agrees Bridge.sourceModulation Bridge.sourceTranslation)))
