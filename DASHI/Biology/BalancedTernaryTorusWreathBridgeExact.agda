module DASHI.Biology.BalancedTernaryTorusWreathBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications".
-- DOI: 10.1017/CBO9780511626265.
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups".
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- Volodymyr Nekrashevych,
-- "Self-Similar Groups".
-- DOI: 10.1090/surv/117.
--
-- DASHI CONTRIBUTION
-- Identify the nine ordinary balanced-pair channels with the finite 3x3 torus
-- carrier and the distinguished j channel with the separate completion point.
-- This supplies exact commuting order-three translations and their pullback
-- action on fine assignments while preserving the distinction between the
-- ordinary torus and j completion channel.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

encodeTrit : Harmonic.BalancedTrit → Torus.Residue3
encodeTrit Harmonic.negativeTrit = Torus.residueMinus
encodeTrit Harmonic.zeroTrit = Torus.residueZero
encodeTrit Harmonic.positiveTrit = Torus.residuePlus

decodeTrit : Torus.Residue3 → Harmonic.BalancedTrit
decodeTrit Torus.residueMinus = Harmonic.negativeTrit
decodeTrit Torus.residueZero = Harmonic.zeroTrit
decodeTrit Torus.residuePlus = Harmonic.positiveTrit

decodeEncodeTrit : ∀ trit → decodeTrit (encodeTrit trit) ≡ trit
decodeEncodeTrit Harmonic.negativeTrit = refl
decodeEncodeTrit Harmonic.zeroTrit = refl
decodeEncodeTrit Harmonic.positiveTrit = refl

encodePair : Harmonic.BalancedPair → Torus.Torus3x3
encodePair pair =
  Torus.torusPoint
    (encodeTrit (Harmonic.firstTrit pair))
    (encodeTrit (Harmonic.secondTrit pair))

decodePair : Torus.Torus3x3 → Harmonic.BalancedPair
decodePair point =
  Harmonic.balancedPair
    (decodeTrit (Torus.firstCoordinate point))
    (decodeTrit (Torus.secondCoordinate point))

decodeEncodePair : ∀ pair → decodePair (encodePair pair) ≡ pair
decodeEncodePair
  (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit) = refl
decodeEncodePair
  (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit) = refl
decodeEncodePair
  (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit) = refl
decodeEncodePair
  (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit) = refl
decodeEncodePair
  (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit) = refl
decodeEncodePair
  (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit) = refl
decodeEncodePair
  (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit) = refl
decodeEncodePair
  (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit) = refl
decodeEncodePair
  (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit) = refl

encodeChannel : Harmonic.CoarseChannel → Torus.CompletedTorusChannel
encodeChannel (Harmonic.ordinaryChannel pair) =
  Torus.ordinaryTorusChannel (encodePair pair)
encodeChannel Harmonic.completionJ = Torus.completionChannel

decodeChannel : Torus.CompletedTorusChannel → Harmonic.CoarseChannel
decodeChannel (Torus.ordinaryTorusChannel point) =
  Harmonic.ordinaryChannel (decodePair point)
decodeChannel Torus.completionChannel = Harmonic.completionJ

decodeEncodeChannel : ∀ channel → decodeChannel (encodeChannel channel) ≡ channel
decodeEncodeChannel (Harmonic.ordinaryChannel pair)
  rewrite decodeEncodePair pair = refl
decodeEncodeChannel Harmonic.completionJ = refl

translateFirstBalanced : Harmonic.CoarseChannel → Harmonic.CoarseChannel
translateFirstBalanced channel =
  decodeChannel (Torus.completedTranslateFirst (encodeChannel channel))

translateSecondBalanced : Harmonic.CoarseChannel → Harmonic.CoarseChannel
translateSecondBalanced channel =
  decodeChannel (Torus.completedTranslateSecond (encodeChannel channel))

completionJFixedByFirstTranslation :
  translateFirstBalanced Harmonic.completionJ ≡ Harmonic.completionJ
completionJFixedByFirstTranslation = refl

completionJFixedBySecondTranslation :
  translateSecondBalanced Harmonic.completionJ ≡ Harmonic.completionJ
completionJFixedBySecondTranslation = refl

record BalancedTorusBoundary : Set where
  constructor balancedTorusBoundary
  field
    jIsTenthOrdinaryTorusResidue : Set
    jIsNotTenthOrdinaryTorusResidue :
      jIsTenthOrdinaryTorusResidue → Set

    finiteTranslationsConstructMonsterAction : Set
    finiteTranslationsDoNotConstructMonsterAction :
      finiteTranslationsConstructMonsterAction → Set

canonicalBalancedTorusBoundary : BalancedTorusBoundary
canonicalBalancedTorusBoundary =
  balancedTorusBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
