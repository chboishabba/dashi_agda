module DASHI.ComputerScience.TekumOrdinaryFactorizationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Integer.Base as ℤ using (ℤ; +_; _+_; _*_)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base using (NonZero)
import Data.Nat.Properties as NatP
open import Data.Rational.Base as ℚ using (ℚ; _*_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; _/_; _*_; _≃_; *≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumParsedExactTriadicWeldExact as Weld
import DASHI.ComputerScience.TekumParsedExactRationalCoordinatesExact as Coordinates
import DASHI.ComputerScience.TekumTriadicScaleExact as Scale

------------------------------------------------------------------------
-- SAME-OBJECT ORDINARY FACTORISATION
--
-- The literal parser decoder has already been exposed as
--
--   s ((3^p + I(F)) 3^{e+}) / 3^{e-+p}.
--
-- This owner proves, first in the unnormalised rational setoid, that this is
-- exactly the source product
--
--   s ((3^p + I(F))/3^p) * 3^e.
--
-- Canonical ℚ equality is obtained only afterwards through fromℚᵘ-cong.
------------------------------------------------------------------------

balancedPow3Add :
  (m n : Nat) →
  BT.pow3 (m + n) ≡ BT.pow3 m * BT.pow3 n
balancedPow3Add zero n = sym (NatP.*-identityˡ (BT.pow3 n))
balancedPow3Add (suc m) n
  rewrite balancedPow3Add m n =
  sym (NatP.*-assoc 3 (BT.pow3 m) (BT.pow3 n))

balancedPow3AddSwap :
  (m n : Nat) →
  BT.pow3 (m + n) ≡ BT.pow3 n * BT.pow3 m
balancedPow3AddSwap m n =
  trans (balancedPow3Add m n)
    (NatP.*-comm (BT.pow3 m) (BT.pow3 n))

balancedPow3NonZero : (n : Nat) → NonZero (BT.pow3 n)
balancedPow3NonZero n =
  subst NonZero
    (Weld.exactPow3MatchesBalancedPow3 n)
    (Exact.pow3NonZero n)

applySignMulNat :
  (s : Anchor.TekumSign) (z : ℤ) (n : Nat) →
  Exact.applySign s (z ℤ.* (+ n))
  ≡ Exact.applySign s z ℤ.* (+ n)
applySignMulNat Anchor.negativeSign z n = ℤP.neg-distribˡ-* z (+ n)
applySignMulNat Anchor.zeroSign z n = refl
applySignMulNat Anchor.positiveSign z n = refl

sourceFractionWidth :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → Nat
sourceFractionWidth {extra} {r = r} parsed =
  Regime.fractionCount (8 + extra) r

sourceUnsignedSignificandInteger :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → ℤ
sourceUnsignedSignificandInteger parsed =
  (+ (BT.pow3 (sourceFractionWidth parsed)))
  ℤ.+ BT.toInteger (BT.eval (Source.fractionLST parsed))

rawSourceSignificand :
  ∀ {extra r payload} →
  Vec Trit.Trit (8 + extra) →
  Source.ParsedPayload extra r payload → ℚᵘ
rawSourceSignificand word parsed =
  let instance denominatorNonZero = balancedPow3NonZero (sourceFractionWidth parsed)
  in Exact.applySign (Source.signOfWord word)
       (sourceUnsignedSignificandInteger parsed)
     ℚᵘ./ BT.pow3 (sourceFractionWidth parsed)

sourceExponentInteger :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → ℤ
sourceExponentInteger parsed =
  Exact.intCodeToInteger (Source.exponentIntCode parsed)

rawSourceScale :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → ℚᵘ
rawSourceScale parsed = Scale.rawTriadicScale (sourceExponentInteger parsed)

rawSourceFactorization :
  ∀ {extra r payload} →
  Vec Trit.Trit (8 + extra) →
  Source.ParsedPayload extra r payload → ℚᵘ
rawSourceFactorization word parsed =
  rawSourceSignificand word parsed ℚᵘ.* rawSourceScale parsed

rawParsedExact :
  ∀ {extra r payload} →
  Vec Trit.Trit (8 + extra) →
  Source.ParsedPayload extra r payload → ℚᵘ
rawParsedExact word parsed =
  let instance denominatorNonZero = Coordinates.parsedSourceDenominatorNonZero parsed
  in Coordinates.parsedSourceNumerator word parsed
     ℚᵘ./ Coordinates.parsedSourceDenominator parsed

------------------------------------------------------------------------
-- The only case distinction is the signed exponent representation.
------------------------------------------------------------------------

parsedOrdinaryRawFactorization :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  rawParsedExact word parsed ℚᵘ.≃ rawSourceFactorization word parsed
parsedOrdinaryRawFactorization {extra} {r} word parsed
  with Source.exponentIntCode parsed
... | Sem.nonnegative e
  rewrite Weld.exactPow3MatchesBalancedPow3 e
        | Weld.exactPow3MatchesBalancedPow3 (sourceFractionWidth parsed)
        | applySignMulNat
            (Source.signOfWord word)
            (sourceUnsignedSignificandInteger parsed)
            (BT.pow3 e)
        | NatP.*-identityʳ (BT.pow3 (sourceFractionWidth parsed)) =
  ℚᵘ.*≡* refl
... | Sem.negative zero
  rewrite Weld.exactPow3MatchesBalancedPow3 zero
        | Weld.exactPow3MatchesBalancedPow3 (sourceFractionWidth parsed)
        | applySignMulNat
            (Source.signOfWord word)
            (sourceUnsignedSignificandInteger parsed)
            1
        | NatP.*-identityʳ (BT.pow3 (sourceFractionWidth parsed))
        | ℤP.*-identityʳ
            (Exact.applySign (Source.signOfWord word)
              (sourceUnsignedSignificandInteger parsed)) =
  ℚᵘ.*≡* refl
... | Sem.negative (suc e)
  rewrite Weld.exactPow3MatchesBalancedPow3 zero
        | Weld.exactPow3MatchesBalancedPow3
            (suc e + sourceFractionWidth parsed)
        | balancedPow3AddSwap (suc e) (sourceFractionWidth parsed)
        | applySignMulNat
            (Source.signOfWord word)
            (sourceUnsignedSignificandInteger parsed)
            1
        | ℤP.*-identityʳ
            (Exact.applySign (Source.signOfWord word)
              (sourceUnsignedSignificandInteger parsed)) =
  ℚᵘ.*≡* refl

------------------------------------------------------------------------
-- Transport the literal raw product into canonical ℚ without normalisation
-- guesswork.  The proof uses only the standard toℚᵘ multiplication
-- homomorphism and the canonical/raw roundtrip equivalence.
------------------------------------------------------------------------

fromRawProduct :
  (p q : ℚᵘ) →
  ℚ.fromℚᵘ (p ℚᵘ.* q)
  ≡ ℚ.fromℚᵘ p ℚ.* ℚ.fromℚᵘ q
fromRawProduct p q =
  ℚP.toℚᵘ-injective proof
  where
  leftToRaw :
    ℚ.toℚᵘ (ℚ.fromℚᵘ (p ℚᵘ.* q)) ℚᵘ.≃ (p ℚᵘ.* q)
  leftToRaw = ℚP.toℚᵘ-fromℚᵘ (p ℚᵘ.* q)

  pToRaw : ℚ.toℚᵘ (ℚ.fromℚᵘ p) ℚᵘ.≃ p
  pToRaw = ℚP.toℚᵘ-fromℚᵘ p

  qToRaw : ℚ.toℚᵘ (ℚ.fromℚᵘ q) ℚᵘ.≃ q
  qToRaw = ℚP.toℚᵘ-fromℚᵘ q

  factorsToRaw :
    (ℚ.toℚᵘ (ℚ.fromℚᵘ p) ℚᵘ.* ℚ.toℚᵘ (ℚ.fromℚᵘ q))
    ℚᵘ.≃ (p ℚᵘ.* q)
  factorsToRaw = ℚᵘP.*-cong pToRaw qToRaw

  canonicalProductToFactors :
    ℚ.toℚᵘ (ℚ.fromℚᵘ p ℚ.* ℚ.fromℚᵘ q)
    ℚᵘ.≃
    (ℚ.toℚᵘ (ℚ.fromℚᵘ p) ℚᵘ.* ℚ.toℚᵘ (ℚ.fromℚᵘ q))
  canonicalProductToFactors =
    ℚP.toℚᵘ-homo-* (ℚ.fromℚᵘ p) (ℚ.fromℚᵘ q)

  proof :
    ℚ.toℚᵘ (ℚ.fromℚᵘ (p ℚᵘ.* q))
    ℚᵘ.≃
    ℚ.toℚᵘ (ℚ.fromℚᵘ p ℚ.* ℚ.fromℚᵘ q)
  proof =
    ℚᵘP.≃-trans leftToRaw
      (ℚᵘP.≃-trans
        (ℚᵘP.≃-sym factorsToRaw)
        (ℚᵘP.≃-sym canonicalProductToFactors))

canonicalSignedSignificand :
  ∀ {extra r payload} →
  Vec Trit.Trit (8 + extra) →
  Source.ParsedPayload extra r payload → ℚ
canonicalSignedSignificand word parsed =
  ℚ.fromℚᵘ (rawSourceSignificand word parsed)

canonicalSourceScale :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → ℚ
canonicalSourceScale parsed = ℚ.fromℚᵘ (rawSourceScale parsed)

canonicalSourceScaleIsTriadicScale :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  canonicalSourceScale parsed ≡ Scale.triadicScale (sourceExponentInteger parsed)
canonicalSourceScaleIsTriadicScale parsed = refl

parsedOrdinaryAsRawExact :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Source.ordinaryRationalFromParsed word parsed
  ≡ ℚ.fromℚᵘ (rawParsedExact word parsed)
parsedOrdinaryAsRawExact word parsed
  rewrite Coordinates.parsedOrdinaryRationalUsesExactSourceCoordinates word parsed =
  refl

parsedOrdinaryCanonicalFactorization :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Source.ordinaryRationalFromParsed word parsed
  ≡ ℚ.fromℚᵘ (rawSourceFactorization word parsed)
parsedOrdinaryCanonicalFactorization word parsed =
  trans
    (parsedOrdinaryAsRawExact word parsed)
    (ℚP.fromℚᵘ-cong (parsedOrdinaryRawFactorization word parsed))

parsedOrdinaryCanonicalProduct :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Source.ordinaryRationalFromParsed word parsed
  ≡ canonicalSignedSignificand word parsed
      ℚ.* canonicalSourceScale parsed
parsedOrdinaryCanonicalProduct word parsed =
  trans
    (parsedOrdinaryCanonicalFactorization word parsed)
    (fromRawProduct
      (rawSourceSignificand word parsed)
      (rawSourceScale parsed))
