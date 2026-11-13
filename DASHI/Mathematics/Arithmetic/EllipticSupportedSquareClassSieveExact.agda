module DASHI.Mathematics.Arithmetic.EllipticSupportedSquareClassSieveExact where

------------------------------------------------------------------------
-- BSD E : y² = x³ - x : ORIGINAL FINITE 16 → 8 → 4 CODE CUT
--
-- This module does NOT identify finite codes with all E[2]-valued H¹
-- classes or with the actual Selmer group. It proves the finite,
-- decidable reduction, in the same sign/v₂ coordinate convention as
-- the literal Agda torsion Kummer dictionary:
--
--   first sign = second sign   (real necessary condition)
--   first v₂ parity = 0        (dyadic necessary condition)
--
-- The four remaining supported codes agree exactly with the
-- ORIGINAL y²=x³-x rational torsion representatives
--   O : ( 1, 1), (0,0) : (-1,-1),
--   (1,0) : (1, 2), (-1,0) : (-1,-2).
--
-- Open original-carrier producers:
--  (1) actual rational square-class sign and v₂ bit invariants,
--  (2) proof of good-prime square-class support of genuine Selmer H¹,
--  (3) real and Q₂ local Kummer image ⇒ these two code constraints,
--  (4) original H¹/Selmer ↔ square-class same-object identification.
--
-- This is a finite combinatorial theorem, NOT an assertion that
-- those local/global producers are inhabited.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact as Torsion
import DASHI.Mathematics.Arithmetic.EllipticCurveFiniteTwoDescentSeedExact as Seed
import DASHI.Mathematics.Arithmetic.EllipticRationalKummerOpenExact as Kummer
import DASHI.Mathematics.Arithmetic.EllipticRationalTwoTorsionKummerExact as TorsionKummer
import DASHI.Mathematics.Arithmetic.RationalSquareClassBitInvariantExact as BitInvariant

record SupportedSquareClassPairCode : Set where
  constructor supportedPair
  field
    firstNegative : Torsion.Bit
    firstOddAtTwo : Torsion.Bit
    secondNegative : Torsion.Bit
    secondOddAtTwo : Torsion.Bit

open SupportedSquareClassPairCode public

supportedPairExtensionality :
  ∀ {left right : SupportedSquareClassPairCode} →
  firstNegative left ≡ firstNegative right →
  firstOddAtTwo left ≡ firstOddAtTwo right →
  secondNegative left ≡ secondNegative right →
  secondOddAtTwo left ≡ secondOddAtTwo right →
  left ≡ right
supportedPairExtensionality
    {supportedPair _ _ _ _} {supportedPair _ _ _ _}
    refl refl refl refl = refl

-- The two finite necessary conditions. The signs are DIAGONAL;
-- neither sign is required to be positive.
record RealAndDyadicNecessaryFilter
    (code : SupportedSquareClassPairCode) : Set where
  constructor filtered
  field
    realSignsEqual :
      firstNegative code ≡ secondNegative code
    evenFirstTwoValuation :
      firstOddAtTwo code ≡ Torsion.bit0

open RealAndDyadicNecessaryFilter public

torsionSupportedCode :
  Torsion.TwoTorsionCode → SupportedSquareClassPairCode
torsionSupportedCode (Torsion.torsionCode negative secondParity) =
  supportedPair negative Torsion.bit0 negative secondParity

torsionCodesPassFilter :
  (code : Torsion.TwoTorsionCode) →
  RealAndDyadicNecessaryFilter (torsionSupportedCode code)
torsionCodesPassFilter (Torsion.torsionCode _ _) =
  filtered refl refl

-- A complete finite proof, by dependent equality elimination.
-- This is NOT a proof about Q₂ points unless the original
-- valuations/square-class realization is independently provided.
filteredSupportedCodeHasTorsionPreimage :
  (code : SupportedSquareClassPairCode) →
  RealAndDyadicNecessaryFilter code →
  Σ Torsion.TwoTorsionCode
    (λ torsion → torsionSupportedCode torsion ≡ code)
filteredSupportedCodeHasTorsionPreimage
    (supportedPair first parity second remaining)
    (filtered equalSigns evenFirst)
    rewrite equalSigns | evenFirst =
  Torsion.torsionCode second remaining , refl

-- The actual finite C₂ × C₂ seed of this recovered original torsion
-- point is read from the ALREADY-PROVED finiteKummerMap.
filteredSupportedCodeRecoversFiniteSeed :
  (code : SupportedSquareClassPairCode) →
  RealAndDyadicNecessaryFilter code →
  Σ Torsion.TwoTorsionCode
    (λ torsion →
      Seed.finiteKummerMap torsion
      ≡ Seed.squareClassPair
          (firstNegative code) (secondOddAtTwo code))
filteredSupportedCodeRecoversFiniteSeed
    (supportedPair first parity second remaining)
    (filtered equalSigns evenFirst)
    rewrite equalSigns | evenFirst =
  Torsion.torsionCode second remaining , refl

-- No new "torsion" dictionary: these are the original four literal
-- images, using the rational pair conventions in the Agda owner.
infinitySupportedCode :
  torsionSupportedCode Torsion.pointAtInfinityCode
  ≡ supportedPair Torsion.bit0 Torsion.bit0
      Torsion.bit0 Torsion.bit0
infinitySupportedCode = refl

zeroSupportedCode :
  torsionSupportedCode Torsion.pointZeroCode
  ≡ supportedPair Torsion.bit1 Torsion.bit0
      Torsion.bit1 Torsion.bit0
zeroSupportedCode = refl

oneSupportedCode :
  torsionSupportedCode Torsion.pointOneCode
  ≡ supportedPair Torsion.bit0 Torsion.bit0
      Torsion.bit0 Torsion.bit1
oneSupportedCode = refl

minusOneSupportedCode :
  torsionSupportedCode Torsion.pointMinusOneCode
  ≡ supportedPair Torsion.bit1 Torsion.bit0
      Torsion.bit1 Torsion.bit1
minusOneSupportedCode = refl

-- Exact finite cardinality ledger. The lists are explicit finite
-- candidates, not a setoid quotient of the original H¹.
allSupportedPairs : List SupportedSquareClassPairCode
allSupportedPairs =
  supportedPair Torsion.bit0 Torsion.bit0 Torsion.bit0 Torsion.bit0 ∷
  supportedPair Torsion.bit0 Torsion.bit0 Torsion.bit0 Torsion.bit1 ∷
  supportedPair Torsion.bit0 Torsion.bit0 Torsion.bit1 Torsion.bit0 ∷
  supportedPair Torsion.bit0 Torsion.bit0 Torsion.bit1 Torsion.bit1 ∷
  supportedPair Torsion.bit0 Torsion.bit1 Torsion.bit0 Torsion.bit0 ∷
  supportedPair Torsion.bit0 Torsion.bit1 Torsion.bit0 Torsion.bit1 ∷
  supportedPair Torsion.bit0 Torsion.bit1 Torsion.bit1 Torsion.bit0 ∷
  supportedPair Torsion.bit0 Torsion.bit1 Torsion.bit1 Torsion.bit1 ∷
  supportedPair Torsion.bit1 Torsion.bit0 Torsion.bit0 Torsion.bit0 ∷
  supportedPair Torsion.bit1 Torsion.bit0 Torsion.bit0 Torsion.bit1 ∷
  supportedPair Torsion.bit1 Torsion.bit0 Torsion.bit1 Torsion.bit0 ∷
  supportedPair Torsion.bit1 Torsion.bit0 Torsion.bit1 Torsion.bit1 ∷
  supportedPair Torsion.bit1 Torsion.bit1 Torsion.bit0 Torsion.bit0 ∷
  supportedPair Torsion.bit1 Torsion.bit1 Torsion.bit0 Torsion.bit1 ∷
  supportedPair Torsion.bit1 Torsion.bit1 Torsion.bit1 Torsion.bit0 ∷
  supportedPair Torsion.bit1 Torsion.bit1 Torsion.bit1 Torsion.bit1 ∷
  []

realDiagonalPairs : List SupportedSquareClassPairCode
realDiagonalPairs =
  supportedPair Torsion.bit0 Torsion.bit0 Torsion.bit0 Torsion.bit0 ∷
  supportedPair Torsion.bit0 Torsion.bit0 Torsion.bit0 Torsion.bit1 ∷
  supportedPair Torsion.bit0 Torsion.bit1 Torsion.bit0 Torsion.bit0 ∷
  supportedPair Torsion.bit0 Torsion.bit1 Torsion.bit0 Torsion.bit1 ∷
  supportedPair Torsion.bit1 Torsion.bit0 Torsion.bit1 Torsion.bit0 ∷
  supportedPair Torsion.bit1 Torsion.bit0 Torsion.bit1 Torsion.bit1 ∷
  supportedPair Torsion.bit1 Torsion.bit1 Torsion.bit1 Torsion.bit0 ∷
  supportedPair Torsion.bit1 Torsion.bit1 Torsion.bit1 Torsion.bit1 ∷
  []

torsionSievePairs : List SupportedSquareClassPairCode
torsionSievePairs =
  torsionSupportedCode Torsion.pointAtInfinityCode ∷
  torsionSupportedCode Torsion.pointZeroCode ∷
  torsionSupportedCode Torsion.pointOneCode ∷
  torsionSupportedCode Torsion.pointMinusOneCode ∷
  []

allSupportedPairsCount : length allSupportedPairs ≡ 16
allSupportedPairsCount = refl

realDiagonalPairsCount : length realDiagonalPairs ≡ 8
realDiagonalPairsCount = refl

torsionSievePairsCount : length torsionSievePairs ≡ 4
torsionSievePairsCount = refl

------------------------------------------------------------------------
-- SOURCE-PRESERVING FOUR-INVARIANT PROJECTION ON ORIGINAL RATIONAL
-- SQUARE-CLASS REPRESENTATIVES; NOT AN INVENTED NEW QUOTIENT.
------------------------------------------------------------------------

record OriginalFourBitProjection : Set₁ where
  field
    firstSign : BitInvariant.SquareClassBitInvariant
    firstV2Parity : BitInvariant.SquareClassBitInvariant
    secondSign : BitInvariant.SquareClassBitInvariant
    secondV2Parity : BitInvariant.SquareClassBitInvariant

open OriginalFourBitProjection public

projectOriginalSquareClassPair :
  OriginalFourBitProjection →
  Kummer.RationalSquareClassPairRepresentative →
  SupportedSquareClassPairCode
projectOriginalSquareClassPair projection pair =
  supportedPair
    (BitInvariant.classify
      (firstSign projection) (Kummer.first pair))
    (BitInvariant.classify
      (firstV2Parity projection) (Kummer.first pair))
    (BitInvariant.classify
      (secondSign projection) (Kummer.second pair))
    (BitInvariant.classify
      (secondV2Parity projection) (Kummer.second pair))

-- Proven for ANY four genuine generator-invariant classifiers.
-- Their actual sign/v₂ arithmetic definitions are still K1 owners.
originalPairSquareEquivalencePreservesAllFourBits :
  (projection : OriginalFourBitProjection) →
  ∀ {left right} →
  Kummer.RationalSquareClassPairEquivalent left right →
  projectOriginalSquareClassPair projection left
  ≡ projectOriginalSquareClassPair projection right
originalPairSquareEquivalencePreservesAllFourBits
    projection (Kummer.pair-equivalent firstEq secondEq) =
  supportedPairExtensionality
    (BitInvariant.squareEquivalentPreservesInvariant
      (firstSign projection) firstEq)
    (BitInvariant.squareEquivalentPreservesInvariant
      (firstV2Parity projection) firstEq)
    (BitInvariant.squareEquivalentPreservesInvariant
      (secondSign projection) secondEq)
    (BitInvariant.squareEquivalentPreservesInvariant
      (secondV2Parity projection) secondEq)

-- The exact calibration of the four ORIGINAL literal torsion pair
-- representatives is a named dependency, not a fake completed gate.
torsionDictionaryCalibrationGivesFilter :
  (projection : OriginalFourBitProjection) →
  ((code : Torsion.TwoTorsionCode) →
    projectOriginalSquareClassPair projection
      (TorsionKummer.torsionKummerRepresentative code)
    ≡ torsionSupportedCode code) →
  (code : Torsion.TwoTorsionCode) →
  RealAndDyadicNecessaryFilter
    (projectOriginalSquareClassPair projection
      (TorsionKummer.torsionKummerRepresentative code))
torsionDictionaryCalibrationGivesFilter
    projection calibrate code
    rewrite calibrate code =
  torsionCodesPassFilter code

------------------------------------------------------------------------
-- Proof-relevant list coverage, not merely a declaration of counts.
------------------------------------------------------------------------

infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

torsionSupportedCodeOccurs :
  (torsion : Torsion.TwoTorsionCode) →
  torsionSupportedCode torsion ∈ torsionSievePairs
torsionSupportedCodeOccurs
    (Torsion.torsionCode Torsion.bit0 Torsion.bit0) =
  here
torsionSupportedCodeOccurs
    (Torsion.torsionCode Torsion.bit1 Torsion.bit0) =
  there here
torsionSupportedCodeOccurs
    (Torsion.torsionCode Torsion.bit0 Torsion.bit1) =
  there (there here)
torsionSupportedCodeOccurs
    (Torsion.torsionCode Torsion.bit1 Torsion.bit1) =
  there (there (there here))

-- No hidden completeness premise: every code satisfying the
-- two exact finite filters occurs in the ORIGINAL torsion table.
filteredSupportedPairOccursInTorsionTable :
  (code : SupportedSquareClassPairCode) →
  RealAndDyadicNecessaryFilter code →
  code ∈ torsionSievePairs
filteredSupportedPairOccursInTorsionTable code filter
  with filteredSupportedCodeHasTorsionPreimage code filter
... | torsion , equality rewrite sym equality =
  torsionSupportedCodeOccurs torsion

-- An explicit proof of COVERAGE for the 16-element list, rather
-- than inferring exhaustiveness from its length alone.
allSupportedPairsExhaustive :
  (a b c d : Torsion.Bit) →
  supportedPair a b c d ∈ allSupportedPairs
allSupportedPairsExhaustive Torsion.bit0 Torsion.bit0 Torsion.bit0 Torsion.bit0 =
  here
allSupportedPairsExhaustive Torsion.bit0 Torsion.bit0 Torsion.bit0 Torsion.bit1 =
  there (here)
allSupportedPairsExhaustive Torsion.bit0 Torsion.bit0 Torsion.bit1 Torsion.bit0 =
  there (there (here))
allSupportedPairsExhaustive Torsion.bit0 Torsion.bit0 Torsion.bit1 Torsion.bit1 =
  there (there (there (here)))
allSupportedPairsExhaustive Torsion.bit0 Torsion.bit1 Torsion.bit0 Torsion.bit0 =
  there (there (there (there (here))))
allSupportedPairsExhaustive Torsion.bit0 Torsion.bit1 Torsion.bit0 Torsion.bit1 =
  there (there (there (there (there (here)))))
allSupportedPairsExhaustive Torsion.bit0 Torsion.bit1 Torsion.bit1 Torsion.bit0 =
  there (there (there (there (there (there (here))))))
allSupportedPairsExhaustive Torsion.bit0 Torsion.bit1 Torsion.bit1 Torsion.bit1 =
  there (there (there (there (there (there (there (here)))))))
allSupportedPairsExhaustive Torsion.bit1 Torsion.bit0 Torsion.bit0 Torsion.bit0 =
  there (there (there (there (there (there (there (there (here))))))))
allSupportedPairsExhaustive Torsion.bit1 Torsion.bit0 Torsion.bit0 Torsion.bit1 =
  there (there (there (there (there (there (there (there (there (here)))))))))
allSupportedPairsExhaustive Torsion.bit1 Torsion.bit0 Torsion.bit1 Torsion.bit0 =
  there (there (there (there (there (there (there (there (there (there (here))))))))))
allSupportedPairsExhaustive Torsion.bit1 Torsion.bit0 Torsion.bit1 Torsion.bit1 =
  there (there (there (there (there (there (there (there (there (there (there (here)))))))))))
allSupportedPairsExhaustive Torsion.bit1 Torsion.bit1 Torsion.bit0 Torsion.bit0 =
  there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))
allSupportedPairsExhaustive Torsion.bit1 Torsion.bit1 Torsion.bit0 Torsion.bit1 =
  there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))
allSupportedPairsExhaustive Torsion.bit1 Torsion.bit1 Torsion.bit1 Torsion.bit0 =
  there (there (there (there (there (there (there (there (there (there (there (there (there (there (here))))))))))))))
allSupportedPairsExhaustive Torsion.bit1 Torsion.bit1 Torsion.bit1 Torsion.bit1 =
  there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here)))))))))))))))

-- Exactly the diagonal-sign 8-element real-necessary slice.
realDiagonalPairsExhaustive :
  (code : SupportedSquareClassPairCode) →
  firstNegative code ≡ secondNegative code →
  code ∈ realDiagonalPairs
realDiagonalPairsExhaustive
    (supportedPair Torsion.bit0 Torsion.bit0 Torsion.bit0 Torsion.bit0) refl =
  here
realDiagonalPairsExhaustive
    (supportedPair Torsion.bit0 Torsion.bit0 Torsion.bit0 Torsion.bit1) refl =
  there (here)
realDiagonalPairsExhaustive
    (supportedPair Torsion.bit0 Torsion.bit1 Torsion.bit0 Torsion.bit0) refl =
  there (there (here))
realDiagonalPairsExhaustive
    (supportedPair Torsion.bit0 Torsion.bit1 Torsion.bit0 Torsion.bit1) refl =
  there (there (there (here)))
realDiagonalPairsExhaustive
    (supportedPair Torsion.bit1 Torsion.bit0 Torsion.bit1 Torsion.bit0) refl =
  there (there (there (there (here))))
realDiagonalPairsExhaustive
    (supportedPair Torsion.bit1 Torsion.bit0 Torsion.bit1 Torsion.bit1) refl =
  there (there (there (there (there (here)))))
realDiagonalPairsExhaustive
    (supportedPair Torsion.bit1 Torsion.bit1 Torsion.bit1 Torsion.bit0) refl =
  there (there (there (there (there (there (here))))))
realDiagonalPairsExhaustive
    (supportedPair Torsion.bit1 Torsion.bit1 Torsion.bit1 Torsion.bit1) refl =
  there (there (there (there (there (there (there (here)))))))
realDiagonalPairsExhaustive
    (supportedPair Torsion.bit0 _ Torsion.bit1 _) ()
realDiagonalPairsExhaustive
    (supportedPair Torsion.bit1 _ Torsion.bit0 _) ()
