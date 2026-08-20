module DASHI.Physics.Closure.NSTriadKNComFiniteNormalizedGramUnitBoundRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz / Gram inequality; no DOI assigned to the
-- original nineteenth-century sources.
--
-- Roger A. Horn; Charles R. Johnson.
-- Title: "Matrix Analysis", second edition.
-- DOI: 10.1017/CBO9781139020411.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 63 B1.5 CONSTRUCTION
--
-- Round63 first proves that the old generic `GramInterferenceCell` does not by
-- itself normalize overlap.  Here we construct the normalization on the repo's
-- exact finite rational Gram carrier.
--
-- For a finite pair family with positive product mass
--
--   M = ||a||^2 ||b||^2 > 0,
--
-- define
--
--   rho = <a,b>^2 / M.
--
-- The already-proved exact finite Gram identity
--
--   M = <a,b>^2 + defect,
--
-- gives both
--
--   0 <= rho <= 1
--
-- and the exact equality characterization
--
--   rho = 1  <=>  defect = 0.
--
-- This is a concrete certificate-level normalization theorem, not yet the
-- missing same-object physical Fourier realization.  B1 must identify the
-- literal localized physical Gram with this mathematical normalization pattern
-- (or prove the analogous theorem directly in its ordered physical carrier).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; 1/_; Positive; NonNegative; NonZero)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

normProduct : List L2.Pair → ℚ
normProduct pairs = L2.leftNormSquared pairs * L2.rightNormSquared pairs

record PositiveFiniteGramMass (pairs : List L2.Pair) : Set where
  constructor positive-finite-gram-mass
  field
    productPositive : 0ℚ < normProduct pairs

open PositiveFiniteGramMass public

positiveReciprocal :
  (denominator : ℚ) → 0ℚ < denominator → ℚ
positiveReciprocal denominator denominatorPositive =
  let
    instance
      denominatorIsPositive : Positive denominator
      denominatorIsPositive = ℚ.positive denominatorPositive
      denominatorIsNonzero : NonZero denominator
      denominatorIsNonzero = ℚP.pos⇒nonZero denominator
  in
  1/ denominator

positiveReciprocalRightInverse :
  (denominator : ℚ) →
  (denominatorPositive : 0ℚ < denominator) →
  denominator * positiveReciprocal denominator denominatorPositive ≡ 1ℚ
positiveReciprocalRightInverse denominator denominatorPositive =
  let
    instance
      denominatorIsPositive : Positive denominator
      denominatorIsPositive = ℚ.positive denominatorPositive
      denominatorIsNonzero : NonZero denominator
      denominatorIsNonzero = ℚP.pos⇒nonZero denominator
  in
  ℚP.*-inverseʳ denominator

positiveReciprocalPositive :
  (denominator : ℚ) →
  (denominatorPositive : 0ℚ < denominator) →
  0ℚ < positiveReciprocal denominator denominatorPositive
positiveReciprocalPositive denominator denominatorPositive =
  let
    instance
      denominatorIsPositive : Positive denominator
      denominatorIsPositive = ℚ.positive denominatorPositive
      denominatorIsNonzero : NonZero denominator
      denominatorIsNonzero = ℚP.pos⇒nonZero denominator
      reciprocalIsPositive : Positive (1/ denominator)
      reciprocalIsPositive = ℚP.1/pos⇒pos denominator
  in
  ℚP.positive⁻¹ (1/ denominator)

normalizedOverlap :
  (pairs : List L2.Pair) →
  PositiveFiniteGramMass pairs → ℚ
normalizedOverlap pairs positiveMass =
  L2.square (L2.pairDot pairs)
  * positiveReciprocal (normProduct pairs) (productPositive positiveMass)

normalizedOverlapNonnegative :
  (pairs : List L2.Pair) →
  (positiveMass : PositiveFiniteGramMass pairs) →
  0ℚ ≤ normalizedOverlap pairs positiveMass
normalizedOverlapNonnegative pairs positiveMass =
  let
    numerator = L2.square (L2.pairDot pairs)
    reciprocal = positiveReciprocal (normProduct pairs) (productPositive positiveMass)
    instance
      numeratorNN : NonNegative numerator
      numeratorNN = ℚ.nonNegative (L2.squareNonnegative (L2.pairDot pairs))
      reciprocalNN : NonNegative reciprocal
      reciprocalNN = ℚ.nonNegative
        (ℚP.<⇒≤
          (positiveReciprocalPositive
            (normProduct pairs) (productPositive positiveMass)))
      productNN : NonNegative (numerator * reciprocal)
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg numerator reciprocal
  in
  ℚP.nonNegative⁻¹ (normalizedOverlap pairs positiveMass)

normalizedOverlapAtMostOne :
  (pairs : List L2.Pair) →
  (positiveMass : PositiveFiniteGramMass pairs) →
  normalizedOverlap pairs positiveMass ≤ 1ℚ
normalizedOverlapAtMostOne pairs positiveMass =
  let
    mass = normProduct pairs
    numerator = L2.square (L2.pairDot pairs)
    reciprocal = positiveReciprocal mass (productPositive positiveMass)

    instance
      reciprocalNN : NonNegative reciprocal
      reciprocalNN = ℚ.nonNegative
        (ℚP.<⇒≤
          (positiveReciprocalPositive mass (productPositive positiveMass)))

    scaled : numerator * reciprocal ≤ mass * reciprocal
    scaled = ℚP.*-monoʳ-≤-nonNeg reciprocal (L2.finiteCauchySchwarzSquared pairs)

    endpoint : mass * reciprocal ≡ 1ℚ
    endpoint = positiveReciprocalRightInverse mass (productPositive positiveMass)
  in
  subst
    (λ upper → normalizedOverlap pairs positiveMass ≤ upper)
    endpoint
    scaled

normalizedOverlapDefectIdentity :
  (pairs : List L2.Pair) →
  (positiveMass : PositiveFiniteGramMass pairs) →
  1ℚ - normalizedOverlap pairs positiveMass
  ≡ L2.gramDefect pairs
      * positiveReciprocal (normProduct pairs) (productPositive positiveMass)
normalizedOverlapDefectIdentity pairs positiveMass =
  let
    mass = normProduct pairs
    numerator = L2.square (L2.pairDot pairs)
    defect = L2.gramDefect pairs
    reciprocal = positiveReciprocal mass (productPositive positiveMass)

    oneAsMassOverMass : 1ℚ ≡ mass * reciprocal
    oneAsMassOverMass = sym
      (positiveReciprocalRightInverse mass (productPositive positiveMass))

    gram : mass ≡ numerator + defect
    gram = L2.finiteGramIdentity pairs
  in
  trans
    (cong (λ one → one - numerator * reciprocal) oneAsMassOverMass)
    (trans
      (cong (λ selected → selected * reciprocal - numerator * reciprocal) gram)
      (solve (numerator ∷ defect ∷ reciprocal ∷ [])))

normalizedOverlapOneImpliesZeroDefect :
  (pairs : List L2.Pair) →
  (positiveMass : PositiveFiniteGramMass pairs) →
  normalizedOverlap pairs positiveMass ≡ 1ℚ →
  L2.gramDefect pairs ≡ 0ℚ
normalizedOverlapOneImpliesZeroDefect pairs positiveMass overlapOne =
  let
    mass = normProduct pairs
    numerator = L2.square (L2.pairDot pairs)
    reciprocal = positiveReciprocal mass (productPositive positiveMass)

    numeratorOverMassOne : numerator * reciprocal ≡ 1ℚ
    numeratorOverMassOne = overlapOne

    multiplyByMass :
      mass * (numerator * reciprocal) ≡ mass * 1ℚ
    multiplyByMass = cong (mass *_) numeratorOverMassOne

    numeratorExactMass : numerator ≡ mass
    numeratorExactMass =
      let
        leftMeaning : mass * (numerator * reciprocal) ≡ numerator
        leftMeaning =
          trans
            (solve (mass ∷ numerator ∷ reciprocal ∷ []))
            (trans
              (cong (numerator *_)
                (positiveReciprocalRightInverse mass (productPositive positiveMass)))
              (solve (numerator ∷ [])))
        rightMeaning : mass * 1ℚ ≡ mass
        rightMeaning = ℚP.*-identityʳ mass
      in
      trans (sym leftMeaning) (trans multiplyByMass rightMeaning)

    gram : mass ≡ numerator + L2.gramDefect pairs
    gram = L2.finiteGramIdentity pairs

    defectEquation : numerator ≡ numerator + L2.gramDefect pairs
    defectEquation = trans numeratorExactMass gram
  in
  let
    shifted = cong (λ value → value - numerator) defectEquation
    leftMeaning : numerator - numerator ≡ 0ℚ
    leftMeaning = solve (numerator ∷ [])
    rightMeaning :
      (numerator + L2.gramDefect pairs) - numerator
      ≡ L2.gramDefect pairs
    rightMeaning = solve (numerator ∷ L2.gramDefect pairs ∷ [])
  in
  trans (sym rightMeaning) (trans (sym shifted) leftMeaning)

zeroDefectImpliesNormalizedOverlapOne :
  (pairs : List L2.Pair) →
  (positiveMass : PositiveFiniteGramMass pairs) →
  L2.gramDefect pairs ≡ 0ℚ →
  normalizedOverlap pairs positiveMass ≡ 1ℚ
zeroDefectImpliesNormalizedOverlapOne pairs positiveMass defectZero =
  let
    mass = normProduct pairs
    numerator = L2.square (L2.pairDot pairs)
    reciprocal = positiveReciprocal mass (productPositive positiveMass)

    gram : mass ≡ numerator + L2.gramDefect pairs
    gram = L2.finiteGramIdentity pairs

    massIsNumerator : mass ≡ numerator
    massIsNumerator =
      trans gram
        (trans
          (cong (numerator +_) defectZero)
          (ℚP.+-identityʳ numerator))

    normalizedMeaning : numerator * reciprocal ≡ mass * reciprocal
    normalizedMeaning = cong (_* reciprocal) (sym massIsNumerator)
  in
  trans normalizedMeaning
    (positiveReciprocalRightInverse mass (productPositive positiveMass))

finiteNormalizedGramUnitBoundClosed : Bool
finiteNormalizedGramUnitBoundClosed = true

finiteNormalizedGramEqualityCharacterizedByZeroDefect : Bool
finiteNormalizedGramEqualityCharacterizedByZeroDefect = true

finiteNormalizedGramUnitBoundClosedIsTrue :
  finiteNormalizedGramUnitBoundClosed ≡ true
finiteNormalizedGramUnitBoundClosedIsTrue = refl

finiteNormalizedGramEqualityCharacterizedByZeroDefectIsTrue :
  finiteNormalizedGramEqualityCharacterizedByZeroDefect ≡ true
finiteNormalizedGramEqualityCharacterizedByZeroDefectIsTrue = refl
