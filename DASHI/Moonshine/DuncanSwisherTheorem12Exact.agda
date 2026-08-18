module DASHI.Moonshine.DuncanSwisherTheorem12Exact where

------------------------------------------------------------------------
-- EXACT SOURCE SHAPE OF DUNCAN--SWISHER THEOREM 1.2
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- For every prime p > 3, Theorem 1.2 gives
--
--   v_p(|M|) = 3 m_p / 2
--     if |S_p^1| = 1 and |S_p^2| = 0,
--
--   v_p(|M|) = m_p / 2
--     if |S_p^1| > 1 and |S_p^2| = 0,
--
--   v_p(|M|) = 0
--     if |S_p^2| > 0.
--
-- DASHI CONTRIBUTION
--
-- Encode the two fractional formulas division-free as
--
--   2*v = 3*m,    2*v = m,
--
-- and derive the support corollary
--
--   1 <= v  <=>  |S_p^2| = 0
--
-- from the exact three-case theorem plus positivity of m_p.  Thus the support
-- theorem used by the Monster/Fricke weld is no longer an independent source
-- premise.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _*_; suc; z≤n; s≤s)
open import Data.Nat.Primality using (Prime)

------------------------------------------------------------------------
-- Exact theorem cases.  `quadraticCount` is |S_p^2|, counting geometric
-- non-rational j-points, not Frobenius pairs.
------------------------------------------------------------------------

data DuncanSwisherTheorem12Case
    (rationalCount quadraticCount minimumAutOrder monsterValuation : Nat) : Set where
  oneRationalNoQuadratic :
    rationalCount ≡ 1 →
    quadraticCount ≡ 0 →
    1 ≤ minimumAutOrder →
    2 * monsterValuation ≡ 3 * minimumAutOrder →
    DuncanSwisherTheorem12Case
      rationalCount quadraticCount minimumAutOrder monsterValuation

  manyRationalNoQuadratic :
    2 ≤ rationalCount →
    quadraticCount ≡ 0 →
    1 ≤ minimumAutOrder →
    2 * monsterValuation ≡ minimumAutOrder →
    DuncanSwisherTheorem12Case
      rationalCount quadraticCount minimumAutOrder monsterValuation

  hasNonRationalSupersingular :
    1 ≤ quadraticCount →
    monsterValuation ≡ 0 →
    DuncanSwisherTheorem12Case
      rationalCount quadraticCount minimumAutOrder monsterValuation

------------------------------------------------------------------------
-- Small constructive positivity lemmas.
------------------------------------------------------------------------

oneLeSuc : (n : Nat) → 1 ≤ suc n
oneLeSuc n = s≤s z≤n

positiveCannotEqualZero :
  (n : Nat) → 1 ≤ n → n ≡ 0 → ⊥
positiveCannotEqualZero 0 () refl
positiveCannotEqualZero (suc n) positive ()

threeTimesPositive :
  (m : Nat) → 1 ≤ m → 1 ≤ 3 * m
threeTimesPositive 0 ()
threeTimesPositive (suc m) positive = oneLeSuc (2 + 3 * m)

positiveFromTwiceEquation :
  (v rhs : Nat) →
  1 ≤ rhs →
  2 * v ≡ rhs →
  1 ≤ v
positiveFromTwiceEquation 0 .0 () refl
positiveFromTwiceEquation (suc v) rhs rhsPositive equation = oneLeSuc v

------------------------------------------------------------------------
-- The exact theorem cases force the support corollary.
------------------------------------------------------------------------

caseNoQuadraticImpliesValuationPositive :
  {r q m v : Nat} →
  DuncanSwisherTheorem12Case r q m v →
  q ≡ 0 →
  1 ≤ v
caseNoQuadraticImpliesValuationPositive
  (oneRationalNoQuadratic rationalOne qZero mPositive twiceEquation)
  qZeroAgain =
  positiveFromTwiceEquation
    _ _
    (threeTimesPositive _ mPositive)
    twiceEquation
caseNoQuadraticImpliesValuationPositive
  (manyRationalNoQuadratic rationalMany qZero mPositive twiceEquation)
  qZeroAgain =
  positiveFromTwiceEquation _ _ mPositive twiceEquation
caseNoQuadraticImpliesValuationPositive
  (hasNonRationalSupersingular qPositive valuationZero)
  qZero =
  ⊥-elim (positiveCannotEqualZero _ qPositive qZero)

caseValuationPositiveImpliesNoQuadratic :
  {r q m v : Nat} →
  DuncanSwisherTheorem12Case r q m v →
  1 ≤ v →
  q ≡ 0
caseValuationPositiveImpliesNoQuadratic
  (oneRationalNoQuadratic rationalOne qZero mPositive twiceEquation)
  valuationPositive = qZero
caseValuationPositiveImpliesNoQuadratic
  (manyRationalNoQuadratic rationalMany qZero mPositive twiceEquation)
  valuationPositive = qZero
caseValuationPositiveImpliesNoQuadratic
  (hasNonRationalSupersingular qPositive valuationZero)
  valuationPositive =
  ⊥-elim (positiveCannotEqualZero _ valuationPositive valuationZero)

caseValuationPositiveIffNoQuadratic :
  {r q m v : Nat} →
  DuncanSwisherTheorem12Case r q m v →
  1 ≤ v ↔ q ≡ 0
caseValuationPositiveIffNoQuadratic theoremCase =
  caseValuationPositiveImpliesNoQuadratic theoremCase
  , caseNoQuadraticImpliesValuationPositive theoremCase

------------------------------------------------------------------------
-- Arbitrary-prime-above-three source package.  Only the exact Theorem 1.2 case
-- remains imported; support is derived above.
------------------------------------------------------------------------

record DuncanSwisherTheorem12Authority
    (p : Nat) (prime : Prime p) : Set where
  field
    rationalSupersingularCount : Nat
    quadraticSupersingularCount : Nat
    minimumSupersingularAutOrder : Nat
    monsterPAdicValuation : Nat

    theorem12 :
      DuncanSwisherTheorem12Case
        rationalSupersingularCount
        quadraticSupersingularCount
        minimumSupersingularAutOrder
        monsterPAdicValuation

open DuncanSwisherTheorem12Authority public

postulate
  publishedDuncanSwisherTheorem12 :
    (p : Nat) → (prime : Prime p) → 5 ≤ p →
    DuncanSwisherTheorem12Authority p prime

publishedValuationPositiveIffNoQuadratic :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  1 ≤ monsterPAdicValuation (publishedDuncanSwisherTheorem12 p prime ge5)
  ↔ quadraticSupersingularCount (publishedDuncanSwisherTheorem12 p prime ge5) ≡ 0
publishedValuationPositiveIffNoQuadratic p prime ge5 =
  caseValuationPositiveIffNoQuadratic
    (theorem12 (publishedDuncanSwisherTheorem12 p prime ge5))

record DuncanSwisherTheorem12Boundary : Set where
  field
    exactThreeCaseTheoremImported : Bool
    fractionalFormulasEncodedDivisionFree : Bool
    minimumAutOrderPositivityCarried : Bool
    supportCorollaryImportedSeparately : Bool
    supportCorollaryDerivedLocally : Bool
    theoremCoversTwoAndThree : Bool

canonicalDuncanSwisherTheorem12Boundary : DuncanSwisherTheorem12Boundary
canonicalDuncanSwisherTheorem12Boundary = record
  { exactThreeCaseTheoremImported = true
  ; fractionalFormulasEncodedDivisionFree = true
  ; minimumAutOrderPositivityCarried = true
  ; supportCorollaryImportedSeparately = false
  ; supportCorollaryDerivedLocally = true
  ; theoremCoversTwoAndThree = false
  }
