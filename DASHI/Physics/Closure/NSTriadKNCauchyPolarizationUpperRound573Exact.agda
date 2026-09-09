module DASHI.Physics.Closure.NSTriadKNCauchyPolarizationUpperRound573Exact where

------------------------------------------------------------------------
-- ROUND573 / FINITE FULL-SQUARE POLARIZATION UPPER BOUND
--
-- The live A1 commutator-only carrier is a mixed Cauchy/Hermitian full square.
-- R446 proves positivity for the same Cauchy kernel on an arbitrary vector
-- family.  Before attaching that theorem to the literal forcing/cell families,
-- isolate the exact finite algebra needed by polarization.
--
-- For pair functions QG,QD,M define
--
--   Delta(a,b) = QG(a,b) + QD(a,b) - M(a,b) - M(b,a).
--
-- Complete-square summation gives
--
--   Full Delta = Full QG + Full QD - 2 Full M,
--
-- since complete finite square summation is invariant under transposition.
-- Hence positivity of Full Delta implies
--
--   2 Full M <= Full QG + Full QD.
--
-- This is only finite rational algebra.  It does NOT claim that the resulting
-- positive QG/QD majorants are analytically cheaper than the original signed
-- mixed form; that adequacy question is the next BIDI audit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504


two573 : ℚ
two573 = 1ℚ + 1ℚ

polarizedPair573 :
  ∀ {A : Set} →
  (A → A → ℚ) → (A → A → ℚ) → (A → A → ℚ) → A → A → ℚ
polarizedPair573 QG QD M a b =
  QG a b + QD a b - M a b - M b a

rowPolarization573 :
  ∀ {A : Set}
    (QG QD M : A → A → ℚ) →
    (x : A) (items : List A) →
  R539.rowSum (polarizedPair573 QG QD M) x items
  ≡ R539.rowSum QG x items + R539.rowSum QD x items
      - R539.rowSum M x items - R539.columnSum M items x
rowPolarization573 QG QD M x [] = refl
rowPolarization573 QG QD M x (y ∷ rest)
  rewrite rowPolarization573 QG QD M x rest =
  solve
    ( QG x y ∷ QD x y ∷ M x y ∷ M y x
    ∷ R539.rowSum QG x rest ∷ R539.rowSum QD x rest
    ∷ R539.rowSum M x rest ∷ R539.columnSum M rest x ∷ [])

columnPolarization573 :
  ∀ {A : Set}
    (QG QD M : A → A → ℚ) →
    (items : List A) (x : A) →
  R539.columnSum (polarizedPair573 QG QD M) items x
  ≡ R539.columnSum QG items x + R539.columnSum QD items x
      - R539.columnSum M items x - R539.rowSum M x items
columnPolarization573 QG QD M [] x = refl
columnPolarization573 QG QD M (y ∷ rest) x
  rewrite columnPolarization573 QG QD M rest x =
  solve
    ( QG y x ∷ QD y x ∷ M y x ∷ M x y
    ∷ R539.columnSum QG rest x ∷ R539.columnSum QD rest x
    ∷ R539.columnSum M rest x ∷ R539.rowSum M x rest ∷ [])

fullSquarePolarization573 :
  ∀ {A : Set}
    (QG QD M : A → A → ℚ) →
    (items : List A) →
  R543.fullSquareSum (polarizedPair573 QG QD M) items
  ≡ R543.fullSquareSum QG items + R543.fullSquareSum QD items
      - two573 * R543.fullSquareSum M items
fullSquarePolarization573 QG QD M [] = refl
fullSquarePolarization573 QG QD M (x ∷ rest)
  rewrite rowPolarization573 QG QD M x rest
        | columnPolarization573 QG QD M rest x
        | fullSquarePolarization573 QG QD M rest =
  solve
    ( QG x x ∷ QD x x ∷ M x x
    ∷ R539.rowSum QG x rest ∷ R539.columnSum QG rest x
    ∷ R539.rowSum QD x rest ∷ R539.columnSum QD rest x
    ∷ R539.rowSum M x rest ∷ R539.columnSum M rest x
    ∷ R543.fullSquareSum QG rest ∷ R543.fullSquareSum QD rest
    ∷ R543.fullSquareSum M rest ∷ [])

polarizationUpper573 :
  ∀ {A : Set}
    (QG QD M : A → A → ℚ) →
    (items : List A) →
  0ℚ ≤ R543.fullSquareSum (polarizedPair573 QG QD M) items →
  two573 * R543.fullSquareSum M items
  ≤ R543.fullSquareSum QG items + R543.fullSquareSum QD items
polarizationUpper573 QG QD M items deltaNN =
  let
    mixed = two573 * R543.fullSquareSum M items
    sumQ = R543.fullSquareSum QG items + R543.fullSquareSum QD items

    shifted : mixed + 0ℚ ≤ mixed +
      R543.fullSquareSum (polarizedPair573 QG QD M) items
    shifted = ℚP.+-monoʳ-≤ mixed deltaNN

    rhsExact :
      mixed + R543.fullSquareSum (polarizedPair573 QG QD M) items
      ≡ sumQ
    rhsExact rewrite fullSquarePolarization573 QG QD M items =
      solve
        ( R543.fullSquareSum QG items
        ∷ R543.fullSquareSum QD items
        ∷ R543.fullSquareSum M items ∷ [])
  in
  subst
    (λ rhs → mixed ≤ rhs)
    rhsExact
    (subst
      (λ lhs → lhs ≤ mixed +
        R543.fullSquareSum (polarizedPair573 QG QD M) items)
      (ℚP.+-identityʳ mixed)
      shifted)

round573FiniteFullSquarePolarizationClosed : Bool
round573FiniteFullSquarePolarizationClosed = true

round573NeedsOnlyDifferenceFormNonnegativity : Bool
round573NeedsOnlyDifferenceFormNonnegativity = true

round573ClaimsPositiveMajorantsAreAnalyticallyCheaper : Bool
round573ClaimsPositiveMajorantsAreAnalyticallyCheaper = false

round573IntroducesAbsoluteValue : Bool
round573IntroducesAbsoluteValue = false

round573CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round573CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round573ClayPromotion : Bool
round573ClayPromotion = false

round573ClayPromotionIsFalse : round573ClayPromotion ≡ false
round573ClayPromotionIsFalse = refl
