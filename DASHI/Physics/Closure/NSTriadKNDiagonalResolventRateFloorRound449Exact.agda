module DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact where

------------------------------------------------------------------------
-- ROUND449 / POSITIVE CELL-RATE FLOOR -> R298 DIAGONAL RESOLVENT CEILING
--
-- R447 reduces the endpoint to a positive full Cauchy form.  Its diagonal
-- cell at rate rho carries the literal weight
--
--                 K(rho,rho) = 1 / (rho + rho).
--
-- R298 only needs a cutoff-independent ceiling for these weights.  This file
-- proves the generic ordered-rational compiler:
--
--       0 < floor <= rho
--       -------------------------------
--       K(rho,rho) <= 1 / (2 floor).
--
-- The reciprocal antitonicity theorem is reused from the Yang--Mills interval
-- arithmetic lane.  No Fourier normalization is assumed here; a physical
-- consumer must separately prove the requested cell-rate floor on its exact
-- carrier.  The ceiling is proof-indexed: there is no proof-free reciprocal
-- of a putatively positive floor and no hidden positivity postulate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _+_; _*_; _≤_; _<_; _≟_; positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary using (yes; no)

import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact as R443
import DASHI.Physics.Closure.NSTriadKNResolventDiagonalNoCardinalityRound298Exact as R298
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

two : ℚ
two = 1ℚ + 1ℚ

twoPositive : 0ℚ < two
twoPositive =
  ℚP.+-mono-<-< (ℚP.positive⁻¹ 1ℚ) (ℚP.positive⁻¹ 1ℚ)

twicePositive :
  ∀ {x : ℚ} → 0ℚ < x → 0ℚ < two * x
twicePositive {x} xPositive =
  let
    instance
      twoPositiveI : Positive two
      twoPositiveI = positive twoPositive
      xPositiveI : Positive x
      xPositiveI = positive xPositive
      productPositiveI = ℚP.pos*pos⇒pos two x
  in
  ℚP.positive⁻¹ (two * x)

twiceMonotone :
  ∀ {lower upper : ℚ} → lower ≤ upper → two * lower ≤ two * upper
twiceMonotone {lower} {upper} lowerBelowUpper =
  let
    instance twoNNI : NonNegative two
    twoNNI = nonNegative (ℚP.<⇒≤ twoPositive)
  in
  ℚP.*-monoˡ-≤-nonNeg two lowerBelowUpper

safeReciprocalIsPositiveReciprocal :
  ∀ value (valuePositive : 0ℚ < value) →
  Reciprocal.safeRationalReciprocal value
  ≡ Quotient.positiveReciprocal value valuePositive
safeReciprocalIsPositiveReciprocal value valuePositive with value ≟ 0ℚ
... | yes valueZero =
  Reciprocal.emptyEliminate
    (Reciprocal.positiveZeroImpossible
      (subst Positive valueZero (positive valuePositive)))
... | no valueNonzero = refl

record DiagonalRateFloorCell (floor : ℚ) : Set where
  constructor diagonal-rate-floor-cell
  field
    rate mass : ℚ
    ratePositive : 0ℚ < rate
    floorBelowRate : floor ≤ rate
    massNonnegative : 0ℚ ≤ mass

open DiagonalRateFloorCell public

diagonalWeight : ∀ {floor} → DiagonalRateFloorCell floor → ℚ
diagonalWeight cell = R443.cauchyEntry (rate cell) (rate cell)

diagonalCeilingAt :
  (floor : ℚ) → 0ℚ < floor → ℚ
diagonalCeilingAt floor floorPositive =
  Quotient.positiveReciprocal (two * floor)
    (twicePositive floorPositive)

diagonalWeightBelowFloorCeiling :
  ∀ {floor} →
  (floorPositive : 0ℚ < floor) →
  (cell : DiagonalRateFloorCell floor) →
  diagonalWeight cell ≤ diagonalCeilingAt floor floorPositive
diagonalWeightBelowFloorCeiling {floor} floorPositive cell =
  let
    rho = rate cell
    rhoPositive = ratePositive cell
    sumRhoPositive : 0ℚ < rho + rho
    sumRhoPositive = ℚP.+-mono-<-< rhoPositive rhoPositive
    twoFloorPositive = twicePositive floorPositive
    twoRhoPositive = twicePositive rhoPositive
    twoFloorBelowTwoRho = twiceMonotone (floorBelowRate cell)

    rhoPlusRhoIsTwoRho : rho + rho ≡ two * rho
    rhoPlusRhoIsTwoRho = solve (rho ∷ [])

    cauchyAsPositiveReciprocal :
      diagonalWeight cell
      ≡ Quotient.positiveReciprocal (rho + rho) sumRhoPositive
    cauchyAsPositiveReciprocal =
      safeReciprocalIsPositiveReciprocal (rho + rho) sumRhoPositive

    reciprocalTransport :
      Quotient.positiveReciprocal (rho + rho) sumRhoPositive
      ≡ Quotient.positiveReciprocal (two * rho) twoRhoPositive
    reciprocalTransport rewrite rhoPlusRhoIsTwoRho = refl

    antitone :
      Quotient.positiveReciprocal (two * rho) twoRhoPositive
      ≤ Quotient.positiveReciprocal (two * floor) twoFloorPositive
    antitone =
      Quotient.reciprocalAntitonePositive
        (two * floor) (two * rho)
        twoFloorPositive twoRhoPositive twoFloorBelowTwoRho
  in
  subst
    (λ selected → selected ≤ diagonalCeilingAt floor floorPositive)
    (sym (trans cauchyAsPositiveReciprocal reciprocalTransport))
    antitone

diagonalWeightNonnegative :
  ∀ {floor} (cell : DiagonalRateFloorCell floor) →
  0ℚ ≤ diagonalWeight cell
diagonalWeightNonnegative cell =
  ℚP.<⇒≤
    (ℚP.positive⁻¹
      (R443.cauchyEntryPositive
        (rate cell) (rate cell)
        (positive (ratePositive cell))
        (positive (ratePositive cell))))

compileR298Cell :
  ∀ {floor} →
  (floorPositive : 0ℚ < floor) →
  (cell : DiagonalRateFloorCell floor) →
  R298.WeightedDiagonalCell (diagonalCeilingAt floor floorPositive)
compileR298Cell floorPositive cell = R298.weighted-diagonal-cell
  (mass cell)
  (diagonalWeight cell)
  (massNonnegative cell)
  (diagonalWeightNonnegative cell)
  (diagonalWeightBelowFloorCeiling floorPositive cell)

record DiagonalRateFloorFamily (floor : ℚ) : Set where
  constructor diagonal-rate-floor-family
  field
    sharedFloorPositive : 0ℚ < floor
    cells : List (DiagonalRateFloorCell floor)

open DiagonalRateFloorFamily public

compileCells :
  ∀ {floor} →
  (floorPositive : 0ℚ < floor) →
  List (DiagonalRateFloorCell floor) →
  List (R298.WeightedDiagonalCell (diagonalCeilingAt floor floorPositive))
compileCells floorPositive [] = []
compileCells floorPositive (cell ∷ rest) =
  compileR298Cell floorPositive cell ∷ compileCells floorPositive rest

compileFamilyToR298 :
  ∀ {floor} (family : DiagonalRateFloorFamily floor) →
  List (R298.WeightedDiagonalCell
    (diagonalCeilingAt floor (sharedFloorPositive family)))
compileFamilyToR298 family =
  compileCells (sharedFloorPositive family) (cells family)

round449RateFloorToDiagonalCeilingCompilerClosed : Bool
round449RateFloorToDiagonalCeilingCompilerClosed = true

round449RequiresCanonicalFourierUnitGap : Bool
round449RequiresCanonicalFourierUnitGap = false

round449RequiresOnlyPositiveSharedCellRateFloor : Bool
round449RequiresOnlyPositiveSharedCellRateFloor = true

round449IntroducesCardinalityTax : Bool
round449IntroducesCardinalityTax = false

round449ContainsPostulate : Bool
round449ContainsPostulate = false

round449PackageAClosed : Bool
round449PackageAClosed = false

round449ClayPromotion : Bool
round449ClayPromotion = false

round449IntroducesCardinalityTaxIsFalse : round449IntroducesCardinalityTax ≡ false
round449IntroducesCardinalityTaxIsFalse = refl

round449ContainsPostulateIsFalse : round449ContainsPostulate ≡ false
round449ContainsPostulateIsFalse = refl
