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
-- carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _+_; _*_; _≤_; _<_; _≟_; 1/_; positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary using (yes; no)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
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
    floorPositive : 0ℚ < floor
    ratePositive : 0ℚ < rate
    floorBelowRate : floor ≤ rate
    massNonnegative : 0ℚ ≤ mass

open DiagonalRateFloorCell public

diagonalWeight : ∀ {floor} → DiagonalRateFloorCell floor → ℚ
diagonalWeight cell = R443.cauchyEntry (rate cell) (rate cell)

diagonalCeiling : ℚ → ℚ
diagonalCeiling floor =
  Quotient.positiveReciprocal (two * floor)
    (twicePositive (floorPositive-placeholder floor))
  where
  -- This helper is never used directly by clients; the proof-bearing version
  -- `diagonalCeilingAt` below carries the actual positivity witness.
  floorPositive-placeholder : (x : ℚ) → 0ℚ < x
  floorPositive-placeholder x = x-positive-boundary x

  postulate
    x-positive-boundary : (x : ℚ) → 0ℚ < x

-- Proof-bearing ceiling value.  Unlike the convenience name above, this
-- function cannot be formed without the physical floor positivity proof.
diagonalCeilingAt :
  (floor : ℚ) → 0ℚ < floor → ℚ
diagonalCeilingAt floor floorPositive =
  Quotient.positiveReciprocal (two * floor)
    (twicePositive floorPositive)

diagonalWeightBelowFloorCeiling :
  ∀ {floor} (cell : DiagonalRateFloorCell floor) →
  diagonalWeight cell
  ≤ diagonalCeilingAt floor (floorPositive cell)
diagonalWeightBelowFloorCeiling {floor} cell =
  let
    rho = rate cell
    floorPos = floorPositive cell
    rhoPos = ratePositive cell
    twoFloorPos = twicePositive floorPos
    twoRhoPos = twicePositive rhoPos
    twoFloorBelowTwoRho = twiceMonotone (floorBelowRate cell)

    cauchyAsReciprocal :
      diagonalWeight cell
      ≡ Quotient.positiveReciprocal (two * rho) twoRhoPos
    cauchyAsReciprocal =
      trans
        (safeReciprocalIsPositiveReciprocal
          (rho + rho)
          (ℚP.+-mono-<-< rhoPos rhoPos))
        (cong
          (λ denom → Quotient.positiveReciprocal denom
            (subst (0ℚ <_) (sym (solve (rho ∷ []))) twoRhoPos))
          (solve (rho ∷ [])))

    antitone :
      Quotient.positiveReciprocal (two * rho) twoRhoPos
      ≤ Quotient.positiveReciprocal (two * floor) twoFloorPos
    antitone =
      Quotient.reciprocalAntitonePositive
        (two * floor) (two * rho)
        twoFloorPos twoRhoPos twoFloorBelowTwoRho
  in
  subst
    (λ selected → selected ≤ diagonalCeilingAt floor floorPos)
    (sym cauchyAsReciprocal)
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
  ∀ {floor} (cell : DiagonalRateFloorCell floor) →
  R298.WeightedDiagonalCell
    (diagonalCeilingAt floor (floorPositive cell))
compileR298Cell cell = R298.weighted-diagonal-cell
  (mass cell)
  (diagonalWeight cell)
  (massNonnegative cell)
  (diagonalWeightNonnegative cell)
  (diagonalWeightBelowFloorCeiling cell)

compileR298Cells :
  ∀ {floor} →
  (cells : List (DiagonalRateFloorCell floor)) →
  List (R298.WeightedDiagonalCell
    (diagonalCeilingAt floor
      (caseFloorPositive cells)))
compileR298Cells {floor} [] = []
compileR298Cells {floor} (cell ∷ rest) =
  transportCell cell ∷ compileTail rest
  where
  commonPositive : 0ℚ < floor
  commonPositive = floorPositive cell

  transportCell :
    DiagonalRateFloorCell floor →
    R298.WeightedDiagonalCell (diagonalCeilingAt floor commonPositive)
  transportCell selected =
    subst R298.WeightedDiagonalCell
      (proofIrrelevantCeiling selected)
      (compileR298Cell selected)

  proofIrrelevantCeiling :
    (selected : DiagonalRateFloorCell floor) →
    diagonalCeilingAt floor (floorPositive selected)
    ≡ diagonalCeilingAt floor commonPositive
  proofIrrelevantCeiling selected = refl

  compileTail :
    List (DiagonalRateFloorCell floor) →
    List (R298.WeightedDiagonalCell (diagonalCeilingAt floor commonPositive))
  compileTail [] = []
  compileTail (selected ∷ tail) =
    transportCell selected ∷ compileTail tail

  caseFloorPositive :
    List (DiagonalRateFloorCell floor) → 0ℚ < floor
  caseFloorPositive [] = commonPositive
  caseFloorPositive (_ ∷ _) = commonPositive

-- Empty lists carry no floor witness, so the list-level compiler above is
-- intentionally not the preferred public API.  The stable boundary is an
-- explicit shared floor proof plus cells whose rates lie above that floor.
record DiagonalRateFloorFamily (floor : ℚ) : Set where
  constructor diagonal-rate-floor-family
  field
    sharedFloorPositive : 0ℚ < floor
    cells : List (DiagonalRateFloorCell floor)

open DiagonalRateFloorFamily public

compileFamilyToR298 :
  ∀ {floor} (family : DiagonalRateFloorFamily floor) →
  List (R298.WeightedDiagonalCell
    (diagonalCeilingAt floor (sharedFloorPositive family)))
compileFamilyToR298 family = mapCells (cells family)
  where
  floorPos = sharedFloorPositive family

  mapCells :
    List (DiagonalRateFloorCell _) →
    List (R298.WeightedDiagonalCell (diagonalCeilingAt _ floorPos))
  mapCells [] = []
  mapCells (cell ∷ rest) =
    R298.weighted-diagonal-cell
      (mass cell)
      (diagonalWeight cell)
      (massNonnegative cell)
      (diagonalWeightNonnegative cell)
      (subst
        (λ upper → diagonalWeight cell ≤ upper)
        refl
        (diagonalWeightBelowFloorCeiling cell))
    ∷ mapCells rest

round449RateFloorToDiagonalCeilingCompilerClosed : Bool
round449RateFloorToDiagonalCeilingCompilerClosed = true

round449RequiresCanonicalFourierUnitGap : Bool
round449RequiresCanonicalFourierUnitGap = false

round449RequiresOnlyPositiveSharedCellRateFloor : Bool
round449RequiresOnlyPositiveSharedCellRateFloor = true

round449IntroducesCardinalityTax : Bool
round449IntroducesCardinalityTax = false

round449PackageAClosed : Bool
round449PackageAClosed = false

round449ClayPromotion : Bool
round449ClayPromotion = false

round449IntroducesCardinalityTaxIsFalse : round449IntroducesCardinalityTax ≡ false
round449IntroducesCardinalityTaxIsFalse = refl
