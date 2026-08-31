module DASHI.Physics.Closure.NSTriadKNResolventDiagonalNoCardinalityRound298Exact where

------------------------------------------------------------------------
-- ROUND298 / DIAGONAL RESOLVENT PAYMENT HAS NO COHERENT CARDINALITY TAX
--
-- Once R297 completes the off-diagonal endpoint by the positive full Cauchy
-- kernel, only the diagonal remains.  For cell masses m_a >= 0 and resolvent
-- weights 0 <= w_a <= W,
--
--   sum_a w_a m_a <= W sum_a m_a.
--
-- This is finite ordered-field algebra and introduces no multiplicity factor.
-- The physical source now only has to provide:
--
--   (1) a cutoff-independent ceiling W for the literal viscous cell resolvent;
--   (2) a bound for the sum of literal R227 mixed-cell masses.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational

record WeightedDiagonalCell (W : ℚ) : Set where
  constructor weighted-diagonal-cell
  field
    mass weight : ℚ
    massNN : 0ℚ ≤ mass
    weightNN : 0ℚ ≤ weight
    weightBelowCeiling : weight ≤ W

open WeightedDiagonalCell public

sumMass : ∀ {W} → List (WeightedDiagonalCell W) → ℚ
sumMass [] = 0ℚ
sumMass (C ∷ rest) = mass C + sumMass rest

sumWeightedMass : ∀ {W} → List (WeightedDiagonalCell W) → ℚ
sumWeightedMass [] = 0ℚ
sumWeightedMass (C ∷ rest) = weight C * mass C + sumWeightedMass rest

sumMassNN :
  ∀ {W} (cells : List (WeightedDiagonalCell W)) → 0ℚ ≤ sumMass cells
sumMassNN [] = ℚP.≤-refl
sumMassNN (C ∷ rest) =
  Rational.addNonnegative (massNN C) (sumMassNN rest)

weightedDiagonalBelowCeilingMass :
  (W : ℚ) → 0ℚ ≤ W →
  (cells : List (WeightedDiagonalCell W)) →
  sumWeightedMass cells ≤ W * sumMass cells
weightedDiagonalBelowCeilingMass W WNN [] =
  subst (0ℚ ≤_) (solve (W ∷ [])) ℚP.≤-refl
weightedDiagonalBelowCeilingMass W WNN (C ∷ rest) =
  let
    cellPaid : weight C * mass C ≤ W * mass C
    cellPaid =
      Rational.nonnegativeProductMonotone
        (weightNN C) (massNN C) WNN (massNN C)
        (weightBelowCeiling C) ℚP.≤-refl

    tailPaid : sumWeightedMass rest ≤ W * sumMass rest
    tailPaid = weightedDiagonalBelowCeilingMass W WNN rest

    summed = ℚP.+-mono-≤ cellPaid tailPaid

    endpoint :
      W * mass C + W * sumMass rest ≡ W * sumMass (C ∷ rest)
    endpoint = solve (W ∷ mass C ∷ sumMass rest ∷ [])
  in
  subst
    (λ upper → sumWeightedMass (C ∷ rest) ≤ upper)
    endpoint summed

record PhysicalDiagonalReduction : Set where
  constructor physical-diagonal-reduction
  field
    ceiling : ℚ
    ceilingNN : 0ℚ ≤ ceiling
    cells : List (WeightedDiagonalCell ceiling)
    cellMassUpperBound : ℚ
    allCellMassPaid : sumMass cells ≤ cellMassUpperBound

open PhysicalDiagonalReduction public

physicalDiagonalPaid :
  (P : PhysicalDiagonalReduction) →
  sumWeightedMass (cells P) ≤ ceiling P * cellMassUpperBound P
physicalDiagonalPaid P =
  let
    first = weightedDiagonalBelowCeilingMass
      (ceiling P) (ceilingNN P) (cells P)

    massNN' = sumMassNN (cells P)

    upperNN : 0ℚ ≤ cellMassUpperBound P
    upperNN = ℚP.≤-trans massNN' (allCellMassPaid P)

    second :
      ceiling P * sumMass (cells P)
      ≤ ceiling P * cellMassUpperBound P
    second =
      Rational.nonnegativeProductMonotone
        (ceilingNN P) massNN'
        (ceilingNN P) upperNN
        ℚP.≤-refl (allCellMassPaid P)
  in
  ℚP.≤-trans first second

round298DiagonalNoCardinalityCompilerClosed : Bool
round298DiagonalNoCardinalityCompilerClosed = true

round298PhysicalResolventWeightCeilingInstalled : Bool
round298PhysicalResolventWeightCeilingInstalled = false

round298PhysicalAllMixedCellMassBoundInstalled : Bool
round298PhysicalAllMixedCellMassBoundInstalled = false

round298PhysicalDiagonalEndpointPaid : Bool
round298PhysicalDiagonalEndpointPaid = false

round298PackageAClosed : Bool
round298PackageAClosed = false

round298ClayPromotion : Bool
round298ClayPromotion = false

round298DiagonalNoCardinalityCompilerClosedIsTrue :
  round298DiagonalNoCardinalityCompilerClosed ≡ true
round298DiagonalNoCardinalityCompilerClosedIsTrue = refl
