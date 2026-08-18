module DASHI.Physics.Closure.NSTriadKNClusterSylvesterBudgetRound81Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Rajendra Bhatia; Chandler Davis; Alan McIntosh,
-- "Perturbation of spectral subspaces and solution of linear operator
-- equations", Linear Algebra and its Applications 52/53 (1983), 45--67.
-- DOI: 10.1016/0024-3795(83)80007-X.
--
-- Tosio Kato,
-- "On the Adiabatic Theorem of Quantum Mechanics",
-- Journal of the Physical Society of Japan 5 (1950), 435--439.
-- DOI: 10.1143/JPSJ.5.435.
--
-- J. E. Avron; R. Seiler; L. G. Yaffe,
-- "Adiabatic theorems and applications to the quantum Hall effect",
-- Communications in Mathematical Physics 110 (1987), 33--49.
-- DOI: 10.1007/BF01209015.
--
-- ROUND81 / CLUSTER SYLVESTER CORE
--
-- Differentiating an invariant spectral projector equation
--
--     S P = P S
--
-- gives the Sylvester/commutator equation
--
--     [S , Pdot] = - [Sdot , P].
--
-- In an eigenbasis, each cluster-complement coordinate has the exact form
--
--     forcing_ij = gap_ij * projectorRate_ij
--
-- up to the orientation/sign convention used for forcing.  This module proves
-- the exact two-coordinate squared-energy consequence needed in dimension 3:
-- if the two cluster-complement gaps are each at least delta, then
--
--   delta^2 (rateA^2 + rateB^2)
--       <= forcingA^2 + forcingB^2.
--
-- No individual simplicity is required inside the selected cluster.  The PDE
-- obligation is now only to identify forcingA/B with the corresponding actual
-- strain-material-derivative / pressure-Riesz coordinates on the selected NS
-- trajectory and fund their squared mass.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order

square : ℚ → ℚ
square x = x * x

record TwoCoordinateClusterSylvester : Set where
  field
    gapA gapB : ℚ
    projectorRateA projectorRateB : ℚ
    forcingA forcingB : ℚ

    forcingAIsGapTimesRate :
      forcingA ≡ gapA * projectorRateA

    forcingBIsGapTimesRate :
      forcingB ≡ gapB * projectorRateB

open TwoCoordinateClusterSylvester public

projectorRateSquareEnergy : TwoCoordinateClusterSylvester → ℚ
projectorRateSquareEnergy datum =
  square (projectorRateA datum) + square (projectorRateB datum)

forcingSquareEnergy : TwoCoordinateClusterSylvester → ℚ
forcingSquareEnergy datum =
  square (forcingA datum) + square (forcingB datum)

gapWeightedProjectorRateSquareEnergy : TwoCoordinateClusterSylvester → ℚ
gapWeightedProjectorRateSquareEnergy datum =
  square (gapA datum) * square (projectorRateA datum)
  + square (gapB datum) * square (projectorRateB datum)

forcingEnergyEqualsGapWeightedRateEnergy :
  (datum : TwoCoordinateClusterSylvester) →
  forcingSquareEnergy datum ≡ gapWeightedProjectorRateSquareEnergy datum
forcingEnergyEqualsGapWeightedRateEnergy datum =
  subst
    (λ a → square a + square (forcingB datum)
      ≡ gapWeightedProjectorRateSquareEnergy datum)
    (forcingAIsGapTimesRate datum)
    (subst
      (λ b → square (gapA datum * projectorRateA datum) + square b
        ≡ gapWeightedProjectorRateSquareEnergy datum)
      (forcingBIsGapTimesRate datum)
      (ℚRing.solve-∀
        (gapA datum) (gapB datum)
        (projectorRateA datum) (projectorRateB datum)))

record SeparatedTwoCoordinateClusterSylvester : Set where
  field
    sylvester : TwoCoordinateClusterSylvester
    threshold : ℚ

    thresholdNonnegative : 0ℚ ≤ threshold
    gapANonnegative : 0ℚ ≤ gapA sylvester
    gapBNonnegative : 0ℚ ≤ gapB sylvester
    thresholdBelowGapA : threshold ≤ gapA sylvester
    thresholdBelowGapB : threshold ≤ gapB sylvester

open SeparatedTwoCoordinateClusterSylvester public

thresholdSquareBelowGapASquare :
  (datum : SeparatedTwoCoordinateClusterSylvester) →
  square (threshold datum) ≤ square (gapA (sylvester datum))
thresholdSquareBelowGapASquare datum =
  Order.nonnegativeProductMonotone
    (thresholdNonnegative datum)
    (thresholdNonnegative datum)
    (gapANonnegative datum)
    (gapANonnegative datum)
    (thresholdBelowGapA datum)
    (thresholdBelowGapA datum)

thresholdSquareBelowGapBSquare :
  (datum : SeparatedTwoCoordinateClusterSylvester) →
  square (threshold datum) ≤ square (gapB (sylvester datum))
thresholdSquareBelowGapBSquare datum =
  Order.nonnegativeProductMonotone
    (thresholdNonnegative datum)
    (thresholdNonnegative datum)
    (gapBNonnegative datum)
    (gapBNonnegative datum)
    (thresholdBelowGapB datum)
    (thresholdBelowGapB datum)

thresholdSquaredProjectorRateEnergyBound :
  (datum : SeparatedTwoCoordinateClusterSylvester) →
  square (threshold datum) * projectorRateSquareEnergy (sylvester datum)
  ≤ forcingSquareEnergy (sylvester datum)
thresholdSquaredProjectorRateEnergyBound datum =
  let
    s = sylvester datum
    deltaSqNN : 0ℚ ≤ square (threshold datum)
    deltaSqNN = Order.squareNonnegative (threshold datum)

    gapASqNN : 0ℚ ≤ square (gapA s)
    gapASqNN = Order.squareNonnegative (gapA s)

    gapBSqNN : 0ℚ ≤ square (gapB s)
    gapBSqNN = Order.squareNonnegative (gapB s)

    rateASqNN : 0ℚ ≤ square (projectorRateA s)
    rateASqNN = Order.squareNonnegative (projectorRateA s)

    rateBSqNN : 0ℚ ≤ square (projectorRateB s)
    rateBSqNN = Order.squareNonnegative (projectorRateB s)

    first :
      square (threshold datum) * square (projectorRateA s)
      ≤ square (gapA s) * square (projectorRateA s)
    first = Order.nonnegativeProductMonotone
      deltaSqNN rateASqNN gapASqNN rateASqNN
      (thresholdSquareBelowGapASquare datum)
      (ℚP.≤-refl {x = square (projectorRateA s)})

    second :
      square (threshold datum) * square (projectorRateB s)
      ≤ square (gapB s) * square (projectorRateB s)
    second = Order.nonnegativeProductMonotone
      deltaSqNN rateBSqNN gapBSqNN rateBSqNN
      (thresholdSquareBelowGapBSquare datum)
      (ℚP.≤-refl {x = square (projectorRateB s)})

    summed :
      square (threshold datum) * square (projectorRateA s)
        + square (threshold datum) * square (projectorRateB s)
      ≤ gapWeightedProjectorRateSquareEnergy s
    summed = ℚP.+-mono-≤ first second

    regrouped :
      square (threshold datum) * projectorRateSquareEnergy s
      ≤ gapWeightedProjectorRateSquareEnergy s
    regrouped = subst
      (λ left → left ≤ gapWeightedProjectorRateSquareEnergy s)
      (sym (ℚRing.solve-∀
        (threshold datum) (projectorRateA s) (projectorRateB s)))
      summed
  in
  subst
    (λ upper →
      square (threshold datum) * projectorRateSquareEnergy s ≤ upper)
    (sym (forcingEnergyEqualsGapWeightedRateEnergy s))
    regrouped

round81ClusterSylvesterSquaredBudgetConstructed : Bool
round81ClusterSylvesterSquaredBudgetConstructed = true

round81ClusterSylvesterSquaredBudgetConstructedIsTrue :
  round81ClusterSylvesterSquaredBudgetConstructed ≡ true
round81ClusterSylvesterSquaredBudgetConstructedIsTrue = refl
