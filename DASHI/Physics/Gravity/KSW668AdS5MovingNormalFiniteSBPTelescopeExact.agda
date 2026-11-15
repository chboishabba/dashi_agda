module DASHI.Physics.Gravity.KSW668AdS5MovingNormalFiniteSBPTelescopeExact where

------------------------------------------------------------------------
-- Original KSW668 moving a=t TT first-order normal upwind algebra.
-- Reuse actual rational ring solver; prove generic FINITE-GRID
-- telescoping (summation by parts), not a Boolean status receipt.
--
-- For samples [x0,..,xN] in any finite ordered string:
-- 2 Sum_{j=0}^{N-1} x_j (x_{j+1}-x_j)
--    + Sum_{j=0}^{N-1} (x_{j+1}-x_j)^2
--  = x_N^2 - x_0^2.
--
-- 2 Sum_{j=1}^N x_j (x_j-x_{j-1})
--    - Sum_{j=0}^{N-1} (x_{j+1}-x_j)^2
--  = x_N^2 - x_0^2.
--
-- No spatial Fourier inverse or continuum assumption. The physical
-- source/velocity factor and full SSPRK3 weighted bulk equations remain
-- separately specified. SOURCE-ONLY: pinned Agda 2.9 kernel NOT run.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans; sym)

two : ℚ
two = (+ 2) / 1

sq : ℚ → ℚ
sq x = x * x

delta : ℚ → ℚ → ℚ
delta x y = y + - x

firstSq : List ℚ → ℚ
firstSq [] = 0ℚ
firstSq (x ∷ xs) = sq x

lastSq : List ℚ → ℚ
lastSq [] = 0ℚ
lastSq (x ∷ []) = sq x
lastSq (x ∷ y ∷ xs) = lastSq (y ∷ xs)

differenceSquareSum : List ℚ → ℚ
differenceSquareSum (x ∷ y ∷ xs) =
  sq (delta x y) + differenceSquareSum (y ∷ xs)
differenceSquareSum _ = 0ℚ

forwardEnergySum : List ℚ → ℚ
forwardEnergySum (x ∷ y ∷ xs) =
  x * delta x y + forwardEnergySum (y ∷ xs)
forwardEnergySum _ = 0ℚ

backwardEnergySum : List ℚ → ℚ
backwardEnergySum (x ∷ y ∷ xs) =
  y * delta x y + backwardEnergySum (y ∷ xs)
backwardEnergySum _ = 0ℚ

forwardPairEnergy : List ℚ → ℚ
forwardPairEnergy (x ∷ y ∷ xs) =
  two * x * delta x y + sq (delta x y)
    + forwardPairEnergy (y ∷ xs)
forwardPairEnergy _ = 0ℚ

backwardPairEnergy : List ℚ → ℚ
backwardPairEnergy (x ∷ y ∷ xs) =
  two * y * delta x y + - sq (delta x y)
    + backwardPairEnergy (y ∷ xs)
backwardPairEnergy _ = 0ℚ

forwardPairTelescope : (xs : List ℚ) →
  forwardPairEnergy xs ≡ lastSq xs + - firstSq xs
forwardPairTelescope [] = refl
forwardPairTelescope (x ∷ []) = solve []
forwardPairTelescope (x ∷ y ∷ xs)
  rewrite forwardPairTelescope (y ∷ xs) = solve []

backwardPairTelescope : (xs : List ℚ) →
  backwardPairEnergy xs ≡ lastSq xs + - firstSq xs
backwardPairTelescope [] = refl
backwardPairTelescope (x ∷ []) = solve []
backwardPairTelescope (x ∷ y ∷ xs)
  rewrite backwardPairTelescope (y ∷ xs) = solve []

forwardPairEqualsTerms : (xs : List ℚ) →
  forwardPairEnergy xs
    ≡ two * forwardEnergySum xs + differenceSquareSum xs
forwardPairEqualsTerms [] = refl
forwardPairEqualsTerms (x ∷ []) = refl
forwardPairEqualsTerms (x ∷ y ∷ xs)
  rewrite forwardPairEqualsTerms (y ∷ xs) = solve []

backwardPairEqualsTerms : (xs : List ℚ) →
  backwardPairEnergy xs
    ≡ two * backwardEnergySum xs + - differenceSquareSum xs
backwardPairEqualsTerms [] = refl
backwardPairEqualsTerms (x ∷ []) = solve []
backwardPairEqualsTerms (x ∷ y ∷ xs)
  rewrite backwardPairEqualsTerms (y ∷ xs) = solve []

originalForwardNormalSBP : (xs : List ℚ) →
  two * forwardEnergySum xs + differenceSquareSum xs
    ≡ lastSq xs + - firstSq xs
originalForwardNormalSBP xs =
  trans (sym (forwardPairEqualsTerms xs)) (forwardPairTelescope xs)

originalBackwardNormalSBP : (xs : List ℚ) →
  two * backwardEnergySum xs + - differenceSquareSum xs
    ≡ lastSq xs + - firstSq xs
originalBackwardNormalSBP xs =
  trans (sym (backwardPairEqualsTerms xs)) (backwardPairTelescope xs)
