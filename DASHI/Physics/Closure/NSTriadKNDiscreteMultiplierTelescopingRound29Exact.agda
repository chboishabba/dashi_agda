module DASHI.Physics.Closure.NSTriadKNDiscreteMultiplierTelescopingRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- Before any kernel majorisation, a multiplier difference is represented as
-- the exact telescoping sum of its signed increments along a finite path. This
-- is the discrete carrier analogue of the mean-value representation used by
-- the commutator lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

terminalSample : ℚ → List ℚ → ℚ
terminalSample current [] = current
terminalSample current (next ∷ rest) = terminalSample next rest

telescopingDifference : ℚ → List ℚ → ℚ
telescopingDifference current [] = 0ℚ
telescopingDifference current (next ∷ rest) =
  current - next + telescopingDifference next rest

telescopingPlusTerminal :
  (current : ℚ) →
  (path : List ℚ) →
  telescopingDifference current path + terminalSample current path
  ≡ current
telescopingPlusTerminal current [] = solve (current ∷ [])
telescopingPlusTerminal current (next ∷ rest) =
  trans
    (cong
      (λ tail → current - next + tail)
      (telescopingPlusTerminal next rest))
    (solve (current ∷ next ∷ []))

multiplierDifferenceIsSignedPathSum :
  (current : ℚ) →
  (path : List ℚ) →
  current - terminalSample current path
  ≡ telescopingDifference current path
multiplierDifferenceIsSignedPathSum current path =
  trans
    (cong
      (λ total → total - terminalSample current path)
      (sym (telescopingPlusTerminal current path)))
    (solve
      ( telescopingDifference current path
      ∷ terminalSample current path
      ∷ []))

stepMagnitudeSum : ℚ → List ℚ → ℚ
stepMagnitudeSum current [] = 0ℚ
stepMagnitudeSum current (next ∷ rest) =
  ∣ current - next ∣ + stepMagnitudeSum next rest

signedPathMagnitudeBound :
  (current : ℚ) →
  (path : List ℚ) →
  ∣ telescopingDifference current path ∣
  ≤ stepMagnitudeSum current path
signedPathMagnitudeBound current [] = ℚₚ.≤-refl
signedPathMagnitudeBound current (next ∷ rest) =
  ℚₚ.≤-trans
    (ℚₚ.∣p+q∣≤∣p∣+∣q∣
      (current - next)
      (telescopingDifference next rest))
    (ℚₚ.+-mono-≤
      ℚₚ.≤-refl
      (signedPathMagnitudeBound next rest))

multiplierEndpointMagnitudeBound :
  (current : ℚ) →
  (path : List ℚ) →
  ∣ current - terminalSample current path ∣
  ≤ stepMagnitudeSum current path
multiplierEndpointMagnitudeBound current path =
  subst
    (λ difference →
      ∣ difference ∣ ≤ stepMagnitudeSum current path)
    (multiplierDifferenceIsSignedPathSum current path)
    (signedPathMagnitudeBound current path)
  where
  open import Relation.Binary.PropositionalEquality using (subst)

discreteMultiplierTelescopingClosed : Bool
discreteMultiplierTelescopingClosed = true

discreteMultiplierTelescopingClosedIsTrue :
  discreteMultiplierTelescopingClosed ≡ true
discreteMultiplierTelescopingClosedIsTrue = refl
