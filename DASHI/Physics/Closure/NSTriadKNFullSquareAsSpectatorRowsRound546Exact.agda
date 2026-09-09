module DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact where

------------------------------------------------------------------------
-- ROUND546 / GENERIC FULL SQUARE AS A SUM OF SPECTATOR ROWS
--
-- For a pair scalar F and a fixed alpha-list xs define the beta-row
--
--   Row(beta;xs) = sum_{alpha in xs} F(alpha,beta).
--
-- Summing those rows over beta in xs gives the complete ordered square.  This
-- is the generic finite bridge needed to lift R545's spectator factorization
-- over the second cell index.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543

spectatorRow :
  ∀ {A : Set} → (A → A → ℚ) → A → List A → ℚ
spectatorRow F beta [] = 0ℚ
spectatorRow F beta (alpha ∷ rest) =
  F alpha beta + spectatorRow F beta rest

allSpectatorRows :
  ∀ {A : Set} →
  (A → A → ℚ) → List A → List A → ℚ
allSpectatorRows F alphas [] = 0ℚ
allSpectatorRows F alphas (beta ∷ rest) =
  spectatorRow F beta alphas + allSpectatorRows F alphas rest

spectatorRowIsColumnSum :
  ∀ {A : Set}
    (F : A → A → ℚ) (beta : A) (items : List A) →
  spectatorRow F beta items ≡ R539.columnSum F items beta
spectatorRowIsColumnSum F beta [] = refl
spectatorRowIsColumnSum F beta (alpha ∷ rest) =
  cong₂ _+_ refl (spectatorRowIsColumnSum F beta rest)

allRowsWithAddedHead :
  ∀ {A : Set}
    (F : A → A → ℚ) (x : A) (rest : List A) →
  allSpectatorRows F (x ∷ rest) rest
  ≡ R539.rowSum F x rest + allSpectatorRows F rest rest
allRowsWithAddedHead F x [] = refl
allRowsWithAddedHead F x (beta ∷ rest)
  rewrite allRowsWithAddedHead F x rest =
  solve
    (F x beta
      ∷ spectatorRow F beta rest
      ∷ R539.rowSum F x rest
      ∷ allSpectatorRows F rest rest
      ∷ [])

fullSquareIsAllSpectatorRows :
  ∀ {A : Set}
    (F : A → A → ℚ) (items : List A) →
  R543.fullSquareSum F items ≡ allSpectatorRows F items items
fullSquareIsAllSpectatorRows F [] = refl
fullSquareIsAllSpectatorRows F (x ∷ rest)
  rewrite fullSquareIsAllSpectatorRows F rest
        | allRowsWithAddedHead F x rest
        | spectatorRowIsColumnSum F x rest =
  solve
    (F x x
      ∷ R539.rowSum F x rest
      ∷ R539.columnSum F rest x
      ∷ allSpectatorRows F rest rest
      ∷ [])

round546FullSquareAsSpectatorRowsClosed : Bool
round546FullSquareAsSpectatorRowsClosed = true

round546IntroducesAnyAnalyticEstimate : Bool
round546IntroducesAnyAnalyticEstimate = false

round546FullSquareAsSpectatorRowsClosedIsTrue :
  round546FullSquareAsSpectatorRowsClosed ≡ true
round546FullSquareAsSpectatorRowsClosedIsTrue = refl
