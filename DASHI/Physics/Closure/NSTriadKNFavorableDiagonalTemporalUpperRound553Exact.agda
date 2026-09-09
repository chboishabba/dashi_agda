module DASHI.Physics.Closure.NSTriadKNFavorableDiagonalTemporalUpperRound553Exact where

------------------------------------------------------------------------
-- ROUND553 / FAVOURABLE-SIGN DIAGONAL TEMPORAL REDUCTION
--
-- Once R552 has integrated R551, the scalar shape is
--
--   2 R = (F - G) - Tdot.
--
-- If FTC gives Tdot = Tend - Tinit, while G >= 0 and Tend >= 0, then
--
--   2 R <= F + Tinit.
--
-- Thus neither the integrated self-Gram term nor the terminal self-flux needs
-- an upper estimate.  Only the initial self-flux survives in an upper bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_; -_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539

subtractMonotone : ∀ {a b c d : ℚ} → a ≤ b → c ≤ d → a - d ≤ b - c
subtractMonotone {a} {b} {c} {d} a≤b c≤d =
  let
    negOrder : - d ≤ - c
    negOrder =
      let
        shifted : 0ℚ ≤ d - c
        shifted = subst
          (λ x → x ≤ d - c)
          (solve (c ∷ []))
          (ℚP.+-monoʳ-≤ (- c) c≤d)
      in
      subst
        (λ x → x ≤ - c)
        (solve (d ∷ c ∷ []))
        (ℚP.+-monoˡ-≤ (- d) shifted)
    added = ℚP.+-mono-≤ a≤b negOrder
  in
  subst
    (λ lhs → lhs ≤ b - c)
    (solve (a ∷ d ∷ []))
    (subst
      (λ rhs → a + (- d) ≤ rhs)
      (solve (b ∷ c ∷ []))
      added)

favorableDiagonalUpper :
  (remainder factored selfGram integratedFluxTangent
    initialFlux terminalFlux : ℚ) →
  R539.two * remainder
    ≡ (factored - selfGram) - integratedFluxTangent →
  integratedFluxTangent ≡ terminalFlux - initialFlux →
  0ℚ ≤ selfGram →
  0ℚ ≤ terminalFlux →
  R539.two * remainder ≤ factored + initialFlux
favorableDiagonalUpper remainder factored selfGram integratedFluxTangent
    initialFlux terminalFlux reduced ftc selfGramNN terminalFluxNN =
  let
    dropGram : factored - selfGram ≤ factored - 0ℚ
    dropGram = subtractMonotone ℚP.≤-refl selfGramNN

    dropTerminal :
      (factored - selfGram) - terminalFlux
      ≤ (factored - 0ℚ) - 0ℚ
    dropTerminal = subtractMonotone dropGram terminalFluxNN

    addInitial :
      ((factored - selfGram) - terminalFlux) + initialFlux
      ≤ ((factored - 0ℚ) - 0ℚ) + initialFlux
    addInitial = ℚP.+-monoʳ-≤ initialFlux dropTerminal

    normalized :
      (factored - selfGram) - (terminalFlux - initialFlux)
      ≤ factored + initialFlux
    normalized =
      subst
        (λ lhs → lhs ≤ factored + initialFlux)
        (solve (factored ∷ selfGram ∷ terminalFlux ∷ initialFlux ∷ []))
        (subst
          (λ rhs →
            ((factored - selfGram) - terminalFlux) + initialFlux ≤ rhs)
          (solve (factored ∷ initialFlux ∷ []))
          addInitial)
  in
  subst
    (λ left → left ≤ factored + initialFlux)
    reduced
    (subst
      (λ tangent →
        (factored - selfGram) - tangent ≤ factored + initialFlux)
      ftc
      normalized)

round553FavorableSelfGramDropped : Bool
round553FavorableSelfGramDropped = true

round553FavorableTerminalSelfFluxDropped : Bool
round553FavorableTerminalSelfFluxDropped = true

round553OnlyInitialSelfFluxSurvivesUpperBound : Bool
round553OnlyInitialSelfFluxSurvivesUpperBound = true

round553FactoredFullSpacetimeBoundClosed : Bool
round553FactoredFullSpacetimeBoundClosed = false

round553ClayPromotion : Bool
round553ClayPromotion = false

round553OnlyInitialSelfFluxSurvivesUpperBoundIsTrue :
  round553OnlyInitialSelfFluxSurvivesUpperBound ≡ true
round553OnlyInitialSelfFluxSurvivesUpperBoundIsTrue = refl

round553ClayPromotionIsFalse : round553ClayPromotion ≡ false
round553ClayPromotionIsFalse = refl
