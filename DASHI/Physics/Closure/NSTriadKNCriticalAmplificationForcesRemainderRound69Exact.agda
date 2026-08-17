module DASHI.Physics.Closure.NSTriadKNCriticalAmplificationForcesRemainderRound69Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Luis Escauriaza; Gregory Seregin; Vladimir Sverak.
-- Title: "L3,infinity-solutions of the Navier-Stokes equations and backward
-- uniqueness".
-- DOI: 10.1070/RM2003v058n02ABEH000609.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND 69 / NON-CIRCULAR AMPLIFICATION ALTERNATIVE
--
-- Barker-Prange/Tao use an ambient critical bound to obtain quantitative
-- regularity/concentration propagation.  That bound cannot be imported as the
-- missing DASHI C1 theorem: C1 is precisely the unconditional bound we seek.
--
-- The non-circular algebraic fragment is nevertheless exact.  Suppose the
-- canonical critical ratio Xi has a SAME-OBJECT one-step decomposition
--
--   Xi_(n+1) <= inherited_n + remainder_n.
--
-- Then any excess
--
--   inherited_n + mu <= Xi_(n+1)
--
-- forces
--
--   mu <= remainder_n.
--
-- No hypothesis Xi_n <= K occurs.  Thus a physical localized shell identity
-- can feed a concentration argument only if its remainder is independently
-- identified with a genuine spatial/frequency concentration quantity.  This
-- theorem isolates exactly that first falsifiable implication.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst₂)

import DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact as C1

record CriticalRatioStepDecomposition
    {balances block}
    (positiveBlock : C1.PositiveCriticalBlockScale balances block) : Set where
  field
    inherited remainder : Nat → ℚ
    successorBound : ∀ n →
      C1.normalizedCriticalRatio positiveBlock (suc n)
      ≤ inherited n + remainder n

open CriticalRatioStepDecomposition public

criticalAmplificationForcesRemainder :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    (step : CriticalRatioStepDecomposition positiveBlock)
    (n : Nat) (mu : ℚ) →
  inherited step n + mu
    ≤ C1.normalizedCriticalRatio positiveBlock (suc n) →
  mu ≤ remainder step n
criticalAmplificationForcesRemainder step n mu amplification =
  let
    base = inherited step n
    rem = remainder step n

    sandwiched : base + mu ≤ base + rem
    sandwiched = ℚP.≤-trans amplification (successorBound step n)

    shifted : (- base) + (base + mu) ≤ (- base) + (base + rem)
    shifted = ℚP.+-monoʳ-≤ (- base) sandwiched

    leftMeaning : (- base) + (base + mu) ≡ mu
    leftMeaning = solve (base ∷ mu ∷ [])

    rightMeaning : (- base) + (base + rem) ≡ rem
    rightMeaning = solve (base ∷ rem ∷ [])
  in
  subst₂ _≤_ leftMeaning rightMeaning shifted

-- A useful specialization: the inherited allowance may itself be a multiple
-- of the previous ratio.  The theorem still needs no bound on that ratio.
record MultiplicativeCriticalRatioStep
    {balances block}
    (positiveBlock : C1.PositiveCriticalBlockScale balances block) : Set where
  field
    alpha remainder : Nat → ℚ
    successorBound : ∀ n →
      C1.normalizedCriticalRatio positiveBlock (suc n)
      ≤ alpha n * C1.normalizedCriticalRatio positiveBlock n + remainder n

open MultiplicativeCriticalRatioStep public

multiplicativeStepAsDecomposition :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block} →
  MultiplicativeCriticalRatioStep positiveBlock →
  CriticalRatioStepDecomposition positiveBlock
multiplicativeStepAsDecomposition {positiveBlock = positiveBlock} step = record
  { inherited = λ n →
      MultiplicativeCriticalRatioStep.alpha step n
      * C1.normalizedCriticalRatio positiveBlock n
  ; remainder = MultiplicativeCriticalRatioStep.remainder step
  ; successorBound = MultiplicativeCriticalRatioStep.successorBound step
  }

multiplicativeExcessForcesRemainder :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    (step : MultiplicativeCriticalRatioStep positiveBlock)
    (n : Nat) (mu : ℚ) →
  MultiplicativeCriticalRatioStep.alpha step n
      * C1.normalizedCriticalRatio positiveBlock n + mu
    ≤ C1.normalizedCriticalRatio positiveBlock (suc n) →
  mu ≤ MultiplicativeCriticalRatioStep.remainder step n
multiplicativeExcessForcesRemainder step n mu amplification =
  criticalAmplificationForcesRemainder
    (multiplicativeStepAsDecomposition step) n mu amplification

round69CriticalAmplificationAlternativeConstructed : Bool
round69CriticalAmplificationAlternativeConstructed = true

round69CriticalAmplificationUsesNoAmbientCriticalBound : Bool
round69CriticalAmplificationUsesNoAmbientCriticalBound = true

round69PhysicalRemainderIdentifiedAsConcentration : Bool
round69PhysicalRemainderIdentifiedAsConcentration = false

round69CriticalAmplificationAlternativeConstructedIsTrue :
  round69CriticalAmplificationAlternativeConstructed ≡ true
round69CriticalAmplificationAlternativeConstructedIsTrue = refl

round69PhysicalRemainderIdentifiedAsConcentrationIsFalse :
  round69PhysicalRemainderIdentifiedAsConcentration ≡ false
round69PhysicalRemainderIdentifiedAsConcentrationIsFalse = refl
