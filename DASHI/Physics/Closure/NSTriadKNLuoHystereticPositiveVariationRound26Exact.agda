module DASHI.Physics.Closure.NSTriadKNLuoHystereticPositiveVariationRound26Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "A Structural Audit of Navier-Stokes Obstruction Calculus".
-- DOI: 10.48550/arXiv.2606.25341.
--
-- DASHI CONTRIBUTION
--
-- Repeated bad-state entries are charged by positive variation rather than by
-- an unsupported residence-count assertion.  For hysteresis gap h and every
-- explicit entry before+h <= after, the rise after-before pays at least h.
-- Summing a finite list gives
--
--   sum(entry gaps) <= sum(positive rises).
--
-- This is the exact finite form of h * N_entries <= Var^+.  The PDE estimate
-- controlling the full positive variation remains the open physical producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _≤_; -_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst₂)

record HystereticEntry (gap : ℚ) : Set where
  constructor hysteretic-entry
  field
    before after : ℚ
    crossesGap : before + gap ≤ after

open HystereticEntry public

entryPositiveRise :
  ∀ {gap} → HystereticEntry gap → ℚ
entryPositiveRise entry = after entry - before entry

entryGapPaidByRise :
  ∀ {gap} →
  (entry : HystereticEntry gap) →
  gap ≤ entryPositiveRise entry
entryGapPaidByRise {gap} entry =
  subst₂ _≤_ leftNormal rightNormal shifted
  where
  shifted :
    (- before entry) + (before entry + gap)
    ≤ (- before entry) + after entry
  shifted = ℚₚ.+-monoˡ-≤ (- before entry) (crossesGap entry)

  leftNormal :
    (- before entry) + (before entry + gap) ≡ gap
  leftNormal = solve (before entry ∷ gap ∷ [])

  rightNormal :
    (- before entry) + after entry
    ≡ entryPositiveRise entry
  rightNormal = solve (before entry ∷ after entry ∷ [])

entryGapCharge :
  ∀ {gap} → List (HystereticEntry gap) → ℚ
entryGapCharge {gap} [] = 0ℚ
entryGapCharge {gap} (entry ∷ rest) =
  gap + entryGapCharge rest

entryPositiveVariation :
  ∀ {gap} → List (HystereticEntry gap) → ℚ
entryPositiveVariation [] = 0ℚ
entryPositiveVariation (entry ∷ rest) =
  entryPositiveRise entry + entryPositiveVariation rest

hystereticEntryChargeBelowPositiveVariation :
  ∀ {gap} →
  (entries : List (HystereticEntry gap)) →
  entryGapCharge entries ≤ entryPositiveVariation entries
hystereticEntryChargeBelowPositiveVariation [] = ℚₚ.≤-refl
hystereticEntryChargeBelowPositiveVariation (entry ∷ rest) =
  ℚₚ.+-mono-≤
    (entryGapPaidByRise entry)
    (hystereticEntryChargeBelowPositiveVariation rest)

record PositiveVariationBudget (gap : ℚ) : Set where
  constructor positive-variation-budget
  field
    entries : List (HystereticEntry gap)
    totalPositiveVariation : ℚ
    listedVariationBelowTotal :
      entryPositiveVariation entries ≤ totalPositiveVariation

open PositiveVariationBudget public

allEntryChargesBelowVariationBudget :
  ∀ {gap} →
  (budget : PositiveVariationBudget gap) →
  entryGapCharge (entries budget) ≤ totalPositiveVariation budget
allEntryChargesBelowVariationBudget budget =
  ℚₚ.≤-trans
    (hystereticEntryChargeBelowPositiveVariation (entries budget))
    (listedVariationBelowTotal budget)
