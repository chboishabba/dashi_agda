module DASHI.Physics.Closure.NSTriadKNIntegratedDangerOccupationWeldRound92Exact where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Integrated signed danger-cost to compact-Gamma occupation weld".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is exact ordered-field/repository composition.
--
-- UPSTREAM CALIBRATION
-- Sean P. Meyn; Richard L. Tweedie,
-- "Markov Chains and Stochastic Stability", 2nd ed., Cambridge University
-- Press, 2009. DOI: 10.1017/CBO9780511626630.
-- The existing Round82 theorem uses only the deterministic drift/occupation
-- shape; no stochastic theorem is imported here.
--
-- ROUND92 / EXACT WELD
--
-- The Round92 signed ledger gives finite cells satisfying
--
--      N_i + delta D_i <= C_i.
--
-- Hence sum N_i + delta sum D_i <= sum C_i.  To feed the already-proved
-- deterministic compact-Gamma occupation theorem literally, instantiate its
-- rational product currency by
--
--      dangerCost          = 1,
--      dangerousResidence = sum C_i.
--
-- The expenditure is exactly sum C_i.  If the signed-ledger escape budget is
-- below compact-Gamma marginEscape, Round82 gives
--
--   sum N_i + delta sum D_i
--     <= initialPotential + remainderConstant.
--
-- Positive instantaneous drift is therefore allowed; only integrated adverse
-- cost is paid.  This closes the abstract #3 -> integrated-budget algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption as Absorb
import DASHI.Physics.Closure.NSTriadKNDeterministicDangerOccupationRound82Exact as Occupation
import DASHI.Physics.Closure.NSTriadKNIntegratedSignedDangerCostRound92Exact as Cost

rationalAbsorptionArithmetic : Absorb.AbsorptionArithmetic
rationalAbsorptionArithmetic = record
  { Absorb.Scalar = ℚ
  ; Absorb.zero = 0ℚ
  ; Absorb._+_ = _+_
  ; Absorb._≤_ = _≤_
  ; Absorb.≤-trans = ℚP.≤-trans
  ; Absorb.addZeroLeft = λ a → solve (a ∷ [])
  ; Absorb.addAssociative = λ a b c → solve (a ∷ b ∷ c ∷ [])
  ; Absorb.addCommutative = λ a b → solve (a ∷ b ∷ [])
  ; Absorb.additionMonotoneLeft =
      λ {a} {b} {c} a≤b → ℚP.+-mono-≤ ℚP.≤-refl a≤b
  ; Absorb.additionMonotoneRight =
      λ {a} {b} {c} a≤b → ℚP.+-mono-≤ a≤b ℚP.≤-refl
  ; Absorb.additionCancelRight =
      λ {a} {b} {c} bound → ℚP.+-cancelʳ-≤ c bound
  }

rationalOccupationProduct :
  Occupation.AbsorptionProductArithmetic rationalAbsorptionArithmetic
rationalOccupationProduct = record
  { Occupation._*_ = _*_
  }

record RationalIntegratedDangerOccupation (delta : ℚ) : Set₁ where
  constructor rational-integrated-danger-occupation
  field
    signedBudget : Cost.IntegratedDangerCostBudget delta
    absorption : Absorb.CompactGammaAbsorptionInputs rationalAbsorptionArithmetic

    escapeBudgetFitsMargin :
      Cost.escapeBudget signedBudget
      ≤ Absorb.marginEscape absorption

open RationalIntegratedDangerOccupation public

signedCostFitsEscapeMargin :
  ∀ {delta} (data : RationalIntegratedDangerOccupation delta) →
  Cost.sumDangerCost (Cost.cells (signedBudget data))
    ≤ Absorb.marginEscape (absorption data)
signedCostFitsEscapeMargin data =
  ℚP.≤-trans
    (Cost.dangerCostPaidByEscape (signedBudget data))
    (escapeBudgetFitsMargin data)

oneTimesCostMeaning : ∀ x → 1ℚ * x ≡ x
oneTimesCostMeaning x = solve (x ∷ [])

toDeterministicDangerOccupation :
  ∀ {delta} (data : RationalIntegratedDangerOccupation delta) →
  Occupation.DeterministicDangerOccupationInputs
    rationalAbsorptionArithmetic rationalOccupationProduct
toDeterministicDangerOccupation data = record
  { Occupation.absorption = absorption data
  ; Occupation.dangerCost = 1ℚ
  ; Occupation.dangerousResidence =
      Cost.sumDangerCost (Cost.cells (signedBudget data))
  ; Occupation.dangerOccupationConsumesEscapeMargin =
      subst
        (λ left → left ≤ Absorb.marginEscape (absorption data))
        (sym (oneTimesCostMeaning
          (Cost.sumDangerCost (Cost.cells (signedBudget data)))))
        (signedCostFitsEscapeMargin data)
  }

signedDangerCostBoundByCompactGamma :
  ∀ {delta} (data : RationalIntegratedDangerOccupation delta) →
  Cost.sumDangerCost (Cost.cells (signedBudget data))
  ≤ Absorb.initialPotential (absorption data)
      + Absorb.remainderConstant (absorption data)
signedDangerCostBoundByCompactGamma data =
  let
    raw = Occupation.deterministicDangerOccupationBound
      (toDeterministicDangerOccupation data)
    meaning = oneTimesCostMeaning
      (Cost.sumDangerCost (Cost.cells (signedBudget data)))
  in
  subst
    (λ left → left ≤
      Absorb.initialPotential (absorption data)
        + Absorb.remainderConstant (absorption data))
    meaning raw

integratedSignedCriticalEstimateFromOccupation :
  ∀ {delta} (data : RationalIntegratedDangerOccupation delta) →
  Cost.sumProduction (Cost.cells (signedBudget data))
    + delta * Cost.sumDissipation (Cost.cells (signedBudget data))
  ≤ Absorb.initialPotential (absorption data)
      + Absorb.remainderConstant (absorption data)
integratedSignedCriticalEstimateFromOccupation data =
  ℚP.≤-trans
    (Cost.finiteIntegratedSignedDangerCost
      (Cost.cells (signedBudget data)))
    (signedDangerCostBoundByCompactGamma data)

round92RationalDangerCostWeldToCompactGammaConstructed : Bool
round92RationalDangerCostWeldToCompactGammaConstructed = true

round92IntegratedSignedCriticalEstimateFromOccupationConstructed : Bool
round92IntegratedSignedCriticalEstimateFromOccupationConstructed = true

round92PhysicalSignedDangerCostEpisodeConstructed : Bool
round92PhysicalSignedDangerCostEpisodeConstructed = false

round92RationalDangerCostWeldToCompactGammaConstructedIsTrue :
  round92RationalDangerCostWeldToCompactGammaConstructed ≡ true
round92RationalDangerCostWeldToCompactGammaConstructedIsTrue = refl

round92IntegratedSignedCriticalEstimateFromOccupationConstructedIsTrue :
  round92IntegratedSignedCriticalEstimateFromOccupationConstructed ≡ true
round92IntegratedSignedCriticalEstimateFromOccupationConstructedIsTrue = refl
