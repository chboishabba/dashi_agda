module DASHI.Physics.YangMills.BalabanUnifiedPolymerStepVContractionBudgetExact where

------------------------------------------------------------------------
-- ROUND66: EXPLICIT d=4 POLYMER CONTRACTION HEADROOM
--
-- PRIMARY SOURCES / CALIBRATION
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- David C. Brydges, P. K. Mitter and B. Scoppola,
-- "Critical (Phi^4)_{3,epsilon}", Communications in Mathematical Physics
-- 240 (2003), 281--327. DOI: 10.1007/s00220-003-0895-4.
--
-- P. K. Mitter, "A non trivial fixed point in a three dimensional quantum
-- field theory", Oberwolfach Report 17/2006, The Rigorous Renormalization
-- Group. DOI of report: 10.4171/OWR/2006/17.
--
-- DASHI CONTRIBUTION
--
-- Existing Step V gives a rooted KP budget <=1/2 once the physical shell bound
-- is supplied.  Round66 assigns the large-polymer rescaling branch the explicit
-- dyadic d=4 target 1/32.  If the two costs add in ONE corrected norm,
--
--     1/2 + 1/32 = 17/32,
--
-- leaving exact headroom 15/32.  The global theta<1 condition is therefore
-- replaced by a concrete numerical target; the physical work is the finite
-- small-polymer extraction and proving the large branch in the same norm.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _≤_; _<_; _/_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanCorrectedSmallPolymerExtractionContractionExact as Extract

seventeenThirtySeconds fifteenThirtySeconds : ℚ
seventeenThirtySeconds = + 17 / 32
fifteenThirtySeconds = + 15 / 32

kpPlusLargeContractionExact :
  StepV.half + Extract.oneThirtySecond ≡ seventeenThirtySeconds
kpPlusLargeContractionExact = ℚRing.solve []

contractionBudgetPlusHeadroomIsOne :
  seventeenThirtySeconds + fifteenThirtySeconds ≡ 1ℚ
contractionBudgetPlusHeadroomIsOne = ℚRing.solve []

contractionHeadroomPositive : 0ℚ < fifteenThirtySeconds
contractionHeadroomPositive =
  let
    instance
      marginPositive : Positive fifteenThirtySeconds
      marginPositive = ℚP.normalize-pos 15 32
  in
  ℚP.positive⁻¹ fifteenThirtySeconds

record AdditiveStepVContractionBudget (Bound : Set) : Set₁ where
  field
    rational : ℚ → Bound
    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    smallAndKPCost largeRescalingCost totalCost : Bound

    smallAndKPBelowHalf : LessEqual smallAndKPCost (rational StepV.half)
    largeBelowOneThirtySecond :
      LessEqual largeRescalingCost (rational Extract.oneThirtySecond)

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    totalCostExact : totalCost ≡ add smallAndKPCost largeRescalingCost
    rationalAddExact : ∀ left right →
      add (rational left) (rational right) ≡ rational (left + right)

open AdditiveStepVContractionBudget public

combinedStepVCostBelowSeventeenThirtySeconds :
  ∀ {Bound} (dataSet : AdditiveStepVContractionBudget Bound) →
  LessEqual dataSet (totalCost dataSet) (rational dataSet seventeenThirtySeconds)
combinedStepVCostBelowSeventeenThirtySeconds dataSet =
  let
    base = addMonotone dataSet
      (smallAndKPBelowHalf dataSet)
      (largeBelowOneThirtySecond dataSet)

    fromTotal = subst
      (λ lower → LessEqual dataSet lower
        (add dataSet
          (rational dataSet StepV.half)
          (rational dataSet Extract.oneThirtySecond)))
      (sym (totalCostExact dataSet))
      base

    rationalSum = subst
      (λ upper → LessEqual dataSet (totalCost dataSet) upper)
      (rationalAddExact dataSet StepV.half Extract.oneThirtySecond)
      fromTotal
  in
  subst
    (λ upper → LessEqual dataSet (totalCost dataSet) upper)
    (cong (rational dataSet) kpPlusLargeContractionExact)
    rationalSum

stepVContractionBudgetArithmeticLevel : ProofLevel
stepVContractionBudgetArithmeticLevel = machineChecked

physicalUnifiedStepVContractionBudgetLevel : ProofLevel
physicalUnifiedStepVContractionBudgetLevel = conditional
