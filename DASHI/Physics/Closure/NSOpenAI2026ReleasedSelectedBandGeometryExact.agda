module DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedBandGeometryExact where

------------------------------------------------------------------------
-- NATIVE PORT: RELEASED SELECTED BAND GEOMETRY
--
-- Source:
--   ActualCycleParameters.bandFloor
--   ActualCandidateConstruction.firstBand
--   ActualCandidateConstruction.residualBand
--
-- This tranche is pure finite arithmetic.  It fixes exactly the source rule
--
--   firstBand    = max 4 bandFloor
--   residualBand = firstBand + 1
--
-- and proves the inequalities used to place every physical prefix inside the
-- original validity region.  No PDE/analytic estimate is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Physics.Closure.NSOpenAI2026ReleasedActualCandidatePhysicalInputsExact
  as Inputs

------------------------------------------------------------------------
-- 1. Small native max library, kept local so the source rule is transparent.
------------------------------------------------------------------------

natMax : Nat → Nat → Nat
natMax zero n = n
natMax (suc m) zero = suc m
natMax (suc m) (suc n) = suc (natMax m n)

≤-refl : (n : Nat) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n _ = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

left≤max : (m n : Nat) → m ≤ natMax m n
left≤max zero n = z≤n
left≤max (suc m) zero = ≤-refl (suc m)
left≤max (suc m) (suc n) = s≤s (left≤max m n)

right≤max : (m n : Nat) → n ≤ natMax m n
right≤max zero n = ≤-refl n
right≤max (suc m) zero = z≤n
right≤max (suc m) (suc n) = s≤s (right≤max m n)

n≤sucn : (n : Nat) → n ≤ suc n
n≤sucn zero = z≤n
n≤sucn (suc n) = s≤s (n≤sucn n)

------------------------------------------------------------------------
-- 2. Exact source construction.
------------------------------------------------------------------------

four : Nat
four = suc (suc (suc (suc zero)))

firstBand : Nat → Nat
firstBand bandFloor = natMax four bandFloor

residualBand : Nat → Nat
residualBand bandFloor = suc (firstBand bandFloor)

firstBandFour :
  (bandFloor : Nat) →
  four ≤ firstBand bandFloor
firstBandFour bandFloor = left≤max four bandFloor

firstBandGeFloor :
  (bandFloor : Nat) →
  bandFloor ≤ firstBand bandFloor
firstBandGeFloor bandFloor = right≤max four bandFloor

record ReleasedBandFloorEvidence : Set where
  field
    selectedThreshold : Nat
    bandFloor : Nat
    selectedThreshold≤bandFloor :
      selectedThreshold ≤ bandFloor

open ReleasedBandFloorEvidence public

selectedThreshold≤firstBand :
  (E : ReleasedBandFloorEvidence) →
  selectedThreshold E ≤ firstBand (bandFloor E)
selectedThreshold≤firstBand E =
  ≤-trans
    (selectedThreshold≤bandFloor E)
    (firstBandGeFloor (bandFloor E))

firstBand≤residualBand :
  (bandFloor : Nat) →
  firstBand bandFloor ≤ residualBand bandFloor
firstBand≤residualBand bandFloor =
  n≤sucn (firstBand bandFloor)

four≤residualBand :
  (bandFloor : Nat) →
  four ≤ residualBand bandFloor
four≤residualBand bandFloor =
  ≤-trans
    (firstBandFour bandFloor)
    (firstBand≤residualBand bandFloor)

selectedThreshold≤residualBand :
  (E : ReleasedBandFloorEvidence) →
  selectedThreshold E ≤ residualBand (bandFloor E)
selectedThreshold≤residualBand E =
  ≤-trans
    (selectedThreshold≤firstBand E)
    (firstBand≤residualBand (bandFloor E))

------------------------------------------------------------------------
-- 3. Tie directly to the source-fixed physical-input record.
------------------------------------------------------------------------

hardFloorMatchesPhysicalInput :
  Inputs.firstBandHardFloor ≡ four
hardFloorMatchesPhysicalInput = refl

residualOffsetMatchesPhysicalInput :
  Inputs.residualBandOffset ≡ 1
residualOffsetMatchesPhysicalInput = refl

releasedFirstBandRulePorted : Bool
releasedFirstBandRulePorted = true

releasedResidualBandRulePorted : Bool
releasedResidualBandRulePorted = true

releasedThresholdFloorInequalitiesPorted : Bool
releasedThresholdFloorInequalitiesPorted = true

releasedFirstBandRulePortedIsTrue :
  releasedFirstBandRulePorted ≡ true
releasedFirstBandRulePortedIsTrue = refl

releasedResidualBandRulePortedIsTrue :
  releasedResidualBandRulePorted ≡ true
releasedResidualBandRulePortedIsTrue = refl

releasedThresholdFloorInequalitiesPortedIsTrue :
  releasedThresholdFloorInequalitiesPorted ≡ true
releasedThresholdFloorInequalitiesPortedIsTrue = refl
