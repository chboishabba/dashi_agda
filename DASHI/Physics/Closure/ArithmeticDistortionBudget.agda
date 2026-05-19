module DASHI.Physics.Closure.ArithmeticDistortionBudget where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_; _∸_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_,_)
import Data.Nat.Properties as NatP

import DASHI.Arithmetic.NormalizeAdd as NA
open import DASHI.Arithmetic.NormalizeAddState as NAS
import DASHI.Arithmetic.ArithmeticIntegerEmbeddingBridge as AIEB
import DASHI.Arithmetic.TrackedSupport as TS
import DASHI.Arithmetic.WeightedPressure as WP
import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DQ
import DASHI.Physics.Closure.DeltaQuadraticDistortion as DQD

------------------------------------------------------------------------
-- Canonical arithmetic distortion budget.
--
-- L0 is intentionally defined only from fields preserved by `normalizeAdd`.
-- It is therefore a finite per-state budget with a definitional
-- non-expansion proof for the canonical normalization path.

supportBudget : NormalizeAddState → Nat
supportBudget = NAS.prime

wallBudget : NormalizeAddState → Nat
wallBudget = NAS.padicDepth

residueBudget : NormalizeAddState → Nat
residueBudget s = NAS.lhs s + NAS.rhs s

L0 : NormalizeAddState → Nat
L0 s = supportBudget s + wallBudget s + residueBudget s

L0-normalizeAdd-nonexpansive :
  ∀ s → L0 (NA.normalizeAdd s) ≤ L0 s
L0-normalizeAdd-nonexpansive s = ≤-refl

canonicalPressureΔ : NormalizeAddState → Nat
canonicalPressureΔ = L0

canonicalEnergyQ : NormalizeAddState → Nat
canonicalEnergyQ = L0

epsilon : NormalizeAddState → Nat
epsilon = L0

canonicalDistortionBound :
  ∀ s →
  DQD.absDiff (canonicalEnergyQ s) (canonicalPressureΔ s)
  ≤
  epsilon s
canonicalDistortionBound s =
  ≤-trans (DQD.absDiff-refl≤0 (L0 s)) z≤n

canonicalArithmeticDistortion :
  DQD.DeltaQuadraticDistortion NormalizeAddState
canonicalArithmeticDistortion = record
  { pressureΔ = canonicalPressureΔ
  ; energyQ = canonicalEnergyQ
  ; epsilon = epsilon
  ; distortionBound = canonicalDistortionBound
  }

canonicalArithmeticOrder :
  DQD.DeltaQuadraticOrder NormalizeAddState
canonicalArithmeticOrder = record
  { pressureΔ = canonicalPressureΔ
  ; energyQ = canonicalEnergyQ
  ; control = λ q → q
  ; monotone-up-to = λ _ → ≤-refl
  }

canonicalBoundedDistortion :
  DQD.ControlledDeltaQuadraticTransform NormalizeAddState
canonicalBoundedDistortion = record
  { distortion = canonicalArithmeticDistortion
  ; order = canonicalArithmeticOrder
  }

------------------------------------------------------------------------
-- First nontrivial transported pair budget.
--
-- This is the computable DeltaPair comparison used for the next promotion
-- step.  The two sides are deliberately not definitionally equal:
--
--   pressureΔ = scalar cancellation pressure from the integer bridge
--   energyQ   = weighted pair energy from the Delta/Q bridge surface
--
-- The epsilon is now a structural support-only budget.  The weighted side is
-- controlled by the landed weighted support inequality; the unweighted scalar
-- side is controlled by the tracked support theorem.  The exact finite
-- difference remains named separately as a diagnostic surface.

pairPressureΔ : DQ.DeltaPair → Nat
pairPressureΔ =
  AIEB.embed-scalarCancellationPressure DQ.pairIntegerPressureBridge

pairEnergyQ : DQ.DeltaPair → Nat
pairEnergyQ = DQ.pairWeightedEnergy

pairExactEpsilon : DQ.DeltaPair → Nat
pairExactEpsilon s = DQD.absDiff (pairEnergyQ s) (pairPressureΔ s)

pairPressure≤trackedSupport :
  ∀ x y → pairPressureΔ (x , y) ≤ TS.trackedSupport x y
pairPressure≤trackedSupport x y = TS.totalPressure≤trackedSupport x y

pairStructuralEpsilon : DQ.DeltaPair → Nat
pairStructuralEpsilon (x , y) = WP.weightedSupport x y + TS.trackedSupport x y

pairEpsilon : DQ.DeltaPair → Nat
pairEpsilon = pairStructuralEpsilon

pairWeightedDistortionBound :
  ∀ s → DQD.absDiff (pairEnergyQ s) (pairPressureΔ s) ≤ pairEpsilon s
pairWeightedDistortionBound (x , y) =
  NatP.+-mono-≤
    (≤-trans
      (NatP.m∸n≤m (pairEnergyQ (x , y)) (pairPressureΔ (x , y)))
      (WP.weightedPressure≤weightedSupport x y))
    (≤-trans
      (NatP.m∸n≤m (pairPressureΔ (x , y)) (pairEnergyQ (x , y)))
      (pairPressure≤trackedSupport x y))

pairWeightedTransportedDistortion :
  DQD.DeltaQuadraticDistortion DQ.DeltaPair
pairWeightedTransportedDistortion = record
  { pressureΔ = pairPressureΔ
  ; energyQ = pairEnergyQ
  ; epsilon = pairEpsilon
  ; distortionBound = pairWeightedDistortionBound
  }

record PairSupportDistortionBudget (s : DQ.DeltaPair) : Set where
  field
    weightedSupportBudget :
      Nat

    trackedSupportBudget :
      Nat

    epsilonDecomposition :
      pairEpsilon s ≡ weightedSupportBudget + trackedSupportBudget

    weightedLegBound :
      pairEnergyQ s ∸ pairPressureΔ s ≤ weightedSupportBudget

    scalarLegBound :
      pairPressureΔ s ∸ pairEnergyQ s ≤ trackedSupportBudget

    combinedDistortionBound :
      DQD.absDiff (pairEnergyQ s) (pairPressureΔ s)
      ≤
      weightedSupportBudget + trackedSupportBudget

open PairSupportDistortionBudget public

pairSupportDistortionBudget :
  ∀ s → PairSupportDistortionBudget s
pairSupportDistortionBudget (x , y) = record
  { weightedSupportBudget = WP.weightedSupport x y
  ; trackedSupportBudget = TS.trackedSupport x y
  ; epsilonDecomposition = refl
  ; weightedLegBound =
      ≤-trans
        (NatP.m∸n≤m (pairEnergyQ (x , y)) (pairPressureΔ (x , y)))
        (WP.weightedPressure≤weightedSupport x y)
  ; scalarLegBound =
      ≤-trans
        (NatP.m∸n≤m (pairPressureΔ (x , y)) (pairEnergyQ (x , y)))
        (pairPressure≤trackedSupport x y)
  ; combinedDistortionBound = pairWeightedDistortionBound (x , y)
  }
