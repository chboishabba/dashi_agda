module DASHI.Physics.Closure.NSCompactGammaPotentialDerivative where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSBoundedPotentialTurnoverBudget as Potential
import DASHI.Physics.Closure.NSNormalizedAlignmentBudgetDerivative as Quotient

------------------------------------------------------------------------
-- Division-free derivative surface for
--
--   B = Q₊ / (Q₊ + V),   V = 2 ν D.
--
-- On a resolved positive-transfer branch Q₊ = Q, set T = Q + V.  The
-- differential identities
--
--   Q = B T
--   Q' = B' T + B T'
--
-- instantiate the generic normalized-budget quotient rule.  The positive-part
-- kink Q = 0 is intentionally outside this classical derivative surface.
------------------------------------------------------------------------

record CompactGammaDerivativeInputs
    (R : Quotient.BudgetProductArithmetic) : Set₁ where
  field
    Q V T B : Quotient.Scalar R
    Qdot Vdot Tdot Bdot : Quotient.Scalar R

    totalIsTransferPlusViscous :
      T ≡ Quotient._+_ R Q V

    totalDerivativeIsTransferPlusViscous :
      Tdot ≡ Quotient._+_ R Qdot Vdot

    transferIsCompactTimesTotal :
      Q ≡ Quotient._*_ R B T

    differentiatedTransferIdentity :
      Qdot ≡ Quotient._+_ R
        (Quotient._*_ R Bdot T)
        (Quotient._*_ R B Tdot)

open CompactGammaDerivativeInputs public

compactGammaCrossMultipliedQuotientRule :
  (R : Quotient.BudgetProductArithmetic) →
  (I : CompactGammaDerivativeInputs R) →
  Quotient._*_ R (Qdot I) (T I) ≡
  Quotient._+_ R
    (Quotient._*_ R (Quotient._*_ R (Bdot I) (T I)) (T I))
    (Quotient._*_ R (Q I) (Tdot I))
compactGammaCrossMultipliedQuotientRule R I =
  Quotient.normalizedAlignmentCrossMultipliedQuotientRule R normalized
  where
  normalized : Quotient.NormalizedAlignmentDerivativeInputs R
  normalized = record
    { E = T I
    ; N = Q I
    ; A = B I
    ; Edot = Tdot I
    ; Ndot = Qdot I
    ; Adot = Bdot I
    ; numeratorIsNormalizedTimesEnstrophy =
        transferIsCompactTimesTotal I
    ; differentiatedNumeratorIdentity =
        differentiatedTransferIdentity I
    }

------------------------------------------------------------------------
-- Once a PDE-facing theorem proves that dangerous Gamma consumes the
-- one-sided decrease of B, the already-proved bounded-potential theorem gives
-- the residence bound.  This adapter keeps compact-Gamma semantics explicit
-- without duplicating the potential proof.
------------------------------------------------------------------------

record CompactGammaResidenceInputs
    (A : Potential.PotentialBudgetArithmetic) : Set₁ where
  field
    compactPotentialBalance : Potential.BoundedPotentialBalance A
    dangerCost : Potential.Scalar A
    dangerousResidence : Potential.Scalar A

    dangerousGammaConsumesCompactEscape :
      Potential._≤_ A
        (Potential._*_ A dangerCost dangerousResidence)
        (Potential.depletionIntegral compactPotentialBalance)

open CompactGammaResidenceInputs public

compactGammaPotentialForcesResidenceBound :
  (A : Potential.PotentialBudgetArithmetic) →
  (I : CompactGammaResidenceInputs A) →
  Potential._≤_ A
    (Potential._*_ A (dangerCost I) (dangerousResidence I))
    (Potential._+_ A
      (Potential.initialPotential (compactPotentialBalance I))
      (Potential.replenishmentIntegral (compactPotentialBalance I)))
compactGammaPotentialForcesResidenceBound A I =
  Potential.boundedPotentialForcesResidenceBound A adapted
  where
  adapted : Potential.BoundedPotentialResidenceInputs A
  adapted = record
    { potentialBalance = compactPotentialBalance I
    ; dangerCost = dangerCost I
    ; dangerousResidence = dangerousResidence I
    ; dangerousTransferConsumesSignedEscape =
        dangerousGammaConsumesCompactEscape I
    }
