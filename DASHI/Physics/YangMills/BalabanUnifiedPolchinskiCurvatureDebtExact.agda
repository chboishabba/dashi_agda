module DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact where

------------------------------------------------------------------------
-- ROUND69: 17/32 LOCAL-HESSIAN DECAY -> FINITE MULTISCALE CURVATURE DEBT
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Roland Bauerschmidt and Thierry Bodineau,
-- "Log-Sobolev Inequality for the Continuum Sine-Gordon Model",
-- Communications on Pure and Applied Mathematics 74 (2021), 2064--2113.
-- DOI: 10.1002/cpa.21926.
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- DASHI CONTRIBUTION
--
-- Bauerschmidt--Bodineau allow the Polchinski curvature rate dotMu_t to be
-- negative; what matters is the accumulated curvature history in the source
-- integral.  Therefore the useful L7 output is not pointwise positivity at
-- every scale but a UNIFORM TOTAL NEGATIVE CURVATURE DEBT.
--
-- If eta_n >= 0 majorises the negative heat-smoothed Hessian contribution at
-- scale n and eta_n <= C (17/32)^n, then every finite cumulative debt obeys
--
--      sum_{n < m} eta_n <= (32/15) C.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact as Tail
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondIterationExact as Iter

record GeometricNegativeCurvatureDebt : Set₁ where
  field
    debtAtScale : Nat → ℚ
    debtNonnegative : ∀ n → 0ℚ ≤ debtAtScale n
    amplitude : ℚ
    amplitudeNonnegative : 0ℚ ≤ amplitude
    geometricDebtBound : ∀ n →
      debtAtScale n ≤ amplitude * Iter.thetaPower n
open GeometricNegativeCurvatureDebt public

asIncrementMajorant :
  GeometricNegativeCurvatureDebt → Tail.GeometricUnifiedIncrementMajorant
asIncrementMajorant dataSet = record
  { Tail.GeometricUnifiedIncrementMajorant.increment = debtAtScale dataSet
  ; Tail.GeometricUnifiedIncrementMajorant.amplitude = amplitude dataSet
  ; Tail.GeometricUnifiedIncrementMajorant.amplitudeNonnegative =
      amplitudeNonnegative dataSet
  ; Tail.GeometricUnifiedIncrementMajorant.incrementBound =
      geometricDebtBound dataSet
  }

finiteCurvatureDebt : GeometricNegativeCurvatureDebt → Nat → ℚ
finiteCurvatureDebt dataSet count =
  Tail.finiteIncrementTail (asIncrementMajorant dataSet) zero count

finiteCurvatureDebtUniformBound :
  (dataSet : GeometricNegativeCurvatureDebt) → ∀ count →
  finiteCurvatureDebt dataSet count
  ≤ Tail.tailFactor * amplitude dataSet
finiteCurvatureDebtUniformBound dataSet count =
  let
    base = Tail.finiteIncrementTailModulus
      (asIncrementMajorant dataSet) zero count
  in
  subst
    (λ right → finiteCurvatureDebt dataSet count ≤ right)
    (ℚRing.solve-∀ (Tail.tailFactor) (amplitude dataSet))
    base

record PolchinskiDiscreteCurvatureBudget : Set₁ where
  field
    negativeDebt : GeometricNegativeCurvatureDebt

    -- Conversion between one discrete RG shell and the continuous Polchinski
    -- time parameter.  This remains a named physical comparison, not a silent
    -- identification of a dyadic shell sum with dt integration.
    shellToContinuousCurvatureDebt : Set

    continuousNegativeCurvatureDebt : ℚ
    continuousDebtBelowDiscreteMajorant :
      continuousNegativeCurvatureDebt
      ≤ Tail.tailFactor * amplitude negativeDebt

open PolchinskiDiscreteCurvatureBudget public

seventeenThirtySecondCurvatureDebtLevel : ProofLevel
seventeenThirtySecondCurvatureDebtLevel = machineChecked

physicalUnifiedPolchinskiCurvatureDebtLevel : ProofLevel
physicalUnifiedPolchinskiCurvatureDebtLevel = conditional
