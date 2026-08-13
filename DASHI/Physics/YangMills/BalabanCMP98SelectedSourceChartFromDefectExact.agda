module DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- SOURCE FACTS
--
-- Equation (25), p. 21: for the principal logarithm of a unitary matrix in the
-- stated branch,
--
--       |log U| <= (pi/2) |U-1|.
--
-- Equation (38), p. 23, permits O(1)=24 on
--
--       |X| <= 1/20,    |Y| <= 1/12.
--
-- DASHI CONTRIBUTION
--
-- Avoid introducing pi into the rational proof carrier.  The elementary
-- source-safe relaxation pi/2 <= 2 shows that the Y-chart condition follows
-- from the purely rational defect threshold
--
--       |U-1| <= 1/24  ==>  |log U| <= 1/12.
--
-- Thus the selected-point G1 task can be attacked on the literal relative
-- holonomy before evaluating any logarithm.  The X and Y conditions are kept
-- separate because X is the perturbation generator while Y is the base-point
-- logarithm in equation (38).
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38

sourceDefectThreshold : ℚ
sourceDefectThreshold = + 1 / 24

two : ℚ
two = + 2 / 1

record PrincipalLogDefectBound
    (defectMagnitude logMagnitude : ℚ) : Set where
  field
    defectNonnegative : 0ℚ ≤ defectMagnitude
    logNonnegative : 0ℚ ≤ logMagnitude
    rationalizedEquation25 : logMagnitude ≤ two * defectMagnitude

open PrincipalLogDefectBound public

defectOneTwentyFourthImpliesYRadius :
  ∀ defectMagnitude logMagnitude →
  PrincipalLogDefectBound defectMagnitude logMagnitude →
  defectMagnitude ≤ sourceDefectThreshold →
  logMagnitude ≤ Eq38.sourceYRadius
defectOneTwentyFourthImpliesYRadius
    defectMagnitude logMagnitude source defectSmall =
  let
    scaled : two * defectMagnitude ≤ two * sourceDefectThreshold
    scaled = Norm.scaleNonnegative two
      (ℚP.nonNegative⁻¹ two) defectSmall
  in
  ℚP.≤-trans (rationalizedEquation25 source)
    (subst
      (λ upper → two * defectMagnitude ≤ upper)
      (ℚRing.solve [] : two * sourceDefectThreshold ≡ Eq38.sourceYRadius)
      scaled)

record SelectedEquation38ChartPoint : Set where
  field
    perturbationMagnitude baseDefectMagnitude baseLogMagnitude : ℚ
    perturbationNonnegative : 0ℚ ≤ perturbationMagnitude
    baseLogFromDefect :
      PrincipalLogDefectBound baseDefectMagnitude baseLogMagnitude
    perturbationInside : perturbationMagnitude ≤ Eq38.sourceXRadius
    baseDefectInside : baseDefectMagnitude ≤ sourceDefectThreshold

open SelectedEquation38ChartPoint public

selectedPointProducesEquation38SourceChart :
  (point : SelectedEquation38ChartPoint) →
  Eq38.Equation38SourceChart
    (perturbationMagnitude point)
    (baseLogMagnitude point)
selectedPointProducesEquation38SourceChart point = record
  { Eq38.Equation38SourceChart.inputNonnegative =
      perturbationNonnegative point
  ; Eq38.Equation38SourceChart.baseNonnegative =
      logNonnegative (baseLogFromDefect point)
  ; Eq38.Equation38SourceChart.inputInsideSourceChart =
      perturbationInside point
  ; Eq38.Equation38SourceChart.baseInsideSourceChart =
      defectOneTwentyFourthImpliesYRadius
        (baseDefectMagnitude point)
        (baseLogMagnitude point)
        (baseLogFromDefect point)
        (baseDefectInside point)
  }

cmp98RationalizedEquation25ChartLevel : ProofLevel
cmp98RationalizedEquation25ChartLevel = machineChecked

cmp98SelectedSourceChartFromDefectLevel : ProofLevel
cmp98SelectedSourceChartFromDefectLevel = machineChecked
