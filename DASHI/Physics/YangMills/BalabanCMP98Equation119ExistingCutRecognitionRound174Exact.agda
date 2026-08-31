{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119ExistingCutRecognitionRound174Exact where

------------------------------------------------------------------------
-- ROUND174 A1 BIDI: REUSE THE EXISTING PRINCIPAL-LOG CUT OWNER
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations",
-- 2nd ed. Springer (2015). DOI: 10.1007/978-3-319-13467-3.
--
-- R166 exposed one uniform recognition theorem
--
--   defect(U) <= 1/24 -> U in principal image.
--
-- The repository already owns the stronger structural theorem through
-- `PrincipalLogCutData`: defect below a selected cut radius implies the
-- canonical admissibility predicate.  Eq. (119) therefore does not get a
-- second recognition theorem.  It needs only same-object identifications plus
-- the scalar inclusion
--
--   1/24 <= existing chart radius.
--
-- Equality of the two radii is deliberately NOT required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPrincipalChartRound166Exact as R166
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale

record ExistingCutRecognition
    {C n Value group Radius}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : R164.LiteralRelativeDefectInputs source) : Set₁ where
  field
    cut : Path.PrincipalLogCutData Value ℚ
    chart : Log.StandardSU2PrincipalLogBall
      (R126.Vector (R146.additive C)) Value Radius

    cutDefectIsOperatorDefect : ∀ value →
      Path.defect (Path.defectAlgebra cut) value
      ≡ Telescope.defect (R164.kernel inputs) value

    cutOrderIsRationalOrder :
      Scale.LessEqual (Path.scale (Path.defectAlgebra cut))
      ≡ _≤_

    sourceThresholdBelowCutRadius :
      Chart.sourceDefectThreshold ≤ Path.chartRadius cut

    cutAdmissibleIsPrincipalImage :
      Path.PrincipalLogAdmissible cut
      ≡ Log.InPrincipalImage chart

open ExistingCutRecognition public

existingCutRecognizesSourceThreshold :
  ∀ {C n Value group Radius}
    {source : R158.CanonicalL13Equation119Source C n Value group}
    {inputs : R164.LiteralRelativeDefectInputs source}
    (existing : ExistingCutRecognition source inputs)
    value →
  Telescope.defect (R164.kernel inputs) value ≤ Chart.sourceDefectThreshold →
  Log.InPrincipalImage (chart existing) value
existingCutRecognizesSourceThreshold {inputs = inputs} existing value operatorBound =
  let
    cutAlgebra = Path.defectAlgebra (cut existing)

    operatorBelowCut :
      Telescope.defect (R164.kernel inputs) value
      ≤ Path.chartRadius (cut existing)
    operatorBelowCut =
      ℚP.≤-trans operatorBound (sourceThresholdBelowCutRadius existing)

    cutDefectBoundRational :
      Path.defect cutAlgebra value ≤ Path.chartRadius (cut existing)
    cutDefectBoundRational =
      subst
        (λ lower → lower ≤ Path.chartRadius (cut existing))
        (sym (cutDefectIsOperatorDefect existing value))
        operatorBelowCut

    cutDefectBound :
      Scale.LessEqual (Path.scale cutAlgebra)
        (Path.defect cutAlgebra value)
        (Path.chartRadius (cut existing))
    cutDefectBound =
      subst
        (λ relation → relation
          (Path.defect cutAlgebra value)
          (Path.chartRadius (cut existing)))
        (sym (cutOrderIsRationalOrder existing))
        cutDefectBoundRational

    admitted : Path.PrincipalLogAdmissible (cut existing) value
    admitted =
      Path.defectBelowRadiusImpliesAdmissible
        (cut existing) value cutDefectBound
  in
  subst
    (λ predicate → predicate value)
    (cutAdmissibleIsPrincipalImage existing)
    admitted

asRound166Recognition :
  ∀ {C n Value group Radius}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : R164.LiteralRelativeDefectInputs source) →
  ExistingCutRecognition source inputs →
  R166.DefectRecognizedPrincipalChart source inputs
asRound166Recognition source inputs existing = record
  { R166.DefectRecognizedPrincipalChart.chart = chart existing
  ; R166.DefectRecognizedPrincipalChart.defectBelowSourceThresholdImpliesPrincipalImage =
      existingCutRecognizesSourceThreshold existing
  }

cmp98Equation119ExistingCutRecognitionRound174Level : ProofLevel
cmp98Equation119ExistingCutRecognitionRound174Level = machineChecked

literalCMP98ExistingCutSameObjectRound174Level : ProofLevel
literalCMP98ExistingCutSameObjectRound174Level = conditional
