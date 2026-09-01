{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPrincipalChartRound166Exact where

------------------------------------------------------------------------
-- ROUND166 A1 BIDI: PRINCIPAL-CHART ADMISSION DIRECTLY FROM THE LITERAL DEFECT
--
-- R165 proves on the exact Eq. (119) relative element
--
--   defect(U(Gamma_{c,x}) U(c)^-1) <= 1/24.
--
-- The only chart theorem now needed is the uniform standard recognition rule
-- saying that this operator-defect neighbourhood lies in the selected SU(2)
-- principal image.  This is one chart theorem, not a pointwise physical receipt.
-- Once supplied, every Round155 relative element is admitted and the existing
-- principal-log inverse law yields
--
--   exp(principalLog(relative)) = relative.
--
-- Thus the generic `PhysicalSU2PrincipalLogMeaning` wrapper is no longer needed
-- on the strongest Eq. (119) route.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (_≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98Equation119ExistingPrincipalLogRound156Exact as R156
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanCMP98Equation119ClosedPathSameObjectRound165Exact as R165
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

record DefectRecognizedPrincipalChart
    {C n Value group Radius}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : R164.LiteralRelativeDefectInputs source) : Set₁ where
  field
    chart : Log.StandardSU2PrincipalLogBall
      (R126.Vector (R146.additive C)) Value Radius

    defectBelowSourceThresholdImpliesPrincipalImage : ∀ value →
      Telescope.defect (R164.kernel inputs) value ≤ Chart.sourceDefectThreshold →
      Log.InPrincipalImage chart value

open DefectRecognizedPrincipalChart public

literalRelativeInPrincipalImage :
  ∀ {C n Value group Radius}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : R164.LiteralRelativeDefectInputs source)
    (recognition : DefectRecognizedPrincipalChart source inputs)
    step (point : Centered.CenteredBlockPoint4 6) →
  Log.InPrincipalImage (chart recognition)
    (R155.relativeContourElement (R158.asRound152Source source) step point)
literalRelativeInPrincipalImage source inputs recognition step point =
  defectBelowSourceThresholdImpliesPrincipalImage recognition
    (R155.relativeContourElement (R158.asRound152Source source) step point)
    (R165.literalRelativeElementDefectBelowSourceThreshold
      source inputs step point)

asRound156PrincipalImage :
  ∀ {C n Value group Radius}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : R164.LiteralRelativeDefectInputs source) →
  (recognition : DefectRecognizedPrincipalChart source inputs) →
  R156.RelativeContourPrincipalImage
    (R158.asRound152Source source)
    (chart recognition)
asRound156PrincipalImage source inputs recognition = record
  { R156.RelativeContourPrincipalImage.relativeInImage =
      literalRelativeInPrincipalImage source inputs recognition
  }

literalPrincipalPointYExponentiates :
  ∀ {C n Value group Radius}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (inputs : R164.LiteralRelativeDefectInputs source)
    (recognition : DefectRecognizedPrincipalChart source inputs)
    step point →
  Log.expSU2 (chart recognition)
    (R156.principalPointY
      (R158.asRound152Source source) (chart recognition) step point)
  ≡ R155.relativeContourElement
      (R158.asRound152Source source) step point
literalPrincipalPointYExponentiates source inputs recognition step point =
  R156.principalPointYExponentiatesToLiteralRelativeContour
    (R158.asRound152Source source)
    (chart recognition)
    (asRound156PrincipalImage source inputs recognition)
    step point

cmp98Equation119LiteralPrincipalChartRound166Level : ProofLevel
cmp98Equation119LiteralPrincipalChartRound166Level = machineChecked

cmp98Equation119LiteralPrincipalExpLogRound166Level : ProofLevel
cmp98Equation119LiteralPrincipalExpLogRound166Level = machineChecked

-- Remaining analytic chart leaf: instantiate this ONE standard recognition
-- theorem for the concrete SU(2) operator defect.  The pointwise Eq. (119)
-- admission is now fully downstream from R164-R165.
literalCMP98OperatorDefectPrincipalRecognitionRound166Level : ProofLevel
literalCMP98OperatorDefectPrincipalRecognitionRound166Level = standardImported
