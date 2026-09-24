module DASHI.Physics.Closure.NSClayFacingAAnalyticCutExact where

------------------------------------------------------------------------
-- CLAY-FACING A: PHYSICAL SAME-OBJECT DEBT VS STANDARD ANALYSIS
--
-- The whole-space lane previously exposed "integrability" as one opaque leaf.
-- For a Clay-facing mathematical proof that is too coarse.  The standard
-- functional-analysis tail should be cited/instantiated; the research content
-- is the physical pointwise majorization on the exact compensated NS carrier.
--
-- LOW:
--   research  : actual compensated low-frequency NS integrand
--               <= compact-output convolution envelope.
--   standard  : Young/Cauchy (or equivalent) makes that envelope L1.
--
-- HIGH:
--   research  : actual state-side high-frequency quantity
--               <= inverse-sixth weighted convolution envelope.
--   standard  : |xi|^-6 is integrable at infinity in R3 and ordinary
--               convolution estimates close the envelope.
--
-- Agda/Lean reconstruction of the standard theorem is optional verification
-- and must not be confused with the physical same-object inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSWholeSpaceProjectedSaturationOriginBoundExact as Origin
import DASHI.Physics.Closure.NSWholeSpacePhysicalKernelSaturationOriginExact as KernelOrigin
import DASHI.Physics.Closure.NSTriadKNEuclideanCenteredResolventScaleRelativeExact as HighCurvature

data ObligationKind : Set where
  physicalSameObjectResearch : ObligationKind
  standardCitableAnalysis : ObligationKind
  compilerOnly : ObligationKind

data ClayFacingStatus : Set where
  openResearch : ClayFacingStatus
  dischargedByStandardTheorem : ClayFacingStatus
  compilerClosed : ClayFacingStatus

record AObligation : Set where
  constructor a-obligation
  field
    name : String
    kind : ObligationKind
    status : ClayFacingStatus
    agdaKernelReconstructionRequiredForPaper : Bool

open AObligation public

lowPhysicalPointwiseDomination : AObligation
lowPhysicalPointwiseDomination = a-obligation
  "instantiate the physical resolvent kernel as the already-proved projected saturation origin cell and identify its state majorant"
  physicalSameObjectResearch
  openResearch
  false

lowEnvelopeIntegrability : AObligation
lowEnvelopeIntegrability = a-obligation
  "compact-output convolution envelope is L1 by standard Young/Cauchy estimates"
  standardCitableAnalysis
  dischargedByStandardTheorem
  false

highPhysicalPointwiseDomination : AObligation
highPhysicalPointwiseDomination = a-obligation
  "identify the actual high-frequency physical resolvent/state quantity with the already-proved scale-relative curvature envelope"
  physicalSameObjectResearch
  openResearch
  false

highEnvelopeIntegrability : AObligation
highEnvelopeIntegrability = a-obligation
  "inverse-sixth weighted convolution envelope is L1 on R3 by standard tail/convolution estimates"
  standardCitableAnalysis
  dischargedByStandardTheorem
  false

lowHighCompiler : AObligation
lowHighCompiler = a-obligation
  "low/high physical majorants compile into the compensated Lebesgue endgame"
  compilerOnly
  compilerClosed
  false

aGenericYoungCauchyIsResearchFrontier : Bool
aGenericYoungCauchyIsResearchFrontier = false

aGenericInverseSixthTailIsResearchFrontier : Bool
aGenericInverseSixthTailIsResearchFrontier = false

aLocalProjectedOriginCancellationClosed : Bool
aLocalProjectedOriginCancellationClosed =
  Origin.wholeSpaceProjectedSaturationOriginBoundClosed

aPhysicalKernelOriginCompilerClosed : Bool
aPhysicalKernelOriginCompilerClosed =
  KernelOrigin.lowFrequencyPhysicalKernelSaturationCompilerClosed

aHighFrequencyScaleRelativeCurvatureClosed : Bool
aHighFrequencyScaleRelativeCurvatureClosed =
  HighCurvature.euclideanHighFrequencyScaleRelativeCurvatureClosed

aLocalLowFrequencySingularityIsResearchFrontier : Bool
aLocalLowFrequencySingularityIsResearchFrontier = false

aPhysicalLowSameObjectDominationClosed : Bool
aPhysicalLowSameObjectDominationClosed = false

aPhysicalHighSameObjectDominationClosed : Bool
aPhysicalHighSameObjectDominationClosed = false

aClayFacingFirstResidualIsPhysicalSameObjectDomination : Bool
aClayFacingFirstResidualIsPhysicalSameObjectDomination = true

aGenericYoungCauchyIsResearchFrontierIsFalse :
  aGenericYoungCauchyIsResearchFrontier ≡ false
aGenericYoungCauchyIsResearchFrontierIsFalse = refl

aGenericInverseSixthTailIsResearchFrontierIsFalse :
  aGenericInverseSixthTailIsResearchFrontier ≡ false
aGenericInverseSixthTailIsResearchFrontierIsFalse = refl

aLocalLowFrequencySingularityIsResearchFrontierIsFalse :
  aLocalLowFrequencySingularityIsResearchFrontier ≡ false
aLocalLowFrequencySingularityIsResearchFrontierIsFalse = refl

aLocalProjectedOriginCancellationClosedIsTrue :
  aLocalProjectedOriginCancellationClosed ≡ true
aLocalProjectedOriginCancellationClosedIsTrue = refl

aPhysicalKernelOriginCompilerClosedIsTrue :
  aPhysicalKernelOriginCompilerClosed ≡ true
aPhysicalKernelOriginCompilerClosedIsTrue = refl

aHighFrequencyScaleRelativeCurvatureClosedIsTrue :
  aHighFrequencyScaleRelativeCurvatureClosed ≡ true
aHighFrequencyScaleRelativeCurvatureClosedIsTrue = refl

aClayFacingFirstResidualIsPhysicalSameObjectDominationIsTrue :
  aClayFacingFirstResidualIsPhysicalSameObjectDomination ≡ true
aClayFacingFirstResidualIsPhysicalSameObjectDominationIsTrue = refl
