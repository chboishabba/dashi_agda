module DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkRegression where

-- RED/GREEN contract for the post-#920 Gate-A tranche.
-- Production must preserve the merged R571 paired-second-moment carrier,
-- reuse existing donors for A1/G2/G1, isolate A2 as the radial-curvature leaf,
-- and must not promote R568 or a Clay endpoint.

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact as GateA
import DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureBoundaryExact as A2
import DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureSquareGapExact as A2Square

preferredLinearizationClosed :
  GateA.r571GateAPreferredLinearizationClosed ≡ true
preferredLinearizationClosed = refl

existingA1GeometryDonorRetained :
  GateA.r571GateAA1ReverseTriangleDonorLocated ≡ true
existingA1GeometryDonorRetained = refl

existingG2PathDonorRetained :
  GateA.r571GateAG2FinitePathDonorLocated ≡ true
existingG2PathDonorRetained = refl

existingG1ModalEnvelopeDonorRetained :
  GateA.r571GateAG1ModalEnergyDonorLocated ≡ true
existingG1ModalEnvelopeDonorRetained = refl

radialCurvatureIsOnlyNewLocalLeaf :
  A2.r571A2RadialCurvatureIsolated ≡ true
radialCurvatureIsOnlyNewLocalLeaf = refl

radialCurvatureSquareGapRationalizationClosed :
  A2Square.r571A2CenteredRadiusDefectSquareGapRationalized ≡ true
radialCurvatureSquareGapRationalizationClosed = refl

radialCurvatureUsesExistingGapProductDonor :
  A2Square.r571A2R127SquareGapAlgebraReused ≡ true
radialCurvatureUsesExistingGapProductDonor = refl

radialCurvatureDenominatorPaymentStillOpen :
  A2Square.r571A2OrderedRadialDenominatorPaymentClosed ≡ false
radialCurvatureDenominatorPaymentStillOpen = refl

radialCurvatureNotFalselyPromoted :
  A2.r571A2UniformCurvatureEstimateClosed ≡ false
radialCurvatureNotFalselyPromoted = refl

r568StillOpen :
  GateA.r571GateAClosesR568 ≡ false
r568StillOpen = refl
