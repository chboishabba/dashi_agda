{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ThreeProfileOrbitClosureWallRound784Exact where

------------------------------------------------------------------------
-- ROUND784 / THREE-PROFILE CANCELLATION NOW HAS ONE EXACT ORBIT-CLOSURE SEAM
--
-- R782:
--   every fully-separated incidence has exactly one of
--
--     (LH,HH,HL), (HL,HL,HH), (HH,LH,LH).
--
-- R783:
--   the fully-separated swap-paired W2 residual is exactly the sum of three
--   corresponding base-class folds.
--
-- Existing pre-R650 orbit machinery already proves:
--   * pEnergyLeg and qEnergyLeg preserve the literal cutoff enumeration;
--   * each is involutive on lattice coordinates;
--   * the ordinary ordered-pair energy transfer cancels on the complete
--     three-leg orbit.
--
-- What is NOT yet packaged for the new R781/R783 mask is the exact statement
--
--   ccTouched (pEnergyLeg beta) = ccTouched beta
--   ccTouched (qEnergyLeg beta) = ccTouched beta.
--
-- That is the shortest next theorem.  Once it is proved, the three surviving
-- profile folds are closed under the literal energy-leg orbit and the signed
-- residual can be tested orbit-by-orbit before any estimate.
--
-- This owner intentionally does not infer that the old energy-transfer
-- cancellation applies to the new residual cell; that same-object identity is
-- a subsequent theorem, not a consequence of orbit closure alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitFibreRound38Exact as OrbitFibre
import DASHI.Physics.Closure.NSTriadKNEnergyCancellationAssembly as EnergyOrbit
import DASHI.Physics.Closure.NSTriadKNR650FullySeparatedOrbitProfileSupportRound782Exact as R782
import DASHI.Physics.Closure.NSTriadKNR650FullySeparatedThreeProfileResidualRound783Exact as R783

round784FullySeparatedProfileSupportReducedToThree : Bool
round784FullySeparatedProfileSupportReducedToThree =
  R782.round782FullySeparatedProfileSupportFinite

round784FullySeparatedResidualSplitIntoThreeFolds : Bool
round784FullySeparatedResidualSplitIntoThreeFolds =
  R783.round783FullySeparatedResidualExactlyThreeBaseFolds

round784EnergyLegCutoffCarrierClosed : Bool
round784EnergyLegCutoffCarrierClosed =
  OrbitFibre.physicalTriadOrbitActionOnCutoffClosed

round784OrdinaryThreeLegEnergyCancellationAvailable : Bool
round784OrdinaryThreeLegEnergyCancellationAvailable =
  EnergyOrbit.energyCancellationAssemblyClosed

round784CCTouchedPEnergyInvariantClosed : Bool
round784CCTouchedPEnergyInvariantClosed = false

round784CCTouchedQEnergyInvariantClosed : Bool
round784CCTouchedQEnergyInvariantClosed = false

round784NewResidualIdentifiedWithOldEnergyTransfer : Bool
round784NewResidualIdentifiedWithOldEnergyTransfer = false

round784ThreeProfileCancellationClosed : Bool
round784ThreeProfileCancellationClosed = false

round784IntroducesEstimate : Bool
round784IntroducesEstimate = false

round784W2Closed : Bool
round784W2Closed = false

round784ClayPromotion : Bool
round784ClayPromotion = false

round784FullySeparatedProfileSupportReducedToThreeIsTrue :
  round784FullySeparatedProfileSupportReducedToThree ≡ true
round784FullySeparatedProfileSupportReducedToThreeIsTrue =
  R782.round782FullySeparatedProfileSupportFiniteIsTrue

round784FullySeparatedResidualSplitIntoThreeFoldsIsTrue :
  round784FullySeparatedResidualSplitIntoThreeFolds ≡ true
round784FullySeparatedResidualSplitIntoThreeFoldsIsTrue =
  R783.round783FullySeparatedResidualExactlyThreeBaseFoldsIsTrue

round784EnergyLegCutoffCarrierClosedIsTrue :
  round784EnergyLegCutoffCarrierClosed ≡ true
round784EnergyLegCutoffCarrierClosedIsTrue =
  OrbitFibre.physicalTriadOrbitActionOnCutoffClosedIsTrue

round784OrdinaryThreeLegEnergyCancellationAvailableIsTrue :
  round784OrdinaryThreeLegEnergyCancellationAvailable ≡ true
round784OrdinaryThreeLegEnergyCancellationAvailableIsTrue =
  EnergyOrbit.energyCancellationAssemblyClosedIsTrue

round784CCTouchedPEnergyInvariantClosedIsFalse :
  round784CCTouchedPEnergyInvariantClosed ≡ false
round784CCTouchedPEnergyInvariantClosedIsFalse = refl

round784CCTouchedQEnergyInvariantClosedIsFalse :
  round784CCTouchedQEnergyInvariantClosed ≡ false
round784CCTouchedQEnergyInvariantClosedIsFalse = refl

round784NewResidualIdentifiedWithOldEnergyTransferIsFalse :
  round784NewResidualIdentifiedWithOldEnergyTransfer ≡ false
round784NewResidualIdentifiedWithOldEnergyTransferIsFalse = refl

round784ThreeProfileCancellationClosedIsFalse :
  round784ThreeProfileCancellationClosed ≡ false
round784ThreeProfileCancellationClosedIsFalse = refl

round784IntroducesEstimateIsFalse :
  round784IntroducesEstimate ≡ false
round784IntroducesEstimateIsFalse = refl

round784W2ClosedIsFalse :
  round784W2Closed ≡ false
round784W2ClosedIsFalse = refl

round784ClayPromotionIsFalse :
  round784ClayPromotion ≡ false
round784ClayPromotionIsFalse = refl
