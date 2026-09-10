module DASHI.Physics.Closure.NSPreReleaseRateWeightedWaleffeSameObjectPriorityBidiExact where

------------------------------------------------------------------------
-- PRE-RELEASE PRIORITY ARCHAEOLOGY / RATE-WEIGHTED WALEFFE CHAIN
--
-- This owner records an exact composition whose ingredients all predate the
-- 2026-09-08 public OpenAI Navier--Stokes release.
--
-- Historical source lineage (Australia/Brisbane local times):
--
--   2026-08-27 23:20:20  b63934b8291289406ff0e2c9f7742b2659e006c4
--     exact selected-swap antisymmetry of actual Waleffe cells (R118)
--
--   2026-08-29 23:50:40  0930f36eb9b5d011608f248b7799da3bce375a85
--     fixed-output mixed-helicity product forcing swap collapse (R230)
--
--   2026-08-30 21:19:48  64e2a4d2b067a05c0a8cf979ea3ed74f960c56dc
--     arbitrary swap-invariant scalar weights preserve the R230 commutator
--     collapse before norms (R294)
--
--   2026-08-30 21:20:24  1e68a03918d7f71f9261487f633c74420865f7f9
--     the physical pair damping rate is swap invariant, hence every scalar
--     function of that rate supplies an R294 weight (R295)
--
--   2026-09-07 14:07:19  41f16207b77dfcb48f1264873de8a97822cc35c9
--     the literal weighted projected-forcing fixed-output fold is the same
--     quadratic-companion fold, with every outer cell classified slot-or-zero
--     (R438)
--
-- Thus the old R118 status flag saying critical selected-weight swap invariance
-- was not closed is stale as a GLOBAL historical reading: R295 later constructs
-- precisely the required swap-invariant weight family, and R438 carries the
-- weighted physical object through the exact projected-forcing/companion seam.
--
-- IMPORTANT FIREWALL
-- ------------------
-- This does NOT prove the final cutoff-uniform spacetime signed-companion
-- estimate.  It proves the representation/symmetry/same-object chain that
-- precedes that estimate.  In particular it does not promote Package A or
-- Clay-B, and it does not identify scalar selected-swap cancellation with the
-- vector-valued degenerate-cluster Gram cancellation theorem returned in Lean.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeSelectedSwapAntisymmetryRound118Exact as R118
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNCellRateSwapInvariantWeightRound295Exact as R295
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438

F : C3.RealField _
F = Rational.rationalRealField

record PreReleaseTheoremReceipt : Set where
  constructor pre-release-theorem-receipt
  field
    localTimestamp : String
    commitSHA : String
    theoremSurface : String

open PreReleaseTheoremReceipt public

r118Priority : PreReleaseTheoremReceipt
r118Priority = pre-release-theorem-receipt
  "2026-08-27T23:20:20+10:00"
  "b63934b8291289406ff0e2c9f7742b2659e006c4"
  "exact selected-swap antisymmetry on actual Waleffe cells"

r230Priority : PreReleaseTheoremReceipt
r230Priority = pre-release-theorem-receipt
  "2026-08-29T23:50:40+10:00"
  "0930f36eb9b5d011608f248b7799da3bce375a85"
  "fixed-output mixed-helicity forcing swap collapse"

r294Priority : PreReleaseTheoremReceipt
r294Priority = pre-release-theorem-receipt
  "2026-08-30T21:19:48+10:00"
  "64e2a4d2b067a05c0a8cf979ea3ed74f960c56dc"
  "swap-invariant weights preserve exact weighted commutator collapse"

r295Priority : PreReleaseTheoremReceipt
r295Priority = pre-release-theorem-receipt
  "2026-08-30T21:20:24+10:00"
  "1e68a03918d7f71f9261487f633c74420865f7f9"
  "physical pair-rate functions produce swap-invariant R294 weights"

r438Priority : PreReleaseTheoremReceipt
r438Priority = pre-release-theorem-receipt
  "2026-09-07T14:07:19+10:00"
  "41f16207b77dfcb48f1264873de8a97822cc35c9"
  "literal weighted projected-forcing fold equals quadratic-companion fold"

------------------------------------------------------------------------
-- The old R118 weight requirement is constructively paid by R295.
------------------------------------------------------------------------

preReleasePhysicalRateWeight :
  (rho : Z3.FourierMode → ℚ) →
  (phi : ℚ → C3.Complex F) →
  R294.SwapInvariantCellWeight F
preReleasePhysicalRateWeight = R295.rateFunctionBuildsR294Weight

preReleasePhysicalRateWeightSwapInvariant :
  (rho : Z3.FourierMode → ℚ) →
  (phi : ℚ → C3.Complex F) →
  (tau : Physical.PhysicalTriadIncidence) →
  R295.rateWeight rho phi (Symmetry.swapTriad tau)
  ≡ R295.rateWeight rho phi tau
preReleasePhysicalRateWeightSwapInvariant = R295.rateWeightSwapInvariant

------------------------------------------------------------------------
-- With that physical rate weight, the exact fixed-output product-rule forcing
-- is already the weighted mixed commutator before absolute values.
------------------------------------------------------------------------

preReleaseRateWeightedProductRuleIsCommutator :
  {E : C3.IntegerEmbedding F}
  {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (rho : Z3.FourierMode → ℚ) →
  (phi : ℚ → C3.Complex F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector
    (R294.weightedProductRuleCell
      (preReleasePhysicalRateWeight rho phi) S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
  ≡
  R224.foldVector
    (R294.weightedCommutatorCell
      (preReleasePhysicalRateWeight rho phi) S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
preReleaseRateWeightedProductRuleIsCommutator
    S velocity forcing rho phi cutoff output =
  R294.fixedOutputWeightedProductRuleIsCommutator
    (preReleasePhysicalRateWeight rho phi)
    S velocity forcing cutoff output

------------------------------------------------------------------------
-- R438 then carries the SAME weighted physical object into the exhaustive
-- slot-or-zero quadratic-companion fold.
------------------------------------------------------------------------

preReleaseRateWeightedProjectedForcingIsQuadraticCompanion :
  {E : C3.IntegerEmbedding F}
  {I : C3.ModeInverseSquare F E}
  {S : Helical.HelicalModeScalars F}
  {L : Helical.PeriodicHelicalProjectorLaws F E I S}
  {H : R142.HelicalHalfCalibration S} →
  (rho : Z3.FourierMode → ℚ) →
  (phi : ℚ → C3.Complex F) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  ((mode : Z3.FourierMode) →
    Helical.Transverse E mode (Audit.velocity system mode)) →
  (output : Z3.FourierMode) →
  R438.foldDoubleWeightedProjectedForcing
    (preReleasePhysicalRateWeight rho phi) S system
    (Output.physicalOutputFiber (Audit.cutoff system) output)
  ≡
  R438.foldExhaustiveWeightedCompanion
    (preReleasePhysicalRateWeight rho phi) S system
    (Output.physicalOutputFiber (Audit.cutoff system) output)
preReleaseRateWeightedProjectedForcingIsQuadraticCompanion
    rho phi system velocityTransverse output =
  R438.fixedOutputDoubleWeightedR294FoldIsQuadraticCompanion
    (preReleasePhysicalRateWeight rho phi)
    system velocityTransverse output

------------------------------------------------------------------------
-- Status correction and remaining analytic firewall.
------------------------------------------------------------------------

preReleaseSelectedSwapAntisymmetryPresent : Bool
preReleaseSelectedSwapAntisymmetryPresent =
  R118.round118ActualSelectedSwapCellAntisymmetryClosed

preReleaseRateWeightSymmetryPresent : Bool
preReleaseRateWeightSymmetryPresent =
  R295.round295CellDampingRateSwapInvariant

preReleaseWeightedCommutatorCollapsePresent : Bool
preReleaseWeightedCommutatorCollapsePresent =
  R294.round294GenericSwapInvariantWeightedCollapseClosed

preReleaseWeightedSameObjectCompanionFoldPresent : Bool
preReleaseWeightedSameObjectCompanionFoldPresent =
  R438.round438FixedOutputWeightedSameObjectFoldClosed

preReleaseCutoffUniformSignedCompanionEstimateProvedHere : Bool
preReleaseCutoffUniformSignedCompanionEstimateProvedHere = false

preReleaseVectorClusterCancellationProvedHere : Bool
preReleaseVectorClusterCancellationProvedHere = false

preReleasePackageAProvedHere : Bool
preReleasePackageAProvedHere = false

preReleaseClayBProvedHere : Bool
preReleaseClayBProvedHere = false

preReleaseRateWeightSymmetryPresentIsTrue :
  preReleaseRateWeightSymmetryPresent ≡ true
preReleaseRateWeightSymmetryPresentIsTrue =
  R295.round295CellDampingRateSwapInvariantIsTrue

preReleaseWeightedCommutatorCollapsePresentIsTrue :
  preReleaseWeightedCommutatorCollapsePresent ≡ true
preReleaseWeightedCommutatorCollapsePresentIsTrue =
  R294.round294GenericSwapInvariantWeightedCollapseClosedIsTrue

preReleaseWeightedSameObjectCompanionFoldPresentIsTrue :
  preReleaseWeightedSameObjectCompanionFoldPresent ≡ true
preReleaseWeightedSameObjectCompanionFoldPresentIsTrue =
  R438.round438FixedOutputWeightedSameObjectFoldClosedIsTrue

preReleaseCutoffUniformSignedCompanionEstimateProvedHereIsFalse :
  preReleaseCutoffUniformSignedCompanionEstimateProvedHere ≡ false
preReleaseCutoffUniformSignedCompanionEstimateProvedHereIsFalse = refl
