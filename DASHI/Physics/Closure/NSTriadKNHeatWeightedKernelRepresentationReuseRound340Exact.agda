module DASHI.Physics.Closure.NSTriadKNHeatWeightedKernelRepresentationReuseRound340Exact where

------------------------------------------------------------------------
-- ROUND340 / BIDI REUSE: THE WEIGHTED-KERNEL REPRESENTATION SEAM IS OLD
--
-- A deeper repository audit finds that the generic weighted Schur layer already
-- protects the exact authority boundary needed by the new F_s operator route.
-- `WeightedKernelSchurTest.ExactKernelAction` says that an abstract `applyKernel`
-- is not enough: the action must be proved to be evaluation of the declared
-- kernel entries.  `KernelIdentityMatch` then transports an already-certified
-- candidate only after kernel AND row/column weights agree.
--
-- `NSWeightedShellTransferBridge` carries the same discipline into the old NS
-- factorized K01 -> R0 -> K10 route.  Its `representsK01` / `representsK10`
-- witnesses are deliberately proof-relevant and are consumed before either
-- weighted Schur certificate can become a physical cross-shell bound.
--
-- Therefore the current R299/R329 heat-factorized nested remainder does not
-- need a new Schur or factorization abstraction.  Its next same-object producer
-- is only the representation weld:
--
--   literal nested F_s shell action
--      == declared weighted kernel action(s)
--
-- on the exact physical incidence fibres and weights.
--
-- R299's scalar identity
--
--   pair remainder = 4 * aggregate amplitude/forcing cross
--
-- is downstream-compatible algebra, but it does not itself construct K01/K10,
-- an ExactKernelAction, or the representation witnesses.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Analysis.WeightedKernelSchurTest as Weighted
import DASHI.Physics.Closure.NSWeightedShellTransferBridge as Transfer
import DASHI.Physics.Closure.NSFactorizedCrossShellBound as Factorized
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNHeatWeightedOperatorTTStarReuseRound338Exact as R338
import DASHI.Physics.Closure.NSTriadKNNestedDominantCommonHatReuseRound339Exact as R339

data RepresentationLeaf : Set where
  literalFsKernelEntries : RepresentationLeaf
  exactKernelAction : RepresentationLeaf
  kernelIdentityMatch : RepresentationLeaf
  physicalK01Representation : RepresentationLeaf
  physicalK10Representation : RepresentationLeaf
  weightedCertificates : RepresentationLeaf
  factorizedCrossShellEvidence : RepresentationLeaf

data LeafState : Set where closed open blocked : LeafState

leafState : RepresentationLeaf → LeafState
leafState literalFsKernelEntries = open
leafState exactKernelAction = blocked
leafState kernelIdentityMatch = blocked
leafState physicalK01Representation = blocked
leafState physicalK10Representation = blocked
leafState weightedCertificates = blocked
leafState factorizedCrossShellEvidence = blocked

weightedKernelInfrastructureDisposition : Admission.RouteDisposition
weightedKernelInfrastructureDisposition = Admission.redirectedReuse

weightedTransferBridgeDisposition : Admission.RouteDisposition
weightedTransferBridgeDisposition = Admission.redirectedReuse

newParallelSchurAbstractionDisposition : Admission.RouteDisposition
newParallelSchurAbstractionDisposition = Admission.rejected Admission.alreadyOwned

literalFsKernelRepresentationDisposition : Admission.RouteDisposition
literalFsKernelRepresentationDisposition = Admission.admitted

round340WeightedKernelIdentityMatchAlreadyOwned : Bool
round340WeightedKernelIdentityMatchAlreadyOwned = true

round340ExactKernelActionAuthorityBoundaryAlreadyOwned : Bool
round340ExactKernelActionAuthorityBoundaryAlreadyOwned = true

round340PhysicalK01K10RepresentationBoundaryAlreadyOwned : Bool
round340PhysicalK01K10RepresentationBoundaryAlreadyOwned = true

round340FactorizedThreeStageCompilerAlreadyOwned : Bool
round340FactorizedThreeStageCompilerAlreadyOwned = true

round340R299ScalarFactorizationAlreadyClosed : Bool
round340R299ScalarFactorizationAlreadyClosed =
  R299.round299FinitePairFactorizationCompilerClosed

round340R299ScalarFactorizationConstructsExactKernelAction : Bool
round340R299ScalarFactorizationConstructsExactKernelAction = false

round340R339LocalCommonHatsConstructOperatorRepresentation : Bool
round340R339LocalCommonHatsConstructOperatorRepresentation = false

round340LiteralFsKernelEntriesClosed : Bool
round340LiteralFsKernelEntriesClosed = false

round340ExactFsKernelActionClosed : Bool
round340ExactFsKernelActionClosed = false

round340PhysicalK01K10RepresentationClosed : Bool
round340PhysicalK01K10RepresentationClosed = false

round340WeightedCertificatesClosed : Bool
round340WeightedCertificatesClosed = false

round340FactorizedFsCrossShellEvidenceClosed : Bool
round340FactorizedFsCrossShellEvidenceClosed = false

round340PackageAClosed : Bool
round340PackageAClosed = false

round340ClayPromotion : Bool
round340ClayPromotion = false

round340R299ScalarFactorizationAlreadyClosedIsTrue :
  round340R299ScalarFactorizationAlreadyClosed ≡ true
round340R299ScalarFactorizationAlreadyClosedIsTrue = refl

round340R299ScalarFactorizationConstructsExactKernelActionIsFalse :
  round340R299ScalarFactorizationConstructsExactKernelAction ≡ false
round340R299ScalarFactorizationConstructsExactKernelActionIsFalse = refl

round340PackageAClosedIsFalse : round340PackageAClosed ≡ false
round340PackageAClosedIsFalse = refl

round340ClayPromotionIsFalse : round340ClayPromotion ≡ false
round340ClayPromotionIsFalse = refl
