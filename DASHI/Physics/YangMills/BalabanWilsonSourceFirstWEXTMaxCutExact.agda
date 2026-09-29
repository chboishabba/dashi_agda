{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonSourceFirstWEXTMaxCutExact where

------------------------------------------------------------------------
-- SOURCE-FIRST REFINEMENT OF ROUND494 WEXT.
--
-- R494's two historical conditional leaves were:
--
--   W1 connected Wilson covariance = signed contributing-cluster sum
--   W3 absolute connecting-cluster weight sum <= physical rooted shell.
--
-- The source-first literal KP / marked-differentiation route now proves that
-- neither is primitive:
--
--   * KP + common finite cluster enumeration + source locality gives log Z;
--   * common-domain mixed differentiation filters exactly to two-support terms;
--   * finite triangle and pointwise-to-finite-sum monotonicity are algebra;
--   * R494 and R491 are then compiler endpoints.
--
-- The live physical/source payments beneath WEXT are therefore:
--
--   S1  instantiate the literal source-first KP family on the terminal gas;
--   S2  instantiate common-domain mixed differentiation on that same family;
--   S3  identify the CMP116 pointwise differentiated cluster charge;
--   S4  prove the SUM of those charges is below the physical rooted shell;
--   S5  identify the KP marked mixed log with the literal normalized finite-T5
--       mixed log on the same generating functional.  Connected covariance is
--       then generic source calculus.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonSourceFirstKPDataExact as KPSource
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonPhysicalKoteckyPreissExact as KPFamily
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedPolymerExpansionExact as Marked
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonCMP116ConnectingTailExact as Tail
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedKPT5SameObjectExact as KPT5
import DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Exact as R494
import DASHI.Physics.YangMills.BalabanWilsonTwoInsertionConnectedShellRound491Exact as R491

sourceFirstKPDatumConstructionLevel : ProofLevel
sourceFirstKPDatumConstructionLevel = machineChecked

sourceFirstKPFamilyAssemblyLevel : ProofLevel
sourceFirstKPFamilyAssemblyLevel = machineChecked

markedLogPartitionExpansionCompilerLevel : ProofLevel
markedLogPartitionExpansionCompilerLevel = machineChecked

twoSupportFilterCompilerLevel : ProofLevel
twoSupportFilterCompilerLevel = machineChecked

finiteTriangleAndChargeSummationCompilerLevel : ProofLevel
finiteTriangleAndChargeSummationCompilerLevel =
  Tail.twoWilsonConnectingTailCompilerLevel

round494AssemblyFromSourceFirstInputsLevel : ProofLevel
round494AssemblyFromSourceFirstInputsLevel =
  Tail.round494TwoMarkExpansionFromMarkedKPCompilerLevel

round491EndpointFromSourceFirstInputsLevel : ProofLevel
round491EndpointFromSourceFirstInputsLevel =
  R491.round491R274CompilerReuseLevel

------------------------------------------------------------------------
-- Exact live source cut.
------------------------------------------------------------------------

literalTerminalKPFamilyInstantiationLevel : ProofLevel
literalTerminalKPFamilyInstantiationLevel = conditional

commonDomainTwoWilsonDifferentiationLevel : ProofLevel
commonDomainTwoWilsonDifferentiationLevel = conditional

pointwiseCMP116ClusterChargeLevel : ProofLevel
pointwiseCMP116ClusterChargeLevel =
  Tail.twoWilsonPointwiseCMP116ChargeLevel

summedCMP116ChargeBelowPhysicalRootedShellLevel : ProofLevel
summedCMP116ChargeBelowPhysicalRootedShellLevel =
  Tail.twoWilsonChargeSumBelowRootedTailLevel

literalMarkedKPGeneratingFunctionalSameObjectLevel : ProofLevel
literalMarkedKPGeneratingFunctionalSameObjectLevel =
  KPT5.literalMarkedKPGeneratingFunctionalSameObjectLevel

finiteT5CovarianceAlgebraCompilerLevel : ProofLevel
finiteT5CovarianceAlgebraCompilerLevel =
  KPT5.finiteT5ConnectedCovarianceAlgebraLevel

signedMixedDerivativeIsFiniteWilsonCovarianceCompilerLevel : ProofLevel
signedMixedDerivativeIsFiniteWilsonCovarianceCompilerLevel =
  KPT5.markedKPT5MixedLogSameObjectCompilerLevel

------------------------------------------------------------------------
-- Pruned old payments.
------------------------------------------------------------------------

independentAbstractKPDatumSelectionRequired : Bool
independentAbstractKPDatumSelectionRequired = false

postHocKPActivityNormEqualityRequired : Bool
postHocKPActivityNormEqualityRequired = false

postHocKPIncompatibilityEqualityRequired : Bool
postHocKPIncompatibilityEqualityRequired = false

postHocKPRootedSumEqualityRequired : Bool
postHocKPRootedSumEqualityRequired = false

primitiveWilsonTwoMarkExpansionRequired : Bool
primitiveWilsonTwoMarkExpansionRequired = false

primitiveWilsonConnectingWeightTailRequired : Bool
primitiveWilsonConnectingWeightTailRequired = false

printedBalabanJEqualsWilsonLoopRequired : Bool
printedBalabanJEqualsWilsonLoopRequired = false

sourceFirstWEXTCompilerLevel : ProofLevel
sourceFirstWEXTCompilerLevel = machineChecked
