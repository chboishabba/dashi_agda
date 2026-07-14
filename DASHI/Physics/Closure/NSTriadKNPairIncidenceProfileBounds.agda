module DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileBounds where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_; z≤n; s≤s; _<_; _∸_; _≥_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Nat.Properties using (≤-refl; <⇒≤; *-identityˡ)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecompositionReceipt as Profiles
import DASHI.Physics.Closure.NSTriadKNForcedTailClosureDependency as ForcedTailClosure
import DASHI.Physics.Closure.NSTriadKNForcedTailWeightedProductBoundReceipt as ForcedTail
import DASHI.Physics.Closure.NSTriadKNAdversarialClosureDependency as AdversarialClosure
import DASHI.Physics.Closure.NSTriadKNTransitionClosureDependency as TransitionClosure
import DASHI.Physics.Closure.NSTriadKNResidualClosureDependency as ResidualClosure
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix as CrossMatrix
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductAnalyticAudit as CrossAudit
import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound as WeightedSchur
import DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem as CNTheorem
import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
import DASHI.Physics.Closure.NSTriadKNGramBaseGapBridge as GramBase
import DASHI.Physics.Closure.NSTriadKNGramRayleighBaseForm as GramRayleigh
import DASHI.Physics.Closure.NSTriadKNGramRayleighBaseFormBridge as GramRayleighBridge
import DASHI.Physics.Closure.NSTriadKNExactGramBaseFormBridge as ExactGramBridge
import DASHI.Physics.Closure.NSTriadKNExactQNBaseForm as ExactQBase
import DASHI.Physics.Closure.NSTriadKNRayleighCoercivityStage3MarginBridge as MarginBridge
import DASHI.Physics.Closure.NSTriadKNSchurResidueScale as ResidueScale
import DASHI.Physics.Closure.NSTriadKNBKMResidenceBridge as BKMBridge
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom
import DASHI.Physics.Closure.NSTriadKNWeakOperatorErrorModel as WeakError
import DASHI.Physics.Closure.NSTriadKNWeakQuadraticFormControl as WeakQuadratic
import DASHI.Physics.Closure.NSTriadKNScaledOperatorErrorAudit as ScaledErrorAudit




------------------------------------------------------------------------
-- Fail-closed analytic surface for the four-profile weighted Schur bounds.
--
-- This is the first genuinely hard Stage 3 theorem layer after the kernel
-- formula and profile taxonomy: prove profile-wise weighted row/column product
-- bounds, then combine them into the global weighted Schur product theorem.

data NSTriadKNPairIncidenceProfileBoundsPromotion : Set where

pairIncidenceProfileBoundsPromotionImpossibleHere :
  NSTriadKNPairIncidenceProfileBoundsPromotion → ⊥
pairIncidenceProfileBoundsPromotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed analytic receipt for the NS triad exact scripted pair-incidence profile-wise weighted Schur bounds."

canonicalKernelObject : String
canonicalKernelObject =
  "K^N(k,p) := -L_FT,script^N(k,p)"

canonicalWeightTarget : String
canonicalWeightTarget =
  "Choose positive weights w_N adapted to the exact scripted shell profile."

canonicalRowFunctional : String
canonicalRowFunctional =
  "R_N^r(w) := sup_i (1 / w_i) * sum_j K_N^r(i,j) * w_j."

canonicalColumnFunctional : String
canonicalColumnFunctional =
  "C_N^r(w) := sup_j (1 / w_j) * sum_i K_N^r(i,j) * w_i."

canonicalForcedTailTarget : String
canonicalForcedTailTarget =
  "Forced-tail target: R_N^FT(w_N) * C_N^FT(w_N) <= C_FT^2 / N^2."

canonicalAdversarialTarget : String
canonicalAdversarialTarget =
  "Adversarial target: R_N^adv(w_N) * C_N^adv(w_N) <= C_adv^2 / N^2."

canonicalTransitionTarget : String
canonicalTransitionTarget =
  "Transition target: R_N^trans(w_N) * C_N^trans(w_N) <= C_trans^2 / N^2."

canonicalResidualTarget : String
canonicalResidualTarget =
  "Residual target: R_N^res(w_N) * C_N^res(w_N) <= C_res^2 / N^2."

canonicalCombinationTarget : String
canonicalCombinationTarget =
  "Global weighted Schur route: if K_N = sum_r K_N^r, prove the full cross-profile matrix R_N^p(w_N) * C_N^q(w_N) <= C_{p,q} / N^2 for all profiles p,q, then conclude R_N(w_N) * C_N(w_N) <= C^2 / N^2."

canonicalForcedTailRouteNote : String
canonicalForcedTailRouteNote =
  "Forced-tail, adversarial, transition, residual domination, the 16-entry cross matrix, weighted Schur, and the PairIncidence C/N route are now closed on the active chain. The live blocker has moved downstream to ResidueScaleCompatibility."

canonicalReadoutText : String
canonicalReadoutText =
  "Profile-bounds status: the structural four-profile decomposition, the full 16-entry profile cross-product matrix, the global weighted Schur product theorem, and the PairIncidence C/N operator route are now closed on the active chain. Blocker 2A open: current unit-shell witness is trivial/model-only; actual Stage 3 pair-incidence operator is not yet exposed. The next honest theorem is no longer a profile-product estimate. It is the Blocker 2 residue/gap scaling bridge: construct ResidueScaleCompatibility so the operator C/N theorem yields q_gap(N) >= c / N^2 through an explicit weak/strong norm scaling and base-gap-minus-error absorption argument. The forced-tail sampled witness remains historical evidence only; theorem authority for the active chain now comes from the depth-bearing profile route plus the still-open residue/gap compatibility layer."

record NSTriadKNPairIncidenceProfileBounds : Setω where
  constructor mkNSTriadKNPairIncidenceProfileBounds
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNPairIncidenceProfileBounds"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    profileDecompositionReceiptName : String
    profileDecompositionReceiptNameIsCanonical :
      profileDecompositionReceiptName ≡
        "NSTriadKNPairIncidenceProfileDecompositionReceipt"

    profileDecompositionReadoutText : String
    profileDecompositionReadoutTextIsCanonical :
      profileDecompositionReadoutText ≡
        Profiles.canonicalReadoutText

    forcedTailWitnessReadoutText : String
    forcedTailWitnessReadoutTextIsCanonical :
      forcedTailWitnessReadoutText ≡ ForcedTail.canonicalReadoutText

    kernelObject : String
    kernelObjectIsCanonical :
      kernelObject ≡ canonicalKernelObject

    weightTarget : String
    weightTargetIsCanonical :
      weightTarget ≡ canonicalWeightTarget

    rowFunctional : String
    rowFunctionalIsCanonical :
      rowFunctional ≡ canonicalRowFunctional

    columnFunctional : String
    columnFunctionalIsCanonical :
      columnFunctional ≡ canonicalColumnFunctional

    forcedTailTarget : String
    forcedTailTargetIsCanonical :
      forcedTailTarget ≡ canonicalForcedTailTarget

    adversarialTarget : String
    adversarialTargetIsCanonical :
      adversarialTarget ≡ canonicalAdversarialTarget

    transitionTarget : String
    transitionTargetIsCanonical :
      transitionTarget ≡ canonicalTransitionTarget

    residualTarget : String
    residualTargetIsCanonical :
      residualTarget ≡ canonicalResidualTarget

    combinationTarget : String
    combinationTargetIsCanonical :
      combinationTarget ≡ canonicalCombinationTarget

    forcedTailRouteNote : String
    forcedTailRouteNoteIsCanonical :
      forcedTailRouteNote ≡ canonicalForcedTailRouteNote

    readoutText : String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    theoremSurfaceImplemented : Bool
    theoremSurfaceImplementedIsTrue :
      theoremSurfaceImplemented ≡ true

    forcedTailFirstRouteStated : Bool
    forcedTailFirstRouteStatedIsTrue :
      forcedTailFirstRouteStated ≡ true

    sampledForcedTailWitnessInstalled : Bool
    sampledForcedTailWitnessInstalledIsTrue :
      sampledForcedTailWitnessInstalled ≡ true

    forcedTailWeightedProductBoundClosed : Bool
    forcedTailWeightedProductBoundClosedIsTrue :
      forcedTailWeightedProductBoundClosed ≡ true

    adversarialWeightedProductBoundClosed : Bool
    adversarialWeightedProductBoundClosedIsTrue :
      adversarialWeightedProductBoundClosed ≡ true

    transitionWeightedProductBoundClosed : Bool
    transitionWeightedProductBoundClosedIsTrue :
      transitionWeightedProductBoundClosed ≡ true

    residualWeightedProductBoundClosed : Bool
    residualWeightedProductBoundClosedIsTrue :
      residualWeightedProductBoundClosed ≡ true

    profileWiseWeightedProductBoundsClosed : Bool
    profileWiseWeightedProductBoundsClosedIsTrue :
      profileWiseWeightedProductBoundsClosed ≡ true

    profileCrossProductMatrixClosed : Bool
    profileCrossProductMatrixClosedIsTrue :
      profileCrossProductMatrixClosed ≡ true

    weightedSchurProductBoundClosed : Bool
    weightedSchurProductBoundClosedIsTrue :
      weightedSchurProductBoundClosed ≡ true

    pairIncidenceCNTheoremClosed : Bool
    pairIncidenceCNTheoremClosedIsTrue :
      pairIncidenceCNTheoremClosed ≡ true

    qGapTransferClosed : Bool
    qGapTransferClosedIsFalse :
      qGapTransferClosed ≡ false

    schurResidueScaleClosed : Bool
    schurResidueScaleClosedIsFalse :
      schurResidueScaleClosed ≡ false

    integratedResidueN2BoundClosed : Bool
    integratedResidueN2BoundClosedIsFalse :
      integratedResidueN2BoundClosed ≡ false

    integratedDangerFromSchurResidueClosed : Bool
    integratedDangerFromSchurResidueClosedIsFalse :
      integratedDangerFromSchurResidueClosed ≡ false

    residenceTimeExclusionClosed : Bool
    residenceTimeExclusionClosedIsFalse :
      residenceTimeExclusionClosed ≡ false

    bkmProjectionSmallnessClosed : Bool
    bkmProjectionSmallnessClosedIsFalse :
      bkmProjectionSmallnessClosed ≡ false

    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    bkmExclusionProved : Bool
    bkmExclusionProvedIsFalse :
      bkmExclusionProved ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNPairIncidenceProfileBounds public

compatibilityShellIndex : Nat
compatibilityShellIndex = suc zero

compatibilityCarrierElement :
  ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex
compatibilityCarrierElement =
  ResidueNorm.mkResidueEnergyCarrier 0

canonicalShellScaleHeadroom :
  ScaleHeadroom.ShellScaleHeadroom compatibilityShellIndex
canonicalShellScaleHeadroom =
  ScaleHeadroom.headroomFromSucN
    compatibilityShellIndex
    (s≤s (s≤s z≤n))

canonicalCompatibilityScale :
  ScaleHeadroom.CompatibilityScale compatibilityShellIndex
canonicalCompatibilityScale =
  ScaleHeadroom.compatibilityScaleFromHeadroom canonicalShellScaleHeadroom

canonicalScaledOperatorErrorMarginClosed : Bool
canonicalScaledOperatorErrorMarginClosed =
  ScaledErrorAudit.canonicalScaledOperatorErrorMarginClosed

canonicalScaledOperatorErrorMarginClosedIsFalse :
  canonicalScaledOperatorErrorMarginClosed ≡ false
canonicalScaledOperatorErrorMarginClosedIsFalse =
  ScaledErrorAudit.canonicalScaledOperatorErrorMarginClosedIsFalse

canonicalSharperScaledOperatorErrorBridgeClosed : Bool
canonicalSharperScaledOperatorErrorBridgeClosed =
  ScaledErrorAudit.canonicalSharperScaledOperatorErrorBridgeClosed

canonicalSharperScaledOperatorErrorBridgeClosedIsFalse :
  canonicalSharperScaledOperatorErrorBridgeClosed ≡ false
canonicalSharperScaledOperatorErrorBridgeClosedIsFalse =
  ScaledErrorAudit.canonicalSharperScaledOperatorErrorBridgeClosedIsFalse

canonicalStage3StrictKernelDefectClosed : Bool
canonicalStage3StrictKernelDefectClosed =
  ScaledErrorAudit.canonicalStage3StrictKernelDefectClosed

canonicalStage3StrictKernelDefectClosedIsFalse :
  canonicalStage3StrictKernelDefectClosed ≡ false
canonicalStage3StrictKernelDefectClosedIsFalse =
  ScaledErrorAudit.canonicalStage3StrictKernelDefectClosedIsFalse

canonicalProfileCrossProductAnalyticClosed : Bool
canonicalProfileCrossProductAnalyticClosed =
  CrossAudit.canonicalProfileCrossProductAnalyticClosed

canonicalProfileCrossProductAnalyticClosedIsFalse :
  canonicalProfileCrossProductAnalyticClosed ≡ false
canonicalProfileCrossProductAnalyticClosedIsFalse =
  CrossAudit.canonicalProfileCrossProductAnalyticClosedIsFalse

canonicalResidueNormModel :
  ResidueNorm.ResidueNormModel
canonicalResidueNormModel =
  ResidueNorm.nWeightedResidueNormModel

------------------------------------------------------------------------
-- Blocker 2A currently has two layers:
--   1. model-only plumbing used to keep the weak-quadratic-form lane typed;
--   2. the actual Stage 3 operator witness, still missing and fail-closed.

modelOperatorWitness :
  CNTheorem.PairIncidenceOperatorWitness canonicalResidueNormModel compatibilityShellIndex
modelOperatorWitness =
  CNTheorem.stage3ToPairIncidenceOperatorWitness
    (CNTheorem.actualUnitShellPairIncidenceOperatorWitness
      canonicalResidueNormModel)

actualOperatorWitnessTarget : Set₁
actualOperatorWitnessTarget =
  CNTheorem.ActualUnitShellPairIncidenceOperatorWitnessTarget
    canonicalResidueNormModel

actualOperatorWitnessClosed : Bool
actualOperatorWitnessClosed =
  CNTheorem.actualUnitShellPairIncidenceOperatorWitnessClosed

actualOperatorWitnessClosedIsFalse :
  actualOperatorWitnessClosed ≡ false
actualOperatorWitnessClosedIsFalse =
  CNTheorem.actualUnitShellPairIncidenceOperatorWitnessClosedIsFalse

canonicalWeakQuadraticFormControlTarget :
  WeakQuadratic.WeakQuadraticFormControlTarget
canonicalWeakQuadraticFormControlTarget =
  WeakQuadratic.mkUnitShellWeakQuadraticFormControlTargetFromStage3Witness
    canonicalResidueNormModel
    (CNTheorem.actualUnitShellPairIncidenceOperatorWitness
      canonicalResidueNormModel)
    (CNTheorem.PairIncidenceOperatorWitness.absQuadraticForm
      modelOperatorWitness)
    (λ _ → refl)

canonicalActualWeakQuadraticForm :
  ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex → Nat
canonicalActualWeakQuadraticForm =
  WeakQuadratic.WeakQuadraticFormControlTarget.actualWeakQuadraticForm
    canonicalWeakQuadraticFormControlTarget

canonicalActualWeakQuadraticFormAtUnitEnergy :
  canonicalActualWeakQuadraticForm
    (ResidueNorm.mkResidueEnergyCarrier (suc zero))
    ≡ suc zero
canonicalActualWeakQuadraticFormAtUnitEnergy = refl

canonicalAbsPairIncidenceQuadraticForm :
  ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex → Nat
canonicalAbsPairIncidenceQuadraticForm =
  WeakQuadratic.WeakQuadraticFormControlTarget.AbsPairIncidenceQuadraticForm
    canonicalWeakQuadraticFormControlTarget

canonicalWeakQuadraticFormConstant : Nat
canonicalWeakQuadraticFormConstant =
  WeakQuadratic.WeakQuadraticFormControlTarget.weakQuadraticFormConstant
    canonicalWeakQuadraticFormControlTarget

canonicalWeakQuadraticFormConstantIsOne :
  canonicalWeakQuadraticFormConstant ≡ suc zero
canonicalWeakQuadraticFormConstantIsOne = refl

postulate
  realActualWeakQuadraticForm :
    ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex → Nat

  actualPairIncidenceQuadraticFormBoundedByWitness :
    (x : ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex) →
    realActualWeakQuadraticForm x
      ≤
      WeakQuadratic.WeakQuadraticFormControlTarget.AbsPairIncidenceQuadraticForm
        canonicalWeakQuadraticFormControlTarget
        x

actualQuadraticFormBoundedByWitnessClosed : Bool
actualQuadraticFormBoundedByWitnessClosed = false

actualQuadraticFormBoundedByWitnessClosedIsFalse :
  actualQuadraticFormBoundedByWitnessClosed ≡ false
actualQuadraticFormBoundedByWitnessClosedIsFalse = refl

canonicalWeakOperatorErrorModelTarget :
  WeakError.WeakOperatorErrorModelTarget
canonicalWeakOperatorErrorModelTarget =
  WeakQuadratic.toWeakOperatorErrorModelTarget
    canonicalWeakQuadraticFormControlTarget

canonicalWeakOperatorErrorModel :
  WeakError.WeakOperatorErrorModel
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
canonicalWeakOperatorErrorModel =
  WeakError.toWeakOperatorErrorModel
    canonicalWeakOperatorErrorModelTarget

canonicalOperatorNormControlsWeakQuadraticForm : Set
canonicalOperatorNormControlsWeakQuadraticForm =
  WeakQuadratic.operatorNormControlsWeakQuadraticForm
    canonicalWeakQuadraticFormControlTarget

canonicalOperatorNormControlsWeakQuadraticFormProof :
  canonicalOperatorNormControlsWeakQuadraticForm
canonicalOperatorNormControlsWeakQuadraticFormProof =
  WeakQuadratic.WeakQuadraticFormControlTarget.pairIncidenceCNToWeakQuadraticCN
    canonicalWeakQuadraticFormControlTarget

canonicalOperatorWeakCN : Set
canonicalOperatorWeakCN =
  canonicalOperatorNormControlsWeakQuadraticForm

canonicalOperatorCNToStrongErrorN2 : Set
canonicalOperatorCNToStrongErrorN2 =
  QGap.operatorStrongErrorN2Target
    (ScaleHeadroom.CompatibilityScale.scaleSq canonicalCompatibilityScale)
    (λ x →
      ResidueNorm.strongNormSquared
        canonicalResidueNormModel
        compatibilityShellIndex
        x)
    canonicalActualWeakQuadraticForm
    canonicalWeakQuadraticFormConstant

canonicalOperatorCNWeakStrongComposeN2Raw :
  canonicalOperatorWeakCN →
  QGap.operatorStrongErrorN2Target
    compatibilityShellIndex
    (λ x →
      ResidueNorm.strongNormSquared
        canonicalResidueNormModel
        compatibilityShellIndex
        x)
    canonicalActualWeakQuadraticForm
    canonicalWeakQuadraticFormConstant
canonicalOperatorCNWeakStrongComposeN2Raw operatorWeakCNProof =
  QGap.operatorCNWeakStrongComposeN2
    compatibilityShellIndex
    (λ x →
      ResidueNorm.weakNormSquared
        canonicalResidueNormModel
        compatibilityShellIndex
        x)
    (λ x →
      ResidueNorm.strongNormSquared
        canonicalResidueNormModel
        compatibilityShellIndex
        x)
    canonicalActualWeakQuadraticForm
    canonicalWeakQuadraticFormConstant
    operatorWeakCNProof
    (λ x →
      ResidueNorm.strongDominatesWeakByN
        canonicalResidueNormModel
        compatibilityShellIndex
        x)

postulate
  canonicalOperatorCNToStrongErrorN2Proof :
    canonicalOperatorCNToStrongErrorN2

canonicalWeakStrongNormScalingTarget :
  QGap.WeakStrongNormScalingTarget
canonicalWeakStrongNormScalingTarget =
  QGap.mkWeakStrongNormScalingTarget
    canonicalResidueNormModel
    compatibilityShellIndex
    compatibilityCarrierElement
    canonicalOperatorWeakCN
    canonicalOperatorCNToStrongErrorN2
    true

canonicalWeakStrongNormScaling :
  QGap.WeakStrongNormScaling
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
canonicalWeakStrongNormScaling =
  QGap.toWeakStrongNormScaling canonicalWeakStrongNormScalingTarget

canonicalStrongNormSquared :
  ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex → Nat
canonicalStrongNormSquared =
  λ x →
    ResidueNorm.strongNormSquared
      canonicalResidueNormModel
      compatibilityShellIndex
      x

canonicalStrongNormSquaredAtUnitEnergy :
  canonicalStrongNormSquared
    (ResidueNorm.mkResidueEnergyCarrier (suc zero))
    ≡ suc zero
canonicalStrongNormSquaredAtUnitEnergy = refl

canonicalStage3UnitEnergySaturated : Bool
canonicalStage3UnitEnergySaturated = true

canonicalStage3UnitEnergySaturatedIsTrue :
  canonicalStage3UnitEnergySaturated ≡ true
canonicalStage3UnitEnergySaturatedIsTrue = refl

canonicalStage3ErrorSaturationSource : String
canonicalStage3ErrorSaturationSource =
  "C_err = 4 is forced upstream by the coarse unit-shell quadratic-form witness: qError = strongNormSquared = residueEnergy at unit energy."

canonicalExactKNAPositiveSubspaceCarrierTarget :
  ExactGramBridge.ExactKNAPositiveSubspaceCarrierTarget
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
canonicalExactKNAPositiveSubspaceCarrierTarget =
  ExactGramBridge.canonicalExactKNAPositiveSubspaceCarrierTarget

canonicalBaseQuadraticForm :
  ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex → Nat
canonicalBaseQuadraticForm =
  ExactQBase.exactKNAQBase

canonicalBaseQuadraticFormIsResidueEnergy :
  (x : ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex) →
  canonicalBaseQuadraticForm x ≡ ResidueNorm.residueEnergy x
canonicalBaseQuadraticFormIsResidueEnergy x = refl

canonicalStrongNormSquaredIsResidueEnergy :
  (x : ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex) →
  canonicalStrongNormSquared x ≡ ResidueNorm.residueEnergy x
canonicalStrongNormSquaredIsResidueEnergy x =
  *-identityˡ (ResidueNorm.residueEnergy x)

canonicalExactKNABaseQuadraticFormIdentificationTarget :
  ExactGramBridge.ExactKNABaseQuadraticFormIdentificationTarget
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
canonicalExactKNABaseQuadraticFormIdentificationTarget =
  ExactQBase.canonicalExactKNABaseQuadraticFormIdentificationTarget

------------------------------------------------------------------------
-- Blocker 2C: Rayleigh margin core uses an explicit compatibility scale.
--
--   compatibilityShellIndex = suc zero (= 1).
--   canonicalStrongNormSquared x = 1 * residueEnergy x  (nWeightedResidueNormModel)
--   canonicalBaseQuadraticForm  x = residueEnergy x     (exactKNAQBase)
--   canonicalWeakQuadraticFormConstant = 1              (stage3ErrorConstant)
--
-- The baseGapN2Target now requires:
--
--   baseGapConstant * strongNormSquared x
--     ≤ scaleSq * baseQuadraticForm x
--
-- Substituting shellIndex = 1, strongNorm = residueEnergy, qBase = residueEnergy:
--
--   baseGapConstant * residueEnergy x  ≤  residueEnergy x
--
-- To satisfy stage3ErrorBelowBaseGap we need baseGapConstant ≥ 2
-- (since stage3ErrorConstant = 1 < baseGapConstant).
-- But for any nonzero residueEnergy x, 2*E ≤ E is false.
--
-- The canonical compatibility scale is successor-scaled, so scaleSq = 4
-- while the operator witness remains typed at shellIndex = 1.
--
-- The ShellScaleHeadroom module (NSTriadKNShellScaleHeadroom) provides the
-- reusable abstraction: if scaleSq ≥ 2 then 2*E ≤ scaleSq*E.  At N=1, the
-- successor constructor headroomFromSucN gives scaleSq = 4:
--
--   canonicalShellScaleHeadroom =
--     ScaleHeadroom.headroomFromSucN 0 (s≤s (s≤s z≤n))  -- 2 ≤ 4
--   rayleighMarginFromScaleHeadroom canonicalShellScaleHeadroom x
--     : 2 * residueEnergy x ≤ 4 * residueEnergy x
--
-- The shared scale is consumed by the NegativeFrameRayleighMarginCore,
-- GapQuadraticFormsTarget, operatorErrorN2Target, and absorption target.
--
-- The scaled operator-error identification remains conditional: the existing
-- unit-shell weak/strong witness proves the raw-scale route, not the new
-- scaleSq route.  The q-gap and BKM gates therefore remain fail-closed.

canonicalNegativeFrameRayleighMarginCoreTarget : Setω
canonicalNegativeFrameRayleighMarginCoreTarget =
  MarginBridge.NegativeFrameRayleighMarginCore
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
    compatibilityShellIndex
    canonicalStrongNormSquared
    canonicalBaseQuadraticForm
    canonicalWeakQuadraticFormConstant

conditionalNegativeFrameRayleighMarginTarget :
  canonicalNegativeFrameRayleighMarginCoreTarget →
  MarginBridge.NegativeFrameRayleighMarginTarget
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
    compatibilityShellIndex
    canonicalStrongNormSquared
    canonicalBaseQuadraticForm
    canonicalWeakQuadraticFormConstant
conditionalNegativeFrameRayleighMarginTarget core =
  MarginBridge.toNegativeFrameRayleighMarginTarget
    core

canonicalExactKNAQuadraticCarrierTarget :
  ExactGramBridge.ExactKNAQuadraticCarrierTarget
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
canonicalExactKNAQuadraticCarrierTarget =
  ExactGramBridge.mkExactKNAQuadraticCarrierTarget
    canonicalExactKNAPositiveSubspaceCarrierTarget
    canonicalExactKNABaseQuadraticFormIdentificationTarget

canonicalExactKNAObjectDefinitionTarget :
  ExactGramBridge.ExactKNAObjectDefinitionTarget
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
canonicalExactKNAObjectDefinitionTarget =
  ExactGramBridge.toExactKNAObjectDefinitionTarget
    canonicalExactKNAQuadraticCarrierTarget

canonicalExactGramBaseFormIdentification :
  GramRayleighBridge.ExactGramBaseFormIdentification
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
canonicalExactGramBaseFormIdentification =
  ExactGramBridge.toExactGramBaseFormIdentification
    canonicalExactKNAObjectDefinitionTarget

conditionalRayleighCoercivityBeatsStage3Error :
  canonicalNegativeFrameRayleighMarginCoreTarget →
  GramRayleighBridge.RayleighCoercivityBeatsStage3Error
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
    compatibilityShellIndex
    canonicalStrongNormSquared
    (GramRayleighBridge.ExactGramBaseFormIdentification.baseQuadraticForm
      canonicalExactGramBaseFormIdentification)
    canonicalWeakQuadraticFormConstant
conditionalRayleighCoercivityBeatsStage3Error core =
  MarginBridge.toRayleighCoercivityBeatsStage3Error
    (conditionalNegativeFrameRayleighMarginTarget core)

conditionalGramRayleighBaseFormTarget :
  canonicalNegativeFrameRayleighMarginCoreTarget →
  GramRayleigh.GramRayleighBaseFormTarget
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
    compatibilityShellIndex
    canonicalStrongNormSquared
    canonicalWeakQuadraticFormConstant
conditionalGramRayleighBaseFormTarget core =
  GramRayleighBridge.toGramRayleighBaseFormTarget
    canonicalExactGramBaseFormIdentification
    (conditionalRayleighCoercivityBeatsStage3Error core)

canonicalGapQuadraticForms :
  QGap.GapQuadraticFormsTarget
canonicalGapQuadraticForms =
  QGap.mkGapQuadraticFormsTarget
    ResidueNorm.ResidueEnergyCarrier
    compatibilityShellIndex
    canonicalCompatibilityScale
    canonicalBaseQuadraticForm
    canonicalActualWeakQuadraticForm
    (λ x → canonicalBaseQuadraticForm x ∸ canonicalActualWeakQuadraticForm x)
    (λ _ → refl)

canonicalOperatorStrongError :
  ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex → Nat
canonicalOperatorStrongError =
  canonicalActualWeakQuadraticForm

postulate
  conditionalGramBaseFormCoercivityTarget :
    canonicalNegativeFrameRayleighMarginCoreTarget →
    GramBase.GramBaseFormCoercivityTarget
      canonicalGapQuadraticForms
      canonicalStrongNormSquared

postulate
  conditionalBaseGapTheorem :
    canonicalNegativeFrameRayleighMarginCoreTarget →
    QGap.BaseGapN2Theorem
      canonicalGapQuadraticForms
      canonicalStrongNormSquared

canonicalErrorDominatedByStage3 :
  QGap.operatorErrorIdentifiedWithOperatorStrongErrorTarget
    canonicalGapQuadraticForms
    canonicalOperatorStrongError
canonicalErrorDominatedByStage3 _ = ≤-refl

canonicalOperatorErrorIdentification :
  QGap.OperatorErrorIdentification
    canonicalGapQuadraticForms
    canonicalOperatorStrongError
    canonicalStrongNormSquared
canonicalOperatorErrorIdentification =
  QGap.operatorErrorIdentificationFromStrongOperatorError
    canonicalWeakQuadraticFormConstant
    canonicalOperatorCNToStrongErrorN2Proof
    canonicalErrorDominatedByStage3

postulate
  canonicalOperatorErrorConstantMatchesStage3 :
    QGap.OperatorErrorIdentification.errorConstant
      canonicalOperatorErrorIdentification
    ≡
    canonicalWeakQuadraticFormConstant

postulate
  conditionalStage3ErrorBelowBaseGap :
    (core : canonicalNegativeFrameRayleighMarginCoreTarget) →
    QGap.OperatorErrorIdentification.errorConstant
      canonicalOperatorErrorIdentification
      <
    QGap.BaseGapN2Theorem.baseGapConstant (conditionalBaseGapTheorem core)

postulate
  conditionalGapMarginPositive :
    (core : canonicalNegativeFrameRayleighMarginCoreTarget) →
    zero <
    (QGap.BaseGapN2Theorem.baseGapConstant (conditionalBaseGapTheorem core)
      ∸ QGap.OperatorErrorIdentification.errorConstant
        canonicalOperatorErrorIdentification)

conditionalGapMargin :
  canonicalNegativeFrameRayleighMarginCoreTarget →
  QGap.GapMargin
conditionalGapMargin core =
  QGap.gapMarginFromTheoremsAndLeq
    (conditionalBaseGapTheorem core)
    canonicalOperatorErrorIdentification
    (conditionalGapMarginPositive core)
    (<⇒≤ (conditionalStage3ErrorBelowBaseGap core))

conditionalGapPerturbationAbsorption :
  canonicalNegativeFrameRayleighMarginCoreTarget →
  Set
conditionalGapPerturbationAbsorption core =
  QGap.gapPerturbationAbsorptionTarget
    canonicalGapQuadraticForms
    canonicalStrongNormSquared
    (conditionalBaseGapTheorem core)
    canonicalOperatorStrongError
    canonicalOperatorErrorIdentification

conditionalGapPerturbationAbsorptionProof :
  (core : canonicalNegativeFrameRayleighMarginCoreTarget) →
  conditionalGapPerturbationAbsorption core
conditionalGapPerturbationAbsorptionProof core =
  QGap.gapAbsorptionFromMargin
    (conditionalBaseGapTheorem core)
    canonicalOperatorErrorIdentification
    (conditionalGapMargin core)

conditionalBaseGapMinusErrorAbsorptionTarget :
  canonicalNegativeFrameRayleighMarginCoreTarget →
  QGap.BaseGapMinusErrorAbsorptionTarget
conditionalBaseGapMinusErrorAbsorptionTarget core =
  QGap.mkBaseGapMinusErrorAbsorptionTarget
    canonicalGapQuadraticForms
    canonicalStrongNormSquared
    canonicalOperatorStrongError
    (conditionalBaseGapTheorem core)
    canonicalOperatorErrorIdentification
    (conditionalGapMargin core)
    (conditionalGapPerturbationAbsorption core)
    false

conditionalBaseGapMinusErrorAbsorption :
  canonicalNegativeFrameRayleighMarginCoreTarget →
  QGap.BaseGapMinusErrorAbsorption
conditionalBaseGapMinusErrorAbsorption core =
  QGap.toBaseGapMinusErrorAbsorption
    (conditionalBaseGapMinusErrorAbsorptionTarget core)

conditionalQGapTransferWitness :
  canonicalNegativeFrameRayleighMarginCoreTarget → Set
conditionalQGapTransferWitness core =
  canonicalOperatorCNToStrongErrorN2 × conditionalGapPerturbationAbsorption core

conditionalCompatibility :
  canonicalNegativeFrameRayleighMarginCoreTarget →
  QGap.ResidueScaleCompatibility
conditionalCompatibility core =
  QGap.mkResidueScaleCompatibility
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
    canonicalCompatibilityScale
    canonicalWeakStrongNormScaling
    (conditionalBaseGapMinusErrorAbsorption core)
    (conditionalQGapTransferWitness core)
    false

canonicalQGapTransferClosed : Bool
canonicalQGapTransferClosed = false

canonicalSchurResidueScaleClosed : Bool
canonicalSchurResidueScaleClosed = false

canonicalIntegratedResidueN2BoundClosed : Bool
canonicalIntegratedResidueN2BoundClosed =
  BKMBridge.integratedResidueN2BoundClosed
    canonicalResidueNormModel
    compatibilityShellIndex
    (BKMBridge.canonicalIntegratedResidueN2BoundTarget
      canonicalResidueNormModel
      compatibilityShellIndex)

canonicalIntegratedDangerFromSchurResidueClosed : Bool
canonicalIntegratedDangerFromSchurResidueClosed =
  BKMBridge.integratedDangerFromSchurResidueClosed
    canonicalResidueNormModel
    (BKMBridge.canonicalIntegratedDangerFromSchurResidueTarget
      canonicalResidueNormModel)

canonicalResidenceTimeExclusionClosed : Bool
canonicalResidenceTimeExclusionClosed =
  BKMBridge.residenceTimeExclusionClosed
    canonicalResidueNormModel
    compatibilityShellIndex
    (BKMBridge.canonicalResidenceTimeExclusionTarget
      canonicalResidueNormModel
      compatibilityShellIndex)

canonicalBKMProjectionSmallnessClosed : Bool
canonicalBKMProjectionSmallnessClosed =
  BKMBridge.bkmProjectionSmallnessClosed
    canonicalResidueNormModel
    compatibilityShellIndex
    (BKMBridge.canonicalBKMProjectionSmallnessTarget
      canonicalResidueNormModel
      compatibilityShellIndex)

canonicalBKMExclusionProved : Bool
canonicalBKMExclusionProved = false

canonicalNSTriadKNPairIncidenceProfileBounds :
  NSTriadKNPairIncidenceProfileBounds
canonicalNSTriadKNPairIncidenceProfileBounds =
  mkNSTriadKNPairIncidenceProfileBounds
    "NSTriadKNPairIncidenceProfileBounds"
    refl
    canonicalReceiptText
    refl
    "NSTriadKNPairIncidenceProfileDecompositionReceipt"
    refl
    Profiles.canonicalReadoutText
    refl
    ForcedTail.canonicalReadoutText
    refl
    canonicalKernelObject
    refl
    canonicalWeightTarget
    refl
    canonicalRowFunctional
    refl
    canonicalColumnFunctional
    refl
    canonicalForcedTailTarget
    refl
    canonicalAdversarialTarget
    refl
    canonicalTransitionTarget
    refl
    canonicalResidualTarget
    refl
    canonicalCombinationTarget
    refl
    canonicalForcedTailRouteNote
    refl
    canonicalReadoutText
    refl
    true
    refl
    true
    refl
    true
    refl
    ForcedTailClosure.forcedTailWeightedProductBoundClosed
    ForcedTailClosure.forcedTailWeightedProductBoundClosedIsTrue
    AdversarialClosure.adversarialWeightedProductBoundClosed
    refl
    TransitionClosure.transitionWeightedProductBoundClosed
    TransitionClosure.transitionWeightedProductBoundClosedIsTrue
    ResidualClosure.residualWeightedProductBoundClosed
    ResidualClosure.residualWeightedProductBoundClosedIsTrue
    true
    refl
    CrossMatrix.profileCrossProductMatrixClosed
    CrossMatrix.profileCrossProductMatrixClosedIsTrue
    WeightedSchur.weightedSchurProductBoundClosed
    WeightedSchur.weightedSchurProductBoundClosedIsTrue
    CNTheorem.pairIncidenceCNTheoremClosed
    CNTheorem.pairIncidenceCNTheoremClosedIsTrue
    canonicalQGapTransferClosed
    refl
    canonicalSchurResidueScaleClosed
    refl
    canonicalIntegratedResidueN2BoundClosed
    refl
    canonicalIntegratedDangerFromSchurResidueClosed
    refl
    canonicalResidenceTimeExclusionClosed
    refl
    canonicalBKMProjectionSmallnessClosed
    refl
    false
    refl
    false
    refl
    canonicalBKMExclusionProved
    refl
    false
    refl
