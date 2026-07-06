module DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileBounds where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecompositionReceipt as Profiles
import DASHI.Physics.Closure.NSTriadKNForcedTailClosureDependency as ForcedTailClosure
import DASHI.Physics.Closure.NSTriadKNForcedTailWeightedProductBoundReceipt as ForcedTail
import DASHI.Physics.Closure.NSTriadKNAdversarialClosureDependency as AdversarialClosure
import DASHI.Physics.Closure.NSTriadKNTransitionClosureDependency as TransitionClosure
import DASHI.Physics.Closure.NSTriadKNResidualClosureDependency as ResidualClosure
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix as CrossMatrix
import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound as WeightedSchur
import DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem as CNTheorem
import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
import DASHI.Physics.Closure.NSTriadKNBKMResidenceBridge as BKMBridge
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm




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
  "Profile-bounds status: the structural four-profile decomposition, the full 16-entry profile cross-product matrix, the global weighted Schur product theorem, and the PairIncidence C/N operator route are now closed on the active chain. The next honest theorem is no longer a profile-product estimate. It is the Blocker 2 residue/gap scaling bridge: construct ResidueScaleCompatibility so the operator C/N theorem yields q_gap(N) >= c / N^2 through an explicit weak/strong norm scaling and base-gap-minus-error absorption argument. The forced-tail sampled witness remains historical evidence only; theorem authority for the active chain now comes from the depth-bearing profile route plus the still-open residue/gap compatibility layer."

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

postulate
  canonicalWeakError :
    ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex → Nat
  canonicalWeakErrorConstant : Nat
  canonicalBaseGapN2 : Set
  canonicalOperatorErrorN2 : Set
  canonicalGapMarginPositive : Set
  canonicalGapPerturbationAbsorption : Set
  canonicalQGapTransferWitness : Set

compatibilityCarrierElement :
  ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex
compatibilityCarrierElement =
  ResidueNorm.mkResidueEnergyCarrier 0

canonicalResidueNormModel :
  ResidueNorm.ResidueNormModel
canonicalResidueNormModel =
  ResidueNorm.nWeightedResidueNormModel

canonicalOperatorWeakCN : Set
canonicalOperatorWeakCN =
  (x : ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex) →
  compatibilityShellIndex * canonicalWeakError x
    ≤
    canonicalWeakErrorConstant *
      ResidueNorm.weakNormSquared
        canonicalResidueNormModel
        compatibilityShellIndex
        x

canonicalOperatorCNToStrongErrorN2 : Set
canonicalOperatorCNToStrongErrorN2 =
  QGap.operatorStrongErrorN2Target
    compatibilityShellIndex
    (λ x →
      ResidueNorm.strongNormSquared
        canonicalResidueNormModel
        compatibilityShellIndex
        x)
    canonicalWeakError
    canonicalWeakErrorConstant

canonicalOperatorCNWeakStrongComposeN2 :
  canonicalOperatorWeakCN →
  canonicalOperatorCNToStrongErrorN2
canonicalOperatorCNWeakStrongComposeN2 operatorWeakCNProof =
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
    canonicalWeakError
    canonicalWeakErrorConstant
    operatorWeakCNProof
    (λ x →
      ResidueNorm.strongDominatesWeakByN
        canonicalResidueNormModel
        compatibilityShellIndex
        x)

canonicalWeakStrongNormScalingTarget :
  QGap.WeakStrongNormScalingTarget
canonicalWeakStrongNormScalingTarget =
  QGap.mkWeakStrongNormScalingTarget
    canonicalResidueNormModel
    compatibilityShellIndex
    compatibilityCarrierElement
    canonicalOperatorWeakCN
    canonicalOperatorCNToStrongErrorN2
    false

canonicalWeakStrongNormScaling :
  QGap.WeakStrongNormScaling
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
canonicalWeakStrongNormScaling =
  QGap.toWeakStrongNormScaling canonicalWeakStrongNormScalingTarget

canonicalBaseGapMinusErrorAbsorptionTarget :
  QGap.BaseGapMinusErrorAbsorptionTarget
canonicalBaseGapMinusErrorAbsorptionTarget =
  QGap.mkBaseGapMinusErrorAbsorptionTarget
    canonicalBaseGapN2
    canonicalOperatorErrorN2
    canonicalGapMarginPositive
    canonicalGapPerturbationAbsorption
    false

canonicalBaseGapMinusErrorAbsorption :
  QGap.BaseGapMinusErrorAbsorption
canonicalBaseGapMinusErrorAbsorption =
  QGap.toBaseGapMinusErrorAbsorption
    canonicalBaseGapMinusErrorAbsorptionTarget

canonicalCompatibility : QGap.ResidueScaleCompatibility
canonicalCompatibility =
  QGap.mkResidueScaleCompatibility
    (ResidueNorm.ResidueEnergyCarrier compatibilityShellIndex)
    canonicalWeakStrongNormScaling
    canonicalBaseGapMinusErrorAbsorption
    canonicalQGapTransferWitness
    false

canonicalQGapTransferClosed : Bool
canonicalQGapTransferClosed =
  QGap.qGapTransferClosed canonicalCompatibility

canonicalBKMExclusionProved : Bool
canonicalBKMExclusionProved =
  BKMBridge.bkmExclusionProved canonicalCompatibility

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
    false
    refl
    false
    refl
    canonicalBKMExclusionProved
    refl
    false
    refl
