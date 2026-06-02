module DASHI.Physics.Closure.EV5ThetaMarginUpgradeReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; _<_; _*_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)

import DASHI.Combinatorics.FractranCOL as FractranCOL
import DASHI.Physics.Closure.EV5VectorAdmissibleStateReceipt as Vector
import DASHI.Physics.Closure.NSToEV5ProjectionFrontierReceipt as Frontier

------------------------------------------------------------------------
-- EV5 theta-margin diagnostic receipt.
--
-- This receipt refines the previous EV5 lane7/lane2 carrier surface with a
-- computable theta seam gauge/profile:
--
--   * lane7 is non-increasing;
--   * lane2 is bounded by K*(nu);
--   * thetaTailMargin is computable diagnostic evidence and may be checked
--     against < 1 at a selected seam.
--
-- The receipt deliberately keeps v3 diagnostic-only, keeps theta as a
-- non-monotone seam/profile diagnostic rather than an admissibility theorem,
-- and performs no Navier-Stokes, BKM, continuation, or Clay promotion.

one : Nat
one =
  suc zero

thetaTailMargin :
  FractranCOL.EV5 →
  Nat
thetaTailMargin ev =
  Vector.lane7 ev

data EV5ThetaMarginUpgradeStatus : Set where
  thetaMarginUpgraded_vectorCarrierOnly_noNSPromotion :
    EV5ThetaMarginUpgradeStatus

data ThetaMarginUpgradeComponent : Set where
  vectorAdmissibleStateReceiptComponent :
    ThetaMarginUpgradeComponent

  projectionFrontierReceiptComponent :
    ThetaMarginUpgradeComponent

  lane7NonIncreasingComponent :
    ThetaMarginUpgradeComponent

  lane2BoundedByKStarNuComponent :
    ThetaMarginUpgradeComponent

  thetaTailMarginBelowOneComponent :
    ThetaMarginUpgradeComponent

  v3DiagnosticOnlyComponent :
    ThetaMarginUpgradeComponent

  thetaDiagnosticEvidenceNotTheoremComponent :
    ThetaMarginUpgradeComponent

  noNSOrClayPromotionComponent :
    ThetaMarginUpgradeComponent

  thetaProfileComputableComponent :
    ThetaMarginUpgradeComponent

  thetaDangerShellArgmaxComponent :
    ThetaMarginUpgradeComponent

  thetaHighShellDecayOpenConditionalComponent :
    ThetaMarginUpgradeComponent

  thetaBKMEquivalenceNotProvedComponent :
    ThetaMarginUpgradeComponent

canonicalThetaMarginUpgradeComponents :
  List ThetaMarginUpgradeComponent
canonicalThetaMarginUpgradeComponents =
  vectorAdmissibleStateReceiptComponent
  ∷ projectionFrontierReceiptComponent
  ∷ lane7NonIncreasingComponent
  ∷ lane2BoundedByKStarNuComponent
  ∷ thetaTailMarginBelowOneComponent
  ∷ v3DiagnosticOnlyComponent
  ∷ thetaDiagnosticEvidenceNotTheoremComponent
  ∷ noNSOrClayPromotionComponent
  ∷ thetaProfileComputableComponent
  ∷ thetaDangerShellArgmaxComponent
  ∷ thetaHighShellDecayOpenConditionalComponent
  ∷ thetaBKMEquivalenceNotProvedComponent
  ∷ []

data ThetaProfileScope : Set where
  thetaProfileComputable :
    ThetaProfileScope

  thetaDangerShellCriticalArgmaxOverKStar :
    ThetaProfileScope

  thetaHighShellDecayOpenConditional :
    ThetaProfileScope

  thetaLessThanOneTailAbsorptionConditional :
    ThetaProfileScope

  thetaLessThanOneContinuationConditional :
    ThetaProfileScope

  thetaBKMEquivalenceNotProved :
    ThetaProfileScope

canonicalThetaProfileScope :
  List ThetaProfileScope
canonicalThetaProfileScope =
  thetaProfileComputable
  ∷ thetaDangerShellCriticalArgmaxOverKStar
  ∷ thetaHighShellDecayOpenConditional
  ∷ thetaLessThanOneTailAbsorptionConditional
  ∷ thetaLessThanOneContinuationConditional
  ∷ thetaBKMEquivalenceNotProved
  ∷ []

data ThetaTheoremPromotion : Set where

thetaTheoremPromotionImpossibleHere :
  ThetaTheoremPromotion →
  ⊥
thetaTheoremPromotionImpossibleHere ()

record ThetaTailMarginEvidence
    (state : FractranCOL.EV5) : Set where
  field
    computedMargin :
      Nat

    computedMarginIsThetaTailMargin :
      computedMargin ≡ thetaTailMargin state

    thetaMarginBelowOne :
      thetaTailMargin state < one

    computableDiagnostic :
      Bool

    computableDiagnosticIsTrue :
      computableDiagnostic ≡ true

    promotedToTheorem :
      Bool

    promotedToTheoremIsFalse :
      promotedToTheorem ≡ false

open ThetaTailMarginEvidence public

canonicalZeroThetaTailMarginEvidence :
  ThetaTailMarginEvidence Vector.zeroEV5
canonicalZeroThetaTailMarginEvidence =
  record
    { computedMargin =
        zero
    ; computedMarginIsThetaTailMargin =
        refl
    ; thetaMarginBelowOne =
        s≤s z≤n
    ; computableDiagnostic =
        true
    ; computableDiagnosticIsTrue =
        refl
    ; promotedToTheorem =
        false
    ; promotedToTheoremIsFalse =
        refl
    }

thetaMarginUpgradeBoundaryStatement :
  String
thetaMarginUpgradeBoundaryStatement =
  "EV5 theta is a computable seam gauge/profile layered over lane7 non-increasing and lane2 bounded by K*(nu); it is not an admissibility triple theorem."

v3DiagnosticBoundaryStatement :
  String
v3DiagnosticBoundaryStatement =
  "v3 remains diagnostic-only: it is non-monotone by construction, excluded from termination/Lyapunov energy, and not promoted to an NS proof."

thetaEvidenceBoundaryStatement :
  String
thetaEvidenceBoundaryStatement =
  "thetaTailMargin is computable EV5 seam/profile diagnostic evidence; theta is not monotone and this receipt does not turn theta into an NS theorem."

thetaProfileBoundaryStatement :
  String
thetaProfileBoundaryStatement =
  "thetaProfileComputable records a profile; the danger shell is the critical-shell argmax over k>=K*, high-shell decay remains open/conditional, theta<1 only conditionally supports tail absorption and continuation, and theta<=>BKM is not proved."

noPromotionBoundaryStatement :
  String
noPromotionBoundaryStatement =
  "No NS regularity theorem and no Clay Navier-Stokes promotion are issued by this EV5 theta-margin receipt."

record EV5ThetaMarginUpgradeReceipt
    (nu K : Nat)
    (before after : FractranCOL.EV5) : Set₁ where
  field
    status :
      EV5ThetaMarginUpgradeStatus

    statusIsCarrierOnlyNoPromotion :
      status
      ≡
      thetaMarginUpgraded_vectorCarrierOnly_noNSPromotion

    vectorReceipt :
      Vector.EV5VectorAdmissibleStateReceipt nu K before after

    vectorReceiptCarriesLane7 :
      Vector.lane7DissipationNonIncreasing vectorReceipt
      ≡
      Vector.Lane7DissipationWitness.lane7NonIncreasing
        (Vector.lane7Dissipation vectorReceipt)

    vectorReceiptCarriesLane2 :
      Vector.lane2BoundedByKStarNu vectorReceipt
      ≡
      Vector.CascadeTerminationWitness.lane2BoundedByKStarNu
        (Vector.cascadeTermination vectorReceipt)

    projectionFrontier :
      Frontier.NSToEV5ProjectionFrontierReceipt

    projectionFrontierIsCanonical :
      projectionFrontier ≡ Frontier.canonicalNSToEV5ProjectionFrontierReceipt

    lane7NonIncreasing :
      Vector.lane7 after ≤ Vector.lane7 before

    lane7NonIncreasingMatchesVectorReceipt :
      lane7NonIncreasing
      ≡
      Vector.lane7DissipationNonIncreasing vectorReceipt

    lane2BoundedByKStarNu :
      Vector.lane2 after ≤ Vector.kStarNu vectorReceipt

    lane2BoundedByKStarNuMatchesVectorReceipt :
      lane2BoundedByKStarNu
      ≡
      Vector.lane2BoundedByKStarNu vectorReceipt

    thetaEvidence :
      ThetaTailMarginEvidence after

    thetaTailMarginBelowOne :
      thetaTailMargin after < one

    thetaTailMarginBelowOneMatchesEvidence :
      thetaTailMarginBelowOne
      ≡
      ThetaTailMarginEvidence.thetaMarginBelowOne thetaEvidence
  field
    thetaComputableDiagnostic :
      Bool

    thetaComputableDiagnosticIsTrue :
      thetaComputableDiagnostic ≡ true

    thetaProfileComputableFlag :
      Bool

    thetaProfileComputableFlagIsTrue :
      thetaProfileComputableFlag ≡ true

    thetaDangerShell :
      Nat

    thetaDangerShellIsCriticalArgmaxOverKStar :
      Bool

    thetaDangerShellIsCriticalArgmaxOverKStarIsTrue :
      thetaDangerShellIsCriticalArgmaxOverKStar ≡ true

    thetaHighShellDecayOpenConditionalFlag :
      Bool

    thetaHighShellDecayOpenConditionalFlagIsTrue :
      thetaHighShellDecayOpenConditionalFlag ≡ true

    thetaMonotoneClaimed :
      Bool

    thetaMonotoneClaimedIsFalse :
      thetaMonotoneClaimed ≡ false

    thetaPromotedToTheorem :
      Bool

    thetaPromotedToTheoremIsFalse :
      thetaPromotedToTheorem ≡ false

    v3DiagnosticOnly :
      Bool

    v3DiagnosticOnlyIsTrue :
      v3DiagnosticOnly ≡ true

    v3ExcludedFromTerminationEnergy :
      Bool

    v3ExcludedFromTerminationEnergyIsTrue :
      v3ExcludedFromTerminationEnergy ≡ true

    v3PromotedToNSRegularityProof :
      Bool

    v3PromotedToNSRegularityProofIsFalse :
      v3PromotedToNSRegularityProof ≡ false

    nsRegularityPromoted :
      Bool

    nsRegularityPromotedIsFalse :
      nsRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    thetaLessThanOneTailAbsorptionConditionalFlag :
      Bool

    thetaLessThanOneTailAbsorptionConditionalFlagIsTrue :
      thetaLessThanOneTailAbsorptionConditionalFlag ≡ true

    thetaLessThanOneContinuationConditionalFlag :
      Bool

    thetaLessThanOneContinuationConditionalFlagIsTrue :
      thetaLessThanOneContinuationConditionalFlag ≡ true

    thetaBKMEquivalenceProved :
      Bool

    thetaBKMEquivalenceProvedIsFalse :
      thetaBKMEquivalenceProved ≡ false

    upgradedAdmissibilityTriple :
      Vector.lane7 after ≤ Vector.lane7 before
      ×
      Vector.lane2 after ≤ Vector.kStarNu vectorReceipt
      ×
      thetaTailMargin after < one

    upgradedAdmissibilityTriplePromotedToTheorem :
      Bool

    upgradedAdmissibilityTriplePromotedToTheoremIsFalse :
      upgradedAdmissibilityTriplePromotedToTheorem ≡ false

    thetaProfileScope :
      List ThetaProfileScope

    thetaProfileScopeIsCanonical :
      thetaProfileScope ≡ canonicalThetaProfileScope

    components :
      List ThetaMarginUpgradeComponent

    componentsAreCanonical :
      components ≡ canonicalThetaMarginUpgradeComponents

    thetaMarginUpgradeBoundary :
      String

    thetaMarginUpgradeBoundaryIsCanonical :
      thetaMarginUpgradeBoundary ≡ thetaMarginUpgradeBoundaryStatement

    v3DiagnosticBoundary :
      String

    v3DiagnosticBoundaryIsCanonical :
      v3DiagnosticBoundary ≡ v3DiagnosticBoundaryStatement

    thetaEvidenceBoundary :
      String

    thetaEvidenceBoundaryIsCanonical :
      thetaEvidenceBoundary ≡ thetaEvidenceBoundaryStatement

    thetaProfileBoundary :
      String

    thetaProfileBoundaryIsCanonical :
      thetaProfileBoundary ≡ thetaProfileBoundaryStatement

    noPromotionBoundary :
      String

    noPromotionBoundaryIsCanonical :
      noPromotionBoundary ≡ noPromotionBoundaryStatement

    thetaTheoremPromotionFlags :
      List ThetaTheoremPromotion

    thetaTheoremPromotionFlagsAreEmpty :
      thetaTheoremPromotionFlags ≡ []

open EV5ThetaMarginUpgradeReceipt public

canonicalZeroEV5ThetaMarginUpgradeReceipt :
  ∀ (nu K : Nat) →
  EV5ThetaMarginUpgradeReceipt nu K Vector.zeroEV5 Vector.zeroEV5
canonicalZeroEV5ThetaMarginUpgradeReceipt nu K =
  record
    { status =
        thetaMarginUpgraded_vectorCarrierOnly_noNSPromotion
    ; statusIsCarrierOnlyNoPromotion =
        refl
    ; vectorReceipt =
        Vector.canonicalZeroEV5VectorAdmissibleStateReceipt nu K
    ; vectorReceiptCarriesLane7 =
        refl
    ; vectorReceiptCarriesLane2 =
        refl
    ; projectionFrontier =
        Frontier.canonicalNSToEV5ProjectionFrontierReceipt
    ; projectionFrontierIsCanonical =
        refl
    ; lane7NonIncreasing =
        z≤n
    ; lane7NonIncreasingMatchesVectorReceipt =
        refl
    ; lane2BoundedByKStarNu =
        z≤n
    ; lane2BoundedByKStarNuMatchesVectorReceipt =
        refl
    ; thetaEvidence =
        canonicalZeroThetaTailMarginEvidence
    ; thetaTailMarginBelowOne =
        s≤s z≤n
    ; thetaTailMarginBelowOneMatchesEvidence =
        refl
    ; thetaComputableDiagnostic =
        true
    ; thetaComputableDiagnosticIsTrue =
        refl
    ; thetaProfileComputableFlag =
        true
    ; thetaProfileComputableFlagIsTrue =
        refl
    ; thetaDangerShell =
        K
    ; thetaDangerShellIsCriticalArgmaxOverKStar =
        true
    ; thetaDangerShellIsCriticalArgmaxOverKStarIsTrue =
        refl
    ; thetaHighShellDecayOpenConditionalFlag =
        true
    ; thetaHighShellDecayOpenConditionalFlagIsTrue =
        refl
    ; thetaMonotoneClaimed =
        false
    ; thetaMonotoneClaimedIsFalse =
        refl
    ; thetaPromotedToTheorem =
        false
    ; thetaPromotedToTheoremIsFalse =
        refl
    ; v3DiagnosticOnly =
        true
    ; v3DiagnosticOnlyIsTrue =
        refl
    ; v3ExcludedFromTerminationEnergy =
        true
    ; v3ExcludedFromTerminationEnergyIsTrue =
        refl
    ; v3PromotedToNSRegularityProof =
        false
    ; v3PromotedToNSRegularityProofIsFalse =
        refl
    ; nsRegularityPromoted =
        false
    ; nsRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; thetaLessThanOneTailAbsorptionConditionalFlag =
        true
    ; thetaLessThanOneTailAbsorptionConditionalFlagIsTrue =
        refl
    ; thetaLessThanOneContinuationConditionalFlag =
        true
    ; thetaLessThanOneContinuationConditionalFlagIsTrue =
        refl
    ; thetaBKMEquivalenceProved =
        false
    ; thetaBKMEquivalenceProvedIsFalse =
        refl
    ; upgradedAdmissibilityTriple =
        z≤n , z≤n , s≤s z≤n
    ; upgradedAdmissibilityTriplePromotedToTheorem =
        false
    ; upgradedAdmissibilityTriplePromotedToTheoremIsFalse =
        refl
    ; thetaProfileScope =
        canonicalThetaProfileScope
    ; thetaProfileScopeIsCanonical =
        refl
    ; components =
        canonicalThetaMarginUpgradeComponents
    ; componentsAreCanonical =
        refl
    ; thetaMarginUpgradeBoundary =
        thetaMarginUpgradeBoundaryStatement
    ; thetaMarginUpgradeBoundaryIsCanonical =
        refl
    ; v3DiagnosticBoundary =
        v3DiagnosticBoundaryStatement
    ; v3DiagnosticBoundaryIsCanonical =
        refl
    ; thetaEvidenceBoundary =
        thetaEvidenceBoundaryStatement
    ; thetaEvidenceBoundaryIsCanonical =
        refl
    ; thetaProfileBoundary =
        thetaProfileBoundaryStatement
    ; thetaProfileBoundaryIsCanonical =
        refl
    ; noPromotionBoundary =
        noPromotionBoundaryStatement
    ; noPromotionBoundaryIsCanonical =
        refl
    ; thetaTheoremPromotionFlags =
        []
    ; thetaTheoremPromotionFlagsAreEmpty =
        refl
    }

canonicalThetaTailMarginBelowOne :
  ∀ (nu K : Nat) →
  thetaTailMarginBelowOne
    (canonicalZeroEV5ThetaMarginUpgradeReceipt nu K)
  ≡
  s≤s z≤n
canonicalThetaTailMarginBelowOne nu K =
  refl

canonicalThetaRemainsDiagnosticEvidence :
  ∀ (nu K : Nat) →
  thetaComputableDiagnostic
    (canonicalZeroEV5ThetaMarginUpgradeReceipt nu K)
  ≡
  true
canonicalThetaRemainsDiagnosticEvidence nu K =
  refl

canonicalThetaNotPromotedToTheorem :
  ∀ (nu K : Nat) →
  thetaPromotedToTheorem
    (canonicalZeroEV5ThetaMarginUpgradeReceipt nu K)
  ≡
  false
canonicalThetaNotPromotedToTheorem nu K =
  refl

canonicalV3RemainsDiagnosticOnly :
  ∀ (nu K : Nat) →
  v3DiagnosticOnly
    (canonicalZeroEV5ThetaMarginUpgradeReceipt nu K)
  ≡
  true
canonicalV3RemainsDiagnosticOnly nu K =
  refl

canonicalNoNSPromotion :
  ∀ (nu K : Nat) →
  nsRegularityPromoted
    (canonicalZeroEV5ThetaMarginUpgradeReceipt nu K)
  ≡
  false
canonicalNoNSPromotion nu K =
  refl

canonicalNoClayPromotion :
  ∀ (nu K : Nat) →
  clayNavierStokesPromoted
    (canonicalZeroEV5ThetaMarginUpgradeReceipt nu K)
  ≡
  false
canonicalNoClayPromotion nu K =
  refl
