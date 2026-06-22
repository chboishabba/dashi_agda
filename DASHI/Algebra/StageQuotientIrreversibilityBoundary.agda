module DASHI.Algebra.StageQuotientIrreversibilityBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; z≤n)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.Product using (_,_)

open import Base369 using
  ( TriTruth
  ; tri-low ; tri-mid ; tri-high
  ; triXor
  )
open import LogicTlurey using
  ( Stage
  ; seed ; overflow
  ; stageTone
  )

import DASHI.Algebra.StageQuotient as SQ
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.ShiftDiscreteContinuityCurrent as SDCC
import DASHI.Physics.DashiDynamicsShiftInstance as DDSI

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- Boundary statement.
--
-- The irreversible seam recorded here is the non-injective quotient
-- Stage -> TriTruth.  It is not a failure of the TriTruth/GF(3)-style
-- additive inverse operation, and it is not promoted to a thermodynamic or
-- physical Carnot theorem.

data IrreversibilityCause : Set where
  geometricCompression : IrreversibilityCause
  nonInjectiveQuotient : IrreversibilityCause

data StageQuotientBoundaryFlag : Set where
  geometricCompressionOnly : StageQuotientBoundaryFlag
  quotientNonInjective : StageQuotientBoundaryFlag
  gf3AdditiveInversesPresent : StageQuotientBoundaryFlag
  notAbsenceOfGF3AdditiveInverse : StageQuotientBoundaryFlag
  impossibleSectionGapRecorded : StageQuotientBoundaryFlag
  impossibleOrderPreservingReversalGapRecorded : StageQuotientBoundaryFlag
  shiftConvergesToHeldWithin2Consumed : StageQuotientBoundaryFlag
  finiteContinuityCurrentInspectedOnly : StageQuotientBoundaryFlag
  noThermodynamicCarnotTheoremPromotion : StageQuotientBoundaryFlag
  noPhysicalCarnotTheoremPromotion : StageQuotientBoundaryFlag

gf3Neg : TriTruth → TriTruth
gf3Neg tri-low = tri-low
gf3Neg tri-mid = tri-high
gf3Neg tri-high = tri-mid

gf3AdditiveInverseLaw :
  ∀ t →
  triXor t (gf3Neg t) ≡ tri-low
gf3AdditiveInverseLaw tri-low = refl
gf3AdditiveInverseLaw tri-mid = refl
gf3AdditiveInverseLaw tri-high = refl

record GF3AdditiveInverseSurface : Set where
  constructor gf3AdditiveInverseSurface
  field
    neg : TriTruth → TriTruth
    inverseLaw :
      ∀ t →
      triXor t (neg t) ≡ tri-low

canonicalGF3AdditiveInverseSurface : GF3AdditiveInverseSurface
canonicalGF3AdditiveInverseSurface =
  gf3AdditiveInverseSurface
    gf3Neg
    gf3AdditiveInverseLaw

seed≢overflow : seed ≢ overflow
seed≢overflow ()

seedOverflowQuotientCollapse :
  SQ.q seed ≡ SQ.q overflow
seedOverflowQuotientCollapse = refl

stageQuotientInspectsLogicTlureyTone :
  ∀ s →
  SQ.q s ≡ stageTone s
stageQuotientInspectsLogicTlureyTone s = refl

StageQuotientLeftInverseSection : Set
StageQuotientLeftInverseSection =
  (section : TriTruth → Stage) →
  ((s : Stage) → section (SQ.q s) ≡ s) →
  ⊥

StageToneLeftInverseSection : Set
StageToneLeftInverseSection =
  (section : TriTruth → Stage) →
  ((s : Stage) → section (stageTone s) ≡ s) →
  ⊥

noStageQuotientLeftInverseSection :
  StageQuotientLeftInverseSection
noStageQuotientLeftInverseSection section leftInverse =
  seed≢overflow
    (trans
      (sym (leftInverse seed))
      (leftInverse overflow))

noStageToneLeftInverseSection :
  StageToneLeftInverseSection
noStageToneLeftInverseSection section leftInverse =
  seed≢overflow
    (trans
      (sym (leftInverse seed))
      (leftInverse overflow))

shiftWithin2StartNormalizes :
  DDSI.shiftConvergesToHeldWithin2 SPTI.shiftStartPoint
    ≡
  (suc (suc zero) , (NatP.≤-refl , refl))
shiftWithin2StartNormalizes = refl

shiftWithin2HeldNormalizes :
  DDSI.shiftConvergesToHeldWithin2 SPTI.shiftHeldExitPoint
    ≡
  (zero , (z≤n , refl))
shiftWithin2HeldNormalizes = refl

record OrderPreservingHeldToStartReversalCandidate : Set where
  constructor orderPreservingHeldToStartReversalCandidate
  field
    convergenceAnchor :
      DDSI.shiftConvergesToHeldWithin2 SPTI.shiftStartPoint
        ≡
      (suc (suc zero) , (NatP.≤-refl , refl))

    heldAnchor :
      DDSI.shiftConvergesToHeldWithin2 SPTI.shiftHeldExitPoint
        ≡
      (zero , (z≤n , refl))

    heldToStartOrderPreserved :
      DDSI.shiftHeldPotential SPTI.shiftStartPoint
        ≤
      DDSI.shiftHeldPotential SPTI.shiftHeldExitPoint

noHeldToStartPotentialOrder :
  DDSI.shiftHeldPotential SPTI.shiftStartPoint
    ≤
  DDSI.shiftHeldPotential SPTI.shiftHeldExitPoint →
  ⊥
noHeldToStartPotentialOrder ()

NoOrderPreservingHeldToStartReversal : Set
NoOrderPreservingHeldToStartReversal =
  OrderPreservingHeldToStartReversalCandidate →
  ⊥

noOrderPreservingHeldToStartReversal :
  NoOrderPreservingHeldToStartReversal
noOrderPreservingHeldToStartReversal candidate =
  noHeldToStartPotentialOrder
    (OrderPreservingHeldToStartReversalCandidate.heldToStartOrderPreserved
      candidate)

record NonInjectiveStageQuotientEvidence : Set where
  constructor nonInjectiveStageQuotientEvidence
  field
    sourceA : Stage
    sourceB : Stage
    sourceDistinct : sourceA ≢ sourceB
    quotientIdentifies :
      SQ.q sourceA ≡ SQ.q sourceB

canonicalNonInjectiveStageQuotientEvidence :
  NonInjectiveStageQuotientEvidence
canonicalNonInjectiveStageQuotientEvidence =
  nonInjectiveStageQuotientEvidence
    seed
    overflow
    seed≢overflow
    seedOverflowQuotientCollapse

record StageQuotientIrreversibilityBoundary : Setω where
  field
    seam :
      SQ.StageQuotientSeam

    nonInjectiveEvidence :
      NonInjectiveStageQuotientEvidence

    logicTlureyToneInspection :
      ∀ s →
      SQ.q s ≡ stageTone s

    irreversibilityCause :
      IrreversibilityCause

    irreversibilityMechanism :
      IrreversibilityCause

    gf3InverseSurface :
      GF3AdditiveInverseSurface

    impossibleQSectionGap :
      StageQuotientLeftInverseSection

    impossibleToneSectionGap :
      StageToneLeftInverseSection

    shiftWithin2StartAnchor :
      DDSI.shiftConvergesToHeldWithin2 SPTI.shiftStartPoint
        ≡
      (suc (suc zero) , (NatP.≤-refl , refl))

    shiftWithin2HeldAnchor :
      DDSI.shiftConvergesToHeldWithin2 SPTI.shiftHeldExitPoint
        ≡
      (zero , (z≤n , refl))

    impossibleOrderPreservingReversalGap :
      NoOrderPreservingHeldToStartReversal

    continuityCurrent :
      SDCC.ShiftDiscreteContinuityCurrent

    shiftWithin2 :
      DDSI.ShiftConvergesToHeldWithin2

    boundaryFlags :
      List StageQuotientBoundaryFlag

    thermodynamicCarnotPromotion :
      Bool

    thermodynamicCarnotPromotionIsFalse :
      thermodynamicCarnotPromotion ≡ false

    physicalCarnotPromotion :
      Bool

    physicalCarnotPromotionIsFalse :
      physicalCarnotPromotion ≡ false

    nonClaimBoundary :
      List String

    stage12FibreSurfaceReceipt :
      SQ.Stage12FibreSurface

    stage12FibreSurfaceReceiptIsCanonical :
      stage12FibreSurfaceReceipt ≡ SQ.canonicalStage12FibreSurface

canonicalStageQuotientIrreversibilityBoundary :
  StageQuotientIrreversibilityBoundary
canonicalStageQuotientIrreversibilityBoundary =
  record
    { seam =
        SQ.stageQuotientSeamSurface
    ; nonInjectiveEvidence =
        canonicalNonInjectiveStageQuotientEvidence
    ; logicTlureyToneInspection =
        stageQuotientInspectsLogicTlureyTone
    ; irreversibilityCause =
        geometricCompression
    ; irreversibilityMechanism =
        nonInjectiveQuotient
    ; gf3InverseSurface =
        canonicalGF3AdditiveInverseSurface
    ; impossibleQSectionGap =
        noStageQuotientLeftInverseSection
    ; impossibleToneSectionGap =
        noStageToneLeftInverseSection
    ; shiftWithin2StartAnchor =
        shiftWithin2StartNormalizes
    ; shiftWithin2HeldAnchor =
        shiftWithin2HeldNormalizes
    ; impossibleOrderPreservingReversalGap =
        noOrderPreservingHeldToStartReversal
    ; continuityCurrent =
        SDCC.shiftDiscreteContinuityCurrent
    ; shiftWithin2 =
        DDSI.shiftConvergesToHeldWithin2
    ; boundaryFlags =
        geometricCompressionOnly
        ∷ quotientNonInjective
        ∷ gf3AdditiveInversesPresent
        ∷ notAbsenceOfGF3AdditiveInverse
        ∷ impossibleSectionGapRecorded
        ∷ impossibleOrderPreservingReversalGapRecorded
        ∷ shiftConvergesToHeldWithin2Consumed
        ∷ finiteContinuityCurrentInspectedOnly
        ∷ noThermodynamicCarnotTheoremPromotion
        ∷ noPhysicalCarnotTheoremPromotion
        ∷ []
    ; thermodynamicCarnotPromotion =
        false
    ; thermodynamicCarnotPromotionIsFalse =
        refl
    ; physicalCarnotPromotion =
        false
    ; physicalCarnotPromotionIsFalse =
        refl
    ; nonClaimBoundary =
        "Irreversibility is recorded as geometric compression through the non-injective Stage -> TriTruth quotient"
        ∷ "The seam is not explained by absence of additive inverse in the GF(3)-style TriTruth operation"
        ∷ "The Stage12FibreSurface receipt is carried conservatively from DASHI.Algebra.StageQuotient"
        ∷ "Its atlas-11 carry-depth seam is retained as imported evidence, not promoted as a new theorem"
        ∷ "The atlas-11 quotient seam remains part of the stage-fibre receipt rather than a collapse claim"
        ∷ "No total left-inverse section can recover both seed and overflow from their shared quotient tone"
        ∷ "No order-preserving held-to-start reversal is supplied; the internal potential order would require 2 <= 0"
        ∷ "shiftConvergesToHeldWithin2 is consumed as an imported finite shift-dynamics witness"
        ∷ "ShiftDiscreteContinuityCurrent is inspected only as a finite continuity/current bookkeeping surface"
        ∷ "No thermodynamic Carnot theorem is promoted from this boundary"
        ∷ "No physical Carnot theorem is promoted from this boundary"
        ∷ []
    ; stage12FibreSurfaceReceipt =
        SQ.canonicalStage12FibreSurface
    ; stage12FibreSurfaceReceiptIsCanonical =
        refl
    }
