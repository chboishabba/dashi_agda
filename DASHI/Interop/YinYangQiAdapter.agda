module DASHI.Interop.YinYangQiAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Core.FormalLensQualificationCore as Lens
import DASHI.Culture.QiOperatorTheoryBoundary as QiTheory
import DASHI.Culture.YinYangPolarityBoundary as YinYang
import DASHI.Interop.QiCarrierFieldBridge as QiBridge

------------------------------------------------------------------------
-- Yin/Yang -> Qi adapter.
--
-- This module is a candidate-only bridge surface.  It maps polarity rows into
-- the existing Qi carrier taxonomy, Qi role grammar, and formal-lens
-- qualification surfaces while keeping all authority lanes blocked.

data YinYangQiBridgeStatus : Set where
  yinYangQiBridge_candidateOnly :
    YinYangQiBridgeStatus

data YinYangQiPromotion : Set where

yinYangQiPromotionImpossible :
  YinYangQiPromotion →
  ⊥
yinYangQiPromotionImpossible ()

data YinYangPolarityRowKind : Set where
  yinStillness :
    YinYangPolarityRowKind

  yangMovement :
    YinYangPolarityRowKind

  balanceThreshold :
    YinYangPolarityRowKind

  breathCirculation :
    YinYangPolarityRowKind

  residualQuiet :
    YinYangPolarityRowKind

  relationCycle :
    YinYangPolarityRowKind

canonicalYinYangPolarityRowKinds :
  List YinYangPolarityRowKind
canonicalYinYangPolarityRowKinds =
  yinStillness
  ∷ yangMovement
  ∷ balanceThreshold
  ∷ breathCirculation
  ∷ residualQuiet
  ∷ relationCycle
  ∷ []

data YinYangQiLensProfile : Set where
  genericLensProfile :
    YinYangQiLensProfile

  gradientLensProfile :
    YinYangQiLensProfile

rowKindLensProfile :
  YinYangPolarityRowKind →
  YinYangQiLensProfile
rowKindLensProfile yinStillness =
  genericLensProfile
rowKindLensProfile yangMovement =
  gradientLensProfile
rowKindLensProfile balanceThreshold =
  genericLensProfile
rowKindLensProfile breathCirculation =
  gradientLensProfile
rowKindLensProfile residualQuiet =
  genericLensProfile
rowKindLensProfile relationCycle =
  genericLensProfile

rowKindQiDomain :
  YinYangPolarityRowKind →
  QiBridge.QiDomain
rowKindQiDomain yinStillness =
  QiBridge.meditationQiDomain
rowKindQiDomain yangMovement =
  QiBridge.taiChiQiDomain
rowKindQiDomain balanceThreshold =
  QiBridge.fengShuiQiDomain
rowKindQiDomain breathCirculation =
  QiBridge.taiChiQiDomain
rowKindQiDomain residualQuiet =
  QiBridge.meditationQiDomain
rowKindQiDomain relationCycle =
  QiBridge.fengShuiQiDomain

rowKindQiCarrier :
  YinYangPolarityRowKind →
  QiBridge.QiCarrier
rowKindQiCarrier yinStillness =
  QiBridge.attentionQiCarrier
rowKindQiCarrier yangMovement =
  QiBridge.movementQiCarrier
rowKindQiCarrier balanceThreshold =
  QiBridge.thresholdQiCarrier
rowKindQiCarrier breathCirculation =
  QiBridge.breathQiCarrier
rowKindQiCarrier residualQuiet =
  QiBridge.residualMindNoiseQiCarrier
rowKindQiCarrier relationCycle =
  QiBridge.relationQiCarrier

rowKindQiRole :
  YinYangPolarityRowKind →
  QiTheory.QiRoleCategory
rowKindQiRole yinStillness =
  QiTheory.QiBoundaryGate
rowKindQiRole yangMovement =
  QiTheory.QiOperator
rowKindQiRole balanceThreshold =
  QiTheory.QiStateSpace
rowKindQiRole breathCirculation =
  QiTheory.QiObservable
rowKindQiRole residualQuiet =
  QiTheory.QiObstruction
rowKindQiRole relationCycle =
  QiTheory.QiAlgebra

rowKindFormalLensSurface :
  YinYangPolarityRowKind →
  Lens.FormalLensQualificationSurface
rowKindFormalLensSurface yinStillness =
  Lens.canonicalGenericFormalLensQualificationSurface
rowKindFormalLensSurface yangMovement =
  Lens.canonicalGradientResistiveQualificationSurface
rowKindFormalLensSurface balanceThreshold =
  Lens.canonicalGenericFormalLensQualificationSurface
rowKindFormalLensSurface breathCirculation =
  Lens.canonicalGradientResistiveQualificationSurface
rowKindFormalLensSurface residualQuiet =
  Lens.canonicalGenericFormalLensQualificationSurface
rowKindFormalLensSurface relationCycle =
  Lens.canonicalGenericFormalLensQualificationSurface

rowKindFormalLensReceipt :
  (rowKind : YinYangPolarityRowKind) →
  Lens.FormalLensQualificationReceipt (rowKindFormalLensSurface rowKind)
rowKindFormalLensReceipt yinStillness =
  Lens.canonicalGenericFormalLensQualificationReceipt
rowKindFormalLensReceipt yangMovement =
  Lens.canonicalGradientResistiveQualificationReceipt
rowKindFormalLensReceipt balanceThreshold =
  Lens.canonicalGenericFormalLensQualificationReceipt
rowKindFormalLensReceipt breathCirculation =
  Lens.canonicalGradientResistiveQualificationReceipt
rowKindFormalLensReceipt residualQuiet =
  Lens.canonicalGenericFormalLensQualificationReceipt
rowKindFormalLensReceipt relationCycle =
  Lens.canonicalGenericFormalLensQualificationReceipt

rowKindProfile :
  YinYangPolarityRowKind →
  String
rowKindProfile yinStillness =
  "yin-stillness"
rowKindProfile yangMovement =
  "yang-movement"
rowKindProfile balanceThreshold =
  "balance-threshold"
rowKindProfile breathCirculation =
  "breath-circulation"
rowKindProfile residualQuiet =
  "residual-quiet"
rowKindProfile relationCycle =
  "relation-cycle"

rowKindStatement :
  YinYangPolarityRowKind →
  String
rowKindStatement yinStillness =
  "Stillness is read as a candidate-only Qi boundary gate in the meditation carrier."
rowKindStatement yangMovement =
  "Movement is read as a candidate-only Qi operator in the Tai Chi carrier."
rowKindStatement balanceThreshold =
  "Balance is read as a candidate-only Qi state-space threshold in the Feng Shui carrier."
rowKindStatement breathCirculation =
  "Breath circulation is read as a candidate-only Qi observable in the Tai Chi carrier."
rowKindStatement residualQuiet =
  "Residual quiet is read as a candidate-only Qi obstruction surface in the meditation carrier."
rowKindStatement relationCycle =
  "Relation cycle is read as a candidate-only Qi algebra surface in the Feng Shui carrier."

yinStillnessMapsToMeditationCarrier :
  rowKindQiCarrier yinStillness ≡ QiBridge.attentionQiCarrier
yinStillnessMapsToMeditationCarrier =
  refl

yangMovementMapsToMovementCarrier :
  rowKindQiCarrier yangMovement ≡ QiBridge.movementQiCarrier
yangMovementMapsToMovementCarrier =
  refl

balanceThresholdMapsToThresholdCarrier :
  rowKindQiCarrier balanceThreshold ≡ QiBridge.thresholdQiCarrier
balanceThresholdMapsToThresholdCarrier =
  refl

breathCirculationMapsToBreathCarrier :
  rowKindQiCarrier breathCirculation ≡ QiBridge.breathQiCarrier
breathCirculationMapsToBreathCarrier =
  refl

residualQuietMapsToResidualCarrier :
  rowKindQiCarrier residualQuiet ≡ QiBridge.residualMindNoiseQiCarrier
residualQuietMapsToResidualCarrier =
  refl

relationCycleMapsToRelationCarrier :
  rowKindQiCarrier relationCycle ≡ QiBridge.relationQiCarrier
relationCycleMapsToRelationCarrier =
  refl

record YinYangQiAuthorityClosure : Set where
  constructor yinYangQiAuthorityClosure
  field
    authorityBlocked :
      Bool

    truthAuthority :
      Bool

    supportAuthority :
      Bool

    admissibilityAuthority :
      Bool

    tradingAuthority :
      Bool

    runtimeAuthority :
      Bool

    theoremAuthority :
      Bool

    clinicalAuthority :
      Bool

    metaphysicalAuthority :
      Bool

open YinYangQiAuthorityClosure public

record YinYangQiAuthorityReceipt
  (closure : YinYangQiAuthorityClosure) :
  Set where
  constructor yinYangQiAuthorityReceipt
  field
    authorityBlockedIsTrue :
      authorityBlocked closure ≡ true

    truthAuthorityIsFalse :
      truthAuthority closure ≡ false

    supportAuthorityIsFalse :
      supportAuthority closure ≡ false

    admissibilityAuthorityIsFalse :
      admissibilityAuthority closure ≡ false

    tradingAuthorityIsFalse :
      tradingAuthority closure ≡ false

    runtimeAuthorityIsFalse :
      runtimeAuthority closure ≡ false

    theoremAuthorityIsFalse :
      theoremAuthority closure ≡ false

    clinicalAuthorityIsFalse :
      clinicalAuthority closure ≡ false

    metaphysicalAuthorityIsFalse :
      metaphysicalAuthority closure ≡ false

open YinYangQiAuthorityReceipt public

canonicalYinYangQiAuthorityClosure :
  YinYangQiAuthorityClosure
canonicalYinYangQiAuthorityClosure =
  yinYangQiAuthorityClosure
    true
    false
    false
    false
    false
    false
    false
    false
    false

canonicalYinYangQiAuthorityReceipt :
  YinYangQiAuthorityReceipt canonicalYinYangQiAuthorityClosure
canonicalYinYangQiAuthorityReceipt =
  yinYangQiAuthorityReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record YinYangQiAdapterRow : Set where
  constructor yinYangQiAdapterRow
  field
    rowId :
      Nat

    sourcePolarity :
      YinYangPolarityRowKind

    qiDomain :
      QiBridge.QiDomain

    qiCarrier :
      QiBridge.QiCarrier

    qiRole :
      QiTheory.QiRoleCategory

    formalLensSurface :
      Lens.FormalLensQualificationSurface

    formalLensSurfaceIsCanonical :
      formalLensSurface ≡ rowKindFormalLensSurface sourcePolarity

    formalLensReceipt :
      Lens.FormalLensQualificationReceipt formalLensSurface

    rowProfile :
      String

    rowStatement :
      String

    candidateOnly :
      Bool

    promoted :
      Bool

    authorityClosure :
      YinYangQiAuthorityClosure

    authorityClosureIsCanonical :
      authorityClosure ≡ canonicalYinYangQiAuthorityClosure

    authorityReceipt :
      YinYangQiAuthorityReceipt authorityClosure

open YinYangQiAdapterRow public

record YinYangQiAdapterRowReceipt
  (row : YinYangQiAdapterRow) :
  Set where
  constructor yinYangQiAdapterRowReceipt
  field
    rowCandidateOnlyIsTrue :
      candidateOnly row ≡ true

    rowPromotedIsFalse :
      promoted row ≡ false

    rowAuthorityBlockedIsTrue :
      authorityBlocked (authorityClosure row) ≡ true

    rowTruthAuthorityIsFalse :
      truthAuthority (authorityClosure row) ≡ false

    rowSupportAuthorityIsFalse :
      supportAuthority (authorityClosure row) ≡ false

    rowAdmissibilityAuthorityIsFalse :
      admissibilityAuthority (authorityClosure row) ≡ false

    rowTradingAuthorityIsFalse :
      tradingAuthority (authorityClosure row) ≡ false

    rowRuntimeAuthorityIsFalse :
      runtimeAuthority (authorityClosure row) ≡ false

    rowTheoremAuthorityIsFalse :
      theoremAuthority (authorityClosure row) ≡ false

    rowClinicalAuthorityIsFalse :
      clinicalAuthority (authorityClosure row) ≡ false

    rowMetaphysicalAuthorityIsFalse :
      metaphysicalAuthority (authorityClosure row) ≡ false

    rowAuthorityClosureIsCanonical :
      authorityClosure row ≡ canonicalYinYangQiAuthorityClosure

    rowQiDomainIsCanonical :
      qiDomain row ≡ rowKindQiDomain (sourcePolarity row)

    rowQiCarrierIsCanonical :
      qiCarrier row ≡ rowKindQiCarrier (sourcePolarity row)

    rowQiRoleIsCanonical :
      qiRole row ≡ rowKindQiRole (sourcePolarity row)

    rowFormalLensSurfaceIsCanonical :
      formalLensSurface row ≡ rowKindFormalLensSurface (sourcePolarity row)

open YinYangQiAdapterRowReceipt public

mkYinYangQiAdapterRow :
  Nat →
  YinYangPolarityRowKind →
  String →
  String →
  YinYangQiAdapterRow
mkYinYangQiAdapterRow rowId polarity profile statement =
  yinYangQiAdapterRow
    rowId
    polarity
    (rowKindQiDomain polarity)
    (rowKindQiCarrier polarity)
    (rowKindQiRole polarity)
    (rowKindFormalLensSurface polarity)
    refl
    (rowKindFormalLensReceipt polarity)
    profile
    statement
    true
    false
    canonicalYinYangQiAuthorityClosure
    refl
    canonicalYinYangQiAuthorityReceipt

yinStillnessRow :
  YinYangQiAdapterRow
yinStillnessRow =
  mkYinYangQiAdapterRow
    zero
    yinStillness
    (rowKindProfile yinStillness)
    (rowKindStatement yinStillness)

yangMovementRow :
  YinYangQiAdapterRow
yangMovementRow =
  mkYinYangQiAdapterRow
    (suc zero)
    yangMovement
    (rowKindProfile yangMovement)
    (rowKindStatement yangMovement)

balanceThresholdRow :
  YinYangQiAdapterRow
balanceThresholdRow =
  mkYinYangQiAdapterRow
    (suc (suc zero))
    balanceThreshold
    (rowKindProfile balanceThreshold)
    (rowKindStatement balanceThreshold)

breathCirculationRow :
  YinYangQiAdapterRow
breathCirculationRow =
  mkYinYangQiAdapterRow
    (suc (suc (suc zero)))
    breathCirculation
    (rowKindProfile breathCirculation)
    (rowKindStatement breathCirculation)

residualQuietRow :
  YinYangQiAdapterRow
residualQuietRow =
  mkYinYangQiAdapterRow
    (suc (suc (suc (suc zero))))
    residualQuiet
    (rowKindProfile residualQuiet)
    (rowKindStatement residualQuiet)

relationCycleRow :
  YinYangQiAdapterRow
relationCycleRow =
  mkYinYangQiAdapterRow
    (suc (suc (suc (suc (suc zero)))))
    relationCycle
    (rowKindProfile relationCycle)
    (rowKindStatement relationCycle)

canonicalYinYangQiAdapterRows :
  List YinYangQiAdapterRow
canonicalYinYangQiAdapterRows =
  yinStillnessRow
  ∷ yangMovementRow
  ∷ balanceThresholdRow
  ∷ breathCirculationRow
  ∷ residualQuietRow
  ∷ relationCycleRow
  ∷ []

yinStillnessRowReceipt :
  YinYangQiAdapterRowReceipt yinStillnessRow
yinStillnessRowReceipt =
  yinYangQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

yangMovementRowReceipt :
  YinYangQiAdapterRowReceipt yangMovementRow
yangMovementRowReceipt =
  yinYangQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

balanceThresholdRowReceipt :
  YinYangQiAdapterRowReceipt balanceThresholdRow
balanceThresholdRowReceipt =
  yinYangQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

breathCirculationRowReceipt :
  YinYangQiAdapterRowReceipt breathCirculationRow
breathCirculationRowReceipt =
  yinYangQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

residualQuietRowReceipt :
  YinYangQiAdapterRowReceipt residualQuietRow
residualQuietRowReceipt =
  yinYangQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

relationCycleRowReceipt :
  YinYangQiAdapterRowReceipt relationCycleRow
relationCycleRowReceipt =
  yinYangQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalYinYangQiFormalLensSurfaces :
  List Lens.FormalLensQualificationSurface
canonicalYinYangQiFormalLensSurfaces =
  rowKindFormalLensSurface yinStillness
  ∷ rowKindFormalLensSurface yangMovement
  ∷ rowKindFormalLensSurface balanceThreshold
  ∷ rowKindFormalLensSurface breathCirculation
  ∷ rowKindFormalLensSurface residualQuiet
  ∷ rowKindFormalLensSurface relationCycle
  ∷ []

yinYangQiCandidateOnlyRow :
  Candidate.CandidateOnlyRow
yinYangQiCandidateOnlyRow =
  Candidate.mkCandidateOnlyRow
    "yin-yang qi candidate-only bridge"
    "DASHI.Interop.YinYangQiAdapter"
    "yinYangQiCandidateOnlyRow"
    Candidate.bridgeCandidateKind
    Candidate.bridgeCandidateOnlyStatus
    "Yin/Yang polarity rows are carried into Qi carrier, role, and formal-lens surfaces as candidate-only readings."
    "No truth, support, admissibility, trading, runtime, theorem, clinical, or metaphysical authority is supplied."

canonicalYinYangQiCandidateOnlyReceipt :
  Candidate.CandidateOnlyReceipt yinYangQiCandidateOnlyRow
canonicalYinYangQiCandidateOnlyReceipt =
  Candidate.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record YinYangQiBridgeReceipt : Set where
  constructor yinYangQiBridgeReceipt
  field
    bridgeStatus :
      YinYangQiBridgeStatus

    bridgeStatusIsCanonical :
      bridgeStatus ≡ yinYangQiBridge_candidateOnly

    qiCarrierBridge :
      QiBridge.QiCarrierFieldBridgeReceipt

    qiCarrierBridgeIsCanonical :
      qiCarrierBridge ≡ QiBridge.canonicalQiCarrierFieldBridgeReceipt

    qiRoleBoundary :
      QiTheory.QiOperatorTheoryBoundaryReceipt

    qiRoleBoundaryIsCanonical :
      qiRoleBoundary ≡ QiTheory.canonicalQiOperatorTheoryBoundaryReceipt

    polarityBoundary :
      YinYang.YinYangPolarityBoundaryReceipt

    polarityBoundaryIsCanonical :
      polarityBoundary ≡ YinYang.canonicalYinYangPolarityBoundaryReceipt

    candidateOnlyCoreAdapter :
      Candidate.CandidateOnlyReceipt yinYangQiCandidateOnlyRow

    candidateOnlyCoreAdapterIsCanonical :
      candidateOnlyCoreAdapter ≡ canonicalYinYangQiCandidateOnlyReceipt

    authorityClosure :
      YinYangQiAuthorityClosure

    authorityClosureIsCanonical :
      authorityClosure ≡ canonicalYinYangQiAuthorityClosure

    bridgeRows :
      List YinYangQiAdapterRow

    bridgeRowsAreCanonical :
      bridgeRows ≡ canonicalYinYangQiAdapterRows

    formalLensSurfaces :
      List Lens.FormalLensQualificationSurface

    formalLensSurfacesAreCanonical :
      formalLensSurfaces ≡ canonicalYinYangQiFormalLensSurfaces

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    promotionImpossible :
      YinYangQiPromotion →
      ⊥

    bridgeReading :
      String

open YinYangQiBridgeReceipt public

canonicalYinYangQiBridgeReceipt :
  YinYangQiBridgeReceipt
canonicalYinYangQiBridgeReceipt =
  yinYangQiBridgeReceipt
    yinYangQiBridge_candidateOnly
    refl
    QiBridge.canonicalQiCarrierFieldBridgeReceipt
    refl
    QiTheory.canonicalQiOperatorTheoryBoundaryReceipt
    refl
    YinYang.canonicalYinYangPolarityBoundaryReceipt
    refl
    canonicalYinYangQiCandidateOnlyReceipt
    refl
    canonicalYinYangQiAuthorityClosure
    refl
    canonicalYinYangQiAdapterRows
    refl
    canonicalYinYangQiFormalLensSurfaces
    refl
    true
    refl
    false
    refl
    yinYangQiPromotionImpossible
    "Yin/Yang polarity rows are interpreted as candidate-only Qi carrier, role, and formal-lens bridges with all authority lanes blocked."

canonicalYinYangQiBridgeCandidateOnly :
  candidateOnly canonicalYinYangQiBridgeReceipt ≡ true
canonicalYinYangQiBridgeCandidateOnly =
  refl

canonicalYinYangQiBridgePromotedFalse :
  promoted canonicalYinYangQiBridgeReceipt ≡ false
canonicalYinYangQiBridgePromotedFalse =
  refl

canonicalYinYangQiBridgeStatus :
  bridgeStatus canonicalYinYangQiBridgeReceipt
  ≡
  yinYangQiBridge_candidateOnly
canonicalYinYangQiBridgeStatus =
  refl

canonicalYinYangQiBridgeAuthorityBlocked :
  authorityBlocked
    (authorityClosure canonicalYinYangQiBridgeReceipt)
  ≡
  true
canonicalYinYangQiBridgeAuthorityBlocked =
  refl

canonicalYinYangQiBridgeTruthAuthorityFalse :
  truthAuthority
    (authorityClosure canonicalYinYangQiBridgeReceipt)
  ≡
  false
canonicalYinYangQiBridgeTruthAuthorityFalse =
  refl

canonicalYinYangQiBridgeQiCarrierBridgeCanonical :
  qiCarrierBridge canonicalYinYangQiBridgeReceipt
  ≡
  QiBridge.canonicalQiCarrierFieldBridgeReceipt
canonicalYinYangQiBridgeQiCarrierBridgeCanonical =
  refl

canonicalYinYangQiBridgeQiRoleBoundaryCanonical :
  qiRoleBoundary canonicalYinYangQiBridgeReceipt
  ≡
  QiTheory.canonicalQiOperatorTheoryBoundaryReceipt
canonicalYinYangQiBridgeQiRoleBoundaryCanonical =
  refl

canonicalYinYangQiBridgePolarityBoundaryCanonical :
  polarityBoundary canonicalYinYangQiBridgeReceipt
  ≡
  YinYang.canonicalYinYangPolarityBoundaryReceipt
canonicalYinYangQiBridgePolarityBoundaryCanonical =
  refl
