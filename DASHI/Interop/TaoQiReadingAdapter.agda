module DASHI.Interop.TaoQiReadingAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.QiOperatorTheoryBoundary as QiTheory
import DASHI.Culture.TaoChapterReadingReceipt as Tao
import DASHI.Interop.QiCarrierFieldBridge as QiBridge
import DASHI.Interop.TypedTermRoleFunctor as TypedTermRole

------------------------------------------------------------------------
-- Tao -> Qi reading adapter.
--
-- This bridge maps Tao motifs into existing Qi carrier domains, Qi role
-- grammar, and Qi formal-lens readings.  It is interpretive and fail-closed:
-- Tao does not validate Qi, Qi does not validate Tao, and no empirical,
-- clinical, spiritual, mystical, metaphysical, political, or philological
-- authority is promoted here.  It also carries the newer body, boundary,
-- seed, carry, and completion/stage material on the direct Tao -> Qi path
-- where that remains a useful candidate-only rereading beside the Tao ->
-- Yin/Yang -> Qi route.

data TaoQiAdapterStrength : Set where
  LexicalResonance : TaoQiAdapterStrength
  MetaphorAlignment : TaoQiAdapterStrength
  CarrierAlignment : TaoQiAdapterStrength
  OperatorAlignment : TaoQiAdapterStrength
  FlowAlignment : TaoQiAdapterStrength
  BoundaryAlignment : TaoQiAdapterStrength
  MeditationStateAlignment : TaoQiAdapterStrength
  SpectralAnalogy : TaoQiAdapterStrength
  GovernanceAnalogy : TaoQiAdapterStrength
  WeakCandidateOnly : TaoQiAdapterStrength

record TaoQiAuthorityBits : Set where
  constructor taoQiAuthorityBits
  field
    taoPromotesQi : Bool
    qiPromotesTao : Bool
    empiricalAuthority : Bool
    clinicalAuthority : Bool
    spiritualAuthority : Bool
    mysticalAuthority : Bool
    metaphysicalAuthority : Bool
    politicalAuthority : Bool
    philologicalAuthority : Bool
    practiceInstruction : Bool
    candidateInteropOnly : Bool

open TaoQiAuthorityBits public

canonicalTaoQiAuthorityBits : TaoQiAuthorityBits
canonicalTaoQiAuthorityBits =
  taoQiAuthorityBits
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    true

record TaoQiFailClosed : Set where
  constructor taoQiFailClosed
  field
    taoPromotesQiFalse : taoPromotesQi canonicalTaoQiAuthorityBits ≡ false
    qiPromotesTaoFalse : qiPromotesTao canonicalTaoQiAuthorityBits ≡ false
    empiricalAuthorityFalse : empiricalAuthority canonicalTaoQiAuthorityBits ≡ false
    clinicalAuthorityFalse : clinicalAuthority canonicalTaoQiAuthorityBits ≡ false
    spiritualAuthorityFalse : spiritualAuthority canonicalTaoQiAuthorityBits ≡ false
    mysticalAuthorityFalse : mysticalAuthority canonicalTaoQiAuthorityBits ≡ false
    metaphysicalAuthorityFalse : metaphysicalAuthority canonicalTaoQiAuthorityBits ≡ false
    politicalAuthorityFalse : politicalAuthority canonicalTaoQiAuthorityBits ≡ false
    philologicalAuthorityFalse : philologicalAuthority canonicalTaoQiAuthorityBits ≡ false
    practiceInstructionFalse : practiceInstruction canonicalTaoQiAuthorityBits ≡ false
    candidateInteropOnlyTrue : candidateInteropOnly canonicalTaoQiAuthorityBits ≡ true

canonicalTaoQiFailClosed : TaoQiFailClosed
canonicalTaoQiFailClosed =
  taoQiFailClosed
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

record TaoQiAdapterRow : Set where
  constructor taoQiAdapterRow
  field
    rowId : Nat
    chapterId : Tao.TaoChapterId
    taoMotif : Tao.TaoMotif
    taoReadingKind : Tao.TaoReadingKind
    qiDomain : QiBridge.QiDomain
    qiCarrier : QiBridge.QiCarrier
    qiRole : QiTheory.QiRoleCategory
    formalLens : QiTheory.QiFormalLensReading
    adapterStrength : TaoQiAdapterStrength
    candidateOnly : Bool
    authorityAllowed : Bool
    reading : String

open TaoQiAdapterRow public

record TaoQiAdapterRowReceipt (row : TaoQiAdapterRow) : Set where
  constructor taoQiAdapterRowReceipt
  field
    candidateOnlyTrue : candidateOnly row ≡ true
    authorityAllowedFalse : authorityAllowed row ≡ false

open TaoQiAdapterRowReceipt public

gateThresholdRow : TaoQiAdapterRow
gateThresholdRow =
  taoQiAdapterRow
    zero
    Tao.chapter1
    Tao.gate
    Tao.NamingBoundary
    QiBridge.fengShuiQiDomain
    QiBridge.thresholdQiCarrier
    QiTheory.QiBoundaryGate
    QiTheory.qiCategoryReading
    BoundaryAlignment
    true
    false
    "Gate and naming-boundary motifs map candidate-only into the Feng Shui threshold carrier and Qi boundary-gate grammar."

boundaryThresholdRow : TaoQiAdapterRow
boundaryThresholdRow =
  taoQiAdapterRow
    (suc zero)
    Tao.chapter11
    Tao.boundary
    Tao.EmptinessUtilityGrammar
    QiBridge.fengShuiQiDomain
    QiBridge.thresholdQiCarrier
    QiTheory.QiBoundaryGate
    QiTheory.qiCategoryReading
    BoundaryAlignment
    true
    false
    "Boundary motifs map candidate-only into the Feng Shui threshold carrier and Qi boundary-gate grammar through emptiness-as-useful-space."

valleyLandscapeRow : TaoQiAdapterRow
valleyLandscapeRow =
  taoQiAdapterRow
    (suc (suc zero))
    Tao.chapter6
    Tao.valley
    Tao.OriginMetaphor
    QiBridge.fengShuiQiDomain
    QiBridge.landscapeQiCarrier
    QiTheory.QiStateSpace
    QiTheory.qiCategoryReading
    MetaphorAlignment
    true
    false
    "Valley motifs map candidate-only into the Feng Shui landscape carrier as state-space grammar."

breathCarrierRow : TaoQiAdapterRow
breathCarrierRow =
  taoQiAdapterRow
    (suc (suc (suc zero)))
    Tao.chapter10
    Tao.breath
    Tao.PracticeAphorism
    QiBridge.taiChiQiDomain
    QiBridge.breathQiCarrier
    QiTheory.QiOperator
    QiTheory.qiGradientFlowReading
    CarrierAlignment
    true
    false
    "Breath motifs map candidate-only into the Tai Chi breath carrier and gradient-flow reading."

stillnessMeditationRow : TaoQiAdapterRow
stillnessMeditationRow =
  taoQiAdapterRow
    (suc (suc (suc (suc zero))))
    Tao.chapter16
    Tao.stillness
    Tao.StillnessGrammar
    QiBridge.meditationQiDomain
    QiBridge.attentionQiCarrier
    QiTheory.QiBoundaryGate
    QiTheory.qiGradientFlowReading
    MeditationStateAlignment
    true
    false
    "Stillness motifs map candidate-only into the meditation attention carrier and gradient-flow gate grammar."

waterFlowRow : TaoQiAdapterRow
waterFlowRow =
  taoQiAdapterRow
    (suc (suc (suc (suc (suc zero)))))
    Tao.chapter8
    Tao.water
    Tao.SoftOverHardOperator
    QiBridge.taiChiQiDomain
    QiBridge.movementQiCarrier
    QiTheory.QiOperator
    QiTheory.qiGradientFlowReading
    FlowAlignment
    true
    false
    "Water motifs map candidate-only into the movement carrier as non-contentious flow grammar."

completionStageRow : TaoQiAdapterRow
completionStageRow =
  taoQiAdapterRow
    (suc (suc (suc (suc (suc (suc zero))))))
    Tao.chapter10
    Tao.returnToRoot
    Tao.ReturnToRootGrammar
    QiBridge.meditationQiDomain
    QiBridge.attentionQiCarrier
    QiTheory.QiBoundaryGate
    QiTheory.qiGradientFlowReading
    MeditationStateAlignment
    true
    false
    "Return-to-root motifs map candidate-only into the meditation attention carrier as a completion/stage rereading rather than a promoted conclusion."

bodyStageRow : TaoQiAdapterRow
bodyStageRow =
  taoQiAdapterRow
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
    Tao.chapter28
    Tao.body
    Tao.UncarvedBlockGrammar
    QiBridge.taiChiQiDomain
    QiBridge.bodyQiCarrier
    QiTheory.QiStateSpace
    QiTheory.qiCategoryReading
    CarrierAlignment
    true
    false
    "Body motifs map candidate-only into the Tai Chi body carrier as a stage-space surface of uncarved potential."

desireReductionRow : TaoQiAdapterRow
desireReductionRow =
  taoQiAdapterRow
    (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    Tao.chapter19
    Tao.desireReduction
    Tao.DesireReductionGrammar
    QiBridge.meditationQiDomain
    QiBridge.affectQiCarrier
    QiTheory.QiObstruction
    QiTheory.qiResistiveTransportReading
    GovernanceAnalogy
    true
    false
    "Desire-reduction motifs map candidate-only into the affect carrier and resistive-transport obstruction grammar."

complementarityRow : TaoQiAdapterRow
complementarityRow =
  taoQiAdapterRow
    (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    Tao.chapter2
    Tao.complementarity
    Tao.ComplementarityGrammar
    QiBridge.fengShuiQiDomain
    QiBridge.relationQiCarrier
    QiTheory.QiAlgebra
    QiTheory.qiSymbolicRationalReading
    OperatorAlignment
    true
    false
    "Complementarity motifs map candidate-only into relation carriers and symbolic-rational algebra grammar."

seedCarryRow : TaoQiAdapterRow
seedCarryRow =
  taoQiAdapterRow
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    Tao.chapter37
    Tao.seed
    Tao.CarrySeedGrammar
    QiBridge.meditationQiDomain
    QiBridge.memoryQiCarrier
    QiTheory.QiStateSpace
    QiTheory.qiCategoryReading
    CarrierAlignment
    true
    false
    "Seed motifs map candidate-only into the meditation memory carrier as a stage-bearing precondition for the next transition."

carryBodyRow : TaoQiAdapterRow
carryBodyRow =
  taoQiAdapterRow
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
    Tao.chapter37
    Tao.carry
    Tao.CarrySeedGrammar
    QiBridge.taiChiQiDomain
    QiBridge.bodyQiCarrier
    QiTheory.QiOperator
    QiTheory.qiGradientFlowReading
    FlowAlignment
    true
    false
    "Carry motifs map candidate-only into the Tai Chi body carrier as a carried flow rather than a promoted completion claim."

softnessSpectralRow : TaoQiAdapterRow
softnessSpectralRow =
  taoQiAdapterRow
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
    Tao.chapter36
    Tao.softness
    Tao.ReversalGrammar
    QiBridge.taiChiQiDomain
    QiBridge.forceQiCarrier
    QiTheory.QiObservable
    QiTheory.qiSpectralReading
    SpectralAnalogy
    true
    false
    "Softness and reversal motifs map candidate-only into force carriers and spectral analogy rather than validated outcomes."

canonicalTaoQiAdapterRows : List TaoQiAdapterRow
canonicalTaoQiAdapterRows =
  gateThresholdRow
  ∷ boundaryThresholdRow
  ∷ valleyLandscapeRow
  ∷ breathCarrierRow
  ∷ stillnessMeditationRow
  ∷ waterFlowRow
  ∷ completionStageRow
  ∷ bodyStageRow
  ∷ desireReductionRow
  ∷ complementarityRow
  ∷ seedCarryRow
  ∷ carryBodyRow
  ∷ softnessSpectralRow
  ∷ []

gateThresholdRowReceipt : TaoQiAdapterRowReceipt gateThresholdRow
gateThresholdRowReceipt = taoQiAdapterRowReceipt refl refl

boundaryThresholdRowReceipt : TaoQiAdapterRowReceipt boundaryThresholdRow
boundaryThresholdRowReceipt = taoQiAdapterRowReceipt refl refl

valleyLandscapeRowReceipt : TaoQiAdapterRowReceipt valleyLandscapeRow
valleyLandscapeRowReceipt = taoQiAdapterRowReceipt refl refl

breathCarrierRowReceipt : TaoQiAdapterRowReceipt breathCarrierRow
breathCarrierRowReceipt = taoQiAdapterRowReceipt refl refl

stillnessMeditationRowReceipt : TaoQiAdapterRowReceipt stillnessMeditationRow
stillnessMeditationRowReceipt = taoQiAdapterRowReceipt refl refl

waterFlowRowReceipt : TaoQiAdapterRowReceipt waterFlowRow
waterFlowRowReceipt = taoQiAdapterRowReceipt refl refl

completionStageRowReceipt : TaoQiAdapterRowReceipt completionStageRow
completionStageRowReceipt = taoQiAdapterRowReceipt refl refl

bodyStageRowReceipt : TaoQiAdapterRowReceipt bodyStageRow
bodyStageRowReceipt = taoQiAdapterRowReceipt refl refl

desireReductionRowReceipt : TaoQiAdapterRowReceipt desireReductionRow
desireReductionRowReceipt = taoQiAdapterRowReceipt refl refl

complementarityRowReceipt : TaoQiAdapterRowReceipt complementarityRow
complementarityRowReceipt = taoQiAdapterRowReceipt refl refl

seedCarryRowReceipt : TaoQiAdapterRowReceipt seedCarryRow
seedCarryRowReceipt = taoQiAdapterRowReceipt refl refl

carryBodyRowReceipt : TaoQiAdapterRowReceipt carryBodyRow
carryBodyRowReceipt = taoQiAdapterRowReceipt refl refl

softnessSpectralRowReceipt : TaoQiAdapterRowReceipt softnessSpectralRow
softnessSpectralRowReceipt = taoQiAdapterRowReceipt refl refl

data TaoQiPromotion : Set where

taoQiPromotionImpossible : TaoQiPromotion → ⊥
taoQiPromotionImpossible ()

record TaoQiBridgeReceipt : Set where
  constructor taoQiBridgeReceipt
  field
    taoSource : Tao.TaoSourceReceipt
    taoSourceIsCanonical : taoSource ≡ Tao.canonicalTaoSourceReceipt
    taoChapter : Tao.TaoChapterReceipt
    taoChapterIsCanonical : taoChapter ≡ Tao.chapter1Receipt
    qiCarrierBridge : QiBridge.QiCarrierFieldBridgeReceipt
    qiCarrierBridgeIsCanonical : qiCarrierBridge ≡ QiBridge.canonicalQiCarrierFieldBridgeReceipt
    qiOperatorBoundary : QiTheory.QiOperatorTheoryBoundaryReceipt
    qiOperatorBoundaryIsCanonical : qiOperatorBoundary ≡ QiTheory.canonicalQiOperatorTheoryBoundaryReceipt
    typedQiAnchor : TypedTermRole.TypedTerm
    typedQiAnchorIsCanonical : typedQiAnchor ≡ TypedTermRole.QiOperator
    adapterRows : List TaoQiAdapterRow
    adapterRowsAreCanonical : adapterRows ≡ canonicalTaoQiAdapterRows
    authorityBits : TaoQiAuthorityBits
    authorityBitsAreCanonical : authorityBits ≡ canonicalTaoQiAuthorityBits
    failClosed : TaoQiFailClosed
    failClosedIsCanonical : failClosed ≡ canonicalTaoQiFailClosed
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    promoted : Bool
    promotedIsFalse : promoted ≡ false
    promotionImpossible : TaoQiPromotion → ⊥
    reading : String

open TaoQiBridgeReceipt public

canonicalTaoQiBridgeReceipt : TaoQiBridgeReceipt
canonicalTaoQiBridgeReceipt =
  taoQiBridgeReceipt
    Tao.canonicalTaoSourceReceipt
    refl
    Tao.chapter1Receipt
    refl
    QiBridge.canonicalQiCarrierFieldBridgeReceipt
    refl
    QiTheory.canonicalQiOperatorTheoryBoundaryReceipt
    refl
    TypedTermRole.QiOperator
    refl
    canonicalTaoQiAdapterRows
    refl
    canonicalTaoQiAuthorityBits
    refl
    canonicalTaoQiFailClosed
    refl
    true
    refl
    false
    refl
    taoQiPromotionImpossible
    "Tao chapter motifs are re-read as candidate-only Qi carrier, role, and formal-lens grammar without reciprocal validation or authority promotion."
