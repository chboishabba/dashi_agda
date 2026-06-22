module DASHI.Culture.YinYangPolarityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Culture.TaoChapterReadingReceipt as Tao
import DASHI.Culture.TaoOperatorGrammar as TaoGrammar
import DASHI.Culture.QiOperatorTheoryBoundary as QiTheory

------------------------------------------------------------------------
-- Yin / yang polarity boundary.
--
-- This module is candidate-only.  It sits between Tao operator grammar and
-- Qi operator / formal-lens grammar, and records a closed interpretive
-- boundary for polarity transitions only.  It does not promote doctrine,
-- empirical, clinical, political, mystical, metaphysical, or canonical
-- authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data YinYangPolarityBoundaryStatus : Set where
  candidateOnlyNonPromotingBoundary :
    YinYangPolarityBoundaryStatus

data PolarityTerm : Set where
  yinPole : PolarityTerm
  yangPole : PolarityTerm
  balancedMiddle : PolarityTerm
  thresholdPole : PolarityTerm
  returnPole : PolarityTerm
  reversalPole : PolarityTerm
  softnessPole : PolarityTerm
  stillnessPole : PolarityTerm
  emptinessPole : PolarityTerm
  complementPole : PolarityTerm
  localBodyPole : PolarityTerm
  boundaryCutPole : PolarityTerm
  bodyBoundarySeedPole : PolarityTerm
  oppositeSeedPole : PolarityTerm
  carryPole : PolarityTerm
  successorPole : PolarityTerm
  p31Plus0Plus1Pole : PolarityTerm
  seedCarryPole : PolarityTerm

polarityTermLabel : PolarityTerm → String
polarityTermLabel yinPole = "yin pole"
polarityTermLabel yangPole = "yang pole"
polarityTermLabel balancedMiddle = "balanced middle"
polarityTermLabel thresholdPole = "threshold pole"
polarityTermLabel returnPole = "return pole"
polarityTermLabel reversalPole = "reversal pole"
polarityTermLabel softnessPole = "softness pole"
polarityTermLabel stillnessPole = "stillness pole"
polarityTermLabel emptinessPole = "emptiness pole"
polarityTermLabel complementPole = "complement pole"
polarityTermLabel localBodyPole = "local body pole"
polarityTermLabel boundaryCutPole = "boundary cut pole"
polarityTermLabel bodyBoundarySeedPole = "body-boundary-seed pole"
polarityTermLabel oppositeSeedPole = "opposite seed pole"
polarityTermLabel carryPole = "carry pole"
polarityTermLabel successorPole = "successor pole"
polarityTermLabel p31Plus0Plus1Pole = "31+0+1 pole"
polarityTermLabel seedCarryPole = "seed-carry pole"

data RelationKind : Set where
  contrastiveRelation : RelationKind
  enablingRelation : RelationKind
  returningRelation : RelationKind
  softeningRelation : RelationKind
  stabilizingRelation : RelationKind
  reversingRelation : RelationKind
  complementaryRelation : RelationKind
  constrainingRelation : RelationKind
  localBodyRelation : RelationKind
  boundaryCutRelation : RelationKind
  bodyBoundarySeedRelation : RelationKind
  oppositeSeedRelation : RelationKind
  carryRelation : RelationKind
  successorRelation : RelationKind
  p31Plus0Plus1Relation : RelationKind
  seedCarryRelation : RelationKind

relationKindLabel : RelationKind → String
relationKindLabel contrastiveRelation = "contrastive"
relationKindLabel enablingRelation = "enabling"
relationKindLabel returningRelation = "returning"
relationKindLabel softeningRelation = "softening"
relationKindLabel stabilizingRelation = "stabilizing"
relationKindLabel reversingRelation = "reversing"
relationKindLabel complementaryRelation = "complementary"
relationKindLabel constrainingRelation = "constraining"
relationKindLabel localBodyRelation = "local-body"
relationKindLabel boundaryCutRelation = "boundary-cut"
relationKindLabel bodyBoundarySeedRelation = "body-boundary-seed"
relationKindLabel oppositeSeedRelation = "opposite-seed"
relationKindLabel carryRelation = "carry"
relationKindLabel successorRelation = "successor"
relationKindLabel p31Plus0Plus1Relation = "31+0+1"
relationKindLabel seedCarryRelation = "seed-carry"

relationKindToTaoRelation : RelationKind → Tao.TaoRelation
relationKindToTaoRelation contrastiveRelation =
  Tao.contrastsWith
relationKindToTaoRelation enablingRelation =
  Tao.enablesUse
relationKindToTaoRelation returningRelation =
  Tao.returnsTo
relationKindToTaoRelation softeningRelation =
  Tao.functionsAs
relationKindToTaoRelation stabilizingRelation =
  Tao.selfOrders
relationKindToTaoRelation reversingRelation =
  Tao.overcomes
relationKindToTaoRelation complementaryRelation =
  Tao.alignsWith
relationKindToTaoRelation constrainingRelation =
  Tao.reduces
relationKindToTaoRelation localBodyRelation =
  Tao.associatedWith
relationKindToTaoRelation boundaryCutRelation =
  Tao.reduces
relationKindToTaoRelation bodyBoundarySeedRelation =
  Tao.coArisesWith
relationKindToTaoRelation oppositeSeedRelation =
  Tao.contrastsWith
relationKindToTaoRelation carryRelation =
  Tao.follows
relationKindToTaoRelation successorRelation =
  Tao.selfOrders
relationKindToTaoRelation p31Plus0Plus1Relation =
  Tao.resolves
relationKindToTaoRelation seedCarryRelation =
  Tao.enablesUse

data TransitionKind : Set where
  yinToYangTransition : TransitionKind
  yangToYinTransition : TransitionKind
  yinToBalanceTransition : TransitionKind
  yangToBalanceTransition : TransitionKind
  balanceToYinTransition : TransitionKind
  balanceToYangTransition : TransitionKind
  thresholdCrossingTransition : TransitionKind
  returnTransition : TransitionKind
  softeningTransition : TransitionKind
  reversalTransition : TransitionKind
  localBodyTransition : TransitionKind
  boundaryCutTransition : TransitionKind
  bodyBoundarySeedTransition : TransitionKind
  oppositeSeedTransition : TransitionKind
  carryTransition : TransitionKind
  successorTransition : TransitionKind
  p31Plus0Plus1Transition : TransitionKind
  seedCarryTransition : TransitionKind

transitionKindLabel : TransitionKind → String
transitionKindLabel yinToYangTransition = "yin-to-yang"
transitionKindLabel yangToYinTransition = "yang-to-yin"
transitionKindLabel yinToBalanceTransition = "yin-to-balance"
transitionKindLabel yangToBalanceTransition = "yang-to-balance"
transitionKindLabel balanceToYinTransition = "balance-to-yin"
transitionKindLabel balanceToYangTransition = "balance-to-yang"
transitionKindLabel thresholdCrossingTransition = "threshold-crossing"
transitionKindLabel returnTransition = "return"
transitionKindLabel softeningTransition = "softening"
transitionKindLabel reversalTransition = "reversal"
transitionKindLabel localBodyTransition = "local-body"
transitionKindLabel boundaryCutTransition = "boundary-cut"
transitionKindLabel bodyBoundarySeedTransition = "body-boundary-seed"
transitionKindLabel oppositeSeedTransition = "opposite-seed"
transitionKindLabel carryTransition = "carry"
transitionKindLabel successorTransition = "successor"
transitionKindLabel p31Plus0Plus1Transition = "31+0+1"
transitionKindLabel seedCarryTransition = "seed-carry"

data YinYangAuthorityBit : Set where
  empiricalAuthorityBit : YinYangAuthorityBit
  spiritualAuthorityBit : YinYangAuthorityBit
  mysticalAuthorityBit : YinYangAuthorityBit
  clinicalAuthorityBit : YinYangAuthorityBit
  politicalAuthorityBit : YinYangAuthorityBit
  metaphysicalAuthorityBit : YinYangAuthorityBit
  canonicalTextAuthorityBit : YinYangAuthorityBit
  promotedDoctrineBit : YinYangAuthorityBit
  candidateOnlyBit : YinYangAuthorityBit
  promotedBit : YinYangAuthorityBit
  taoPromotesQiBit : YinYangAuthorityBit
  qiPromotesTaoBit : YinYangAuthorityBit

record YinYangAuthorityBits : Set where
  constructor yinYangAuthorityBits
  field
    empiricalAuthority : Bool
    spiritualAuthority : Bool
    mysticalAuthority : Bool
    clinicalAuthority : Bool
    politicalAuthority : Bool
    metaphysicalAuthority : Bool
    canonicalTextAuthority : Bool
    promotedDoctrine : Bool
    candidateOnly : Bool
    promoted : Bool
    taoPromotesQi : Bool
    qiPromotesTao : Bool

open YinYangAuthorityBits public

canonicalYinYangAuthorityBits : YinYangAuthorityBits
canonicalYinYangAuthorityBits =
  yinYangAuthorityBits
    false
    false
    false
    false
    false
    false
    false
    false
    true
    false
    false
    false

record YinYangAuthorityFailClosed : Set where
  constructor yinYangAuthorityFailClosed
  field
    empiricalAuthorityFalse :
      empiricalAuthority canonicalYinYangAuthorityBits ≡ false
    spiritualAuthorityFalse :
      spiritualAuthority canonicalYinYangAuthorityBits ≡ false
    mysticalAuthorityFalse :
      mysticalAuthority canonicalYinYangAuthorityBits ≡ false
    clinicalAuthorityFalse :
      clinicalAuthority canonicalYinYangAuthorityBits ≡ false
    politicalAuthorityFalse :
      politicalAuthority canonicalYinYangAuthorityBits ≡ false
    metaphysicalAuthorityFalse :
      metaphysicalAuthority canonicalYinYangAuthorityBits ≡ false
    canonicalTextAuthorityFalse :
      canonicalTextAuthority canonicalYinYangAuthorityBits ≡ false
    promotedDoctrineFalse :
      promotedDoctrine canonicalYinYangAuthorityBits ≡ false
    candidateOnlyTrue :
      candidateOnly canonicalYinYangAuthorityBits ≡ true
    promotedFalse :
      promoted canonicalYinYangAuthorityBits ≡ false
    taoPromotesQiFalse :
      taoPromotesQi canonicalYinYangAuthorityBits ≡ false
    qiPromotesTaoFalse :
      qiPromotesTao canonicalYinYangAuthorityBits ≡ false

canonicalYinYangAuthorityFailClosed : YinYangAuthorityFailClosed
canonicalYinYangAuthorityFailClosed =
  yinYangAuthorityFailClosed
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

record YinYangPolarityBoundaryRow : Set where
  constructor yinYangPolarityBoundaryRow
  field
    rowId : Nat
    taoOperatorFamily : TaoGrammar.TaoOperatorFamily
    taoMotif : Tao.TaoMotif
    taoReadingKind : Tao.TaoReadingKind
    taoQualifier : Tao.TaoQualifier
    taoAssertionStrength : Tao.AssertionStrength
    taoRelation : Tao.TaoRelation
    polarityTerm : PolarityTerm
    relationKind : RelationKind
    transitionKind : TransitionKind
    qiRoleCategory : QiTheory.QiRoleCategory
    qiFormalLensReading : QiTheory.QiFormalLensReading
    candidateOnly : Bool
    promoted : Bool
    authorityBits : YinYangAuthorityBits
    reading : String

open YinYangPolarityBoundaryRow public

record YinYangPolarityBoundaryRowReceipt (row : YinYangPolarityBoundaryRow) : Set where
  constructor yinYangPolarityBoundaryRowReceipt
  field
    candidateOnlyTrue :
      candidateOnly row ≡ true
    promotedFalse :
      promoted row ≡ false
    reading :
      String

open YinYangPolarityBoundaryRowReceipt public

mkYinYangPolarityBoundaryRow :
  Nat →
  TaoGrammar.TaoOperatorFamily →
  Tao.TaoMotif →
  Tao.TaoReadingKind →
  Tao.TaoQualifier →
  Tao.AssertionStrength →
  RelationKind →
  TransitionKind →
  PolarityTerm →
  QiTheory.QiRoleCategory →
  QiTheory.QiFormalLensReading →
  String →
  YinYangPolarityBoundaryRow
mkYinYangPolarityBoundaryRow rowId family motif readingKind qualifier strength relationKind
  transitionKind polarityTerm qiRole qiLens reading =
  yinYangPolarityBoundaryRow
    rowId
    family
    motif
    readingKind
    qualifier
    strength
    (relationKindToTaoRelation relationKind)
    polarityTerm
    relationKind
    transitionKind
    qiRole
    qiLens
    true
    false
    canonicalYinYangAuthorityBits
    reading

canonicalPolarityTerms : List PolarityTerm
canonicalPolarityTerms =
  yinPole
  ∷ yangPole
  ∷ balancedMiddle
  ∷ thresholdPole
  ∷ returnPole
  ∷ reversalPole
  ∷ softnessPole
  ∷ stillnessPole
  ∷ emptinessPole
  ∷ complementPole
  ∷ localBodyPole
  ∷ boundaryCutPole
  ∷ bodyBoundarySeedPole
  ∷ oppositeSeedPole
  ∷ carryPole
  ∷ successorPole
  ∷ p31Plus0Plus1Pole
  ∷ seedCarryPole
  ∷ []

canonicalPolarityTermCount : Nat
canonicalPolarityTermCount =
  listCount canonicalPolarityTerms

canonicalRelationKinds : List RelationKind
canonicalRelationKinds =
  contrastiveRelation
  ∷ enablingRelation
  ∷ returningRelation
  ∷ softeningRelation
  ∷ stabilizingRelation
  ∷ reversingRelation
  ∷ complementaryRelation
  ∷ constrainingRelation
  ∷ localBodyRelation
  ∷ boundaryCutRelation
  ∷ bodyBoundarySeedRelation
  ∷ oppositeSeedRelation
  ∷ carryRelation
  ∷ successorRelation
  ∷ p31Plus0Plus1Relation
  ∷ seedCarryRelation
  ∷ []

canonicalRelationKindCount : Nat
canonicalRelationKindCount =
  listCount canonicalRelationKinds

canonicalTransitionKinds : List TransitionKind
canonicalTransitionKinds =
  yinToYangTransition
  ∷ yangToYinTransition
  ∷ yinToBalanceTransition
  ∷ yangToBalanceTransition
  ∷ balanceToYinTransition
  ∷ balanceToYangTransition
  ∷ thresholdCrossingTransition
  ∷ returnTransition
  ∷ softeningTransition
  ∷ reversalTransition
  ∷ localBodyTransition
  ∷ boundaryCutTransition
  ∷ bodyBoundarySeedTransition
  ∷ oppositeSeedTransition
  ∷ carryTransition
  ∷ successorTransition
  ∷ p31Plus0Plus1Transition
  ∷ seedCarryTransition
  ∷ []

canonicalTransitionKindCount : Nat
canonicalTransitionKindCount =
  listCount canonicalTransitionKinds

canonicalYinYangPolarityBoundaryRows : List YinYangPolarityBoundaryRow
canonicalYinYangPolarityBoundaryRows =
  mkYinYangPolarityBoundaryRow
    zero
    TaoGrammar.ApophaticBoundaryOperator
    Tao.dao
    Tao.ApophaticBoundary
    Tao.candidateOnlyQualifier
    Tao.NegativeBoundary
    contrastiveRelation
    thresholdCrossingTransition
    yinPole
    QiTheory.QiBoundaryGate
    QiTheory.qiCategoryReading
    "Apophatic boundary keeps the Dao and the named frame in contrast as a candidate-only yin threshold row."
  ∷ mkYinYangPolarityBoundaryRow
    (suc zero)
    TaoGrammar.UseThroughEmptinessOperator
    Tao.emptiness
    Tao.EmptinessUtilityGrammar
    Tao.translationDependentQualifier
    Tao.CandidateAnalogy
    enablingRelation
    yinToBalanceTransition
    emptinessPole
    QiTheory.QiOperator
    QiTheory.qiOperatorReading
    "Use-through-emptiness keeps absence as a candidate bridge from Tao emptiness into Qi operator grammar."
  ∷ mkYinYangPolarityBoundaryRow
    (suc (suc zero))
    TaoGrammar.NonActionGovernanceOperator
    Tao.nonAction
    Tao.NonActionGovernance
    Tao.candidateOnlyQualifier
    Tao.PracticeGrammar
    stabilizingRelation
    yinToBalanceTransition
    stillnessPole
    QiTheory.QiBoundaryGate
    QiTheory.qiGradientFlowReading
    "Non-action governance stabilizes the boundary and keeps stillness as a candidate gate rather than a doctrine."
  ∷ mkYinYangPolarityBoundaryRow
    (suc (suc (suc zero)))
    TaoGrammar.SoftOverHardOperator
    Tao.water
    Tao.SoftOverHardOperator
    Tao.translationDependentQualifier
    Tao.PracticeGrammar
    softeningRelation
    softeningTransition
    softnessPole
    QiTheory.QiOperator
    QiTheory.qiGradientFlowReading
    "Soft-over-hard follows water as a softening candidate row for Qi operator and gradient-flow reading."
  ∷ mkYinYangPolarityBoundaryRow
    (suc (suc (suc (suc zero))))
    TaoGrammar.ReturnToRootOperator
    Tao.returnToRoot
    Tao.ReturnToRootGrammar
    Tao.candidateOnlyQualifier
    Tao.PracticeGrammar
    returningRelation
    returnTransition
    returnPole
    QiTheory.QiOperator
    QiTheory.qiOperatorReading
    "Return-to-root marks reversal as a candidate-only return transition between Tao grammar and Qi operator grammar."
  ∷ mkYinYangPolarityBoundaryRow
    (suc (suc (suc (suc (suc zero)))))
    TaoGrammar.AntiExcessOperator
    Tao.antiExcess
    Tao.AntiExcessGrammar
    Tao.candidateOnlyQualifier
    Tao.NegativeBoundary
    constrainingRelation
    thresholdCrossingTransition
    thresholdPole
    QiTheory.QiObstruction
    QiTheory.qiResistiveTransportReading
    "Anti-excess constrains surplus at the threshold and routes the reading through Qi obstruction grammar."
  ∷ mkYinYangPolarityBoundaryRow
    (suc (suc (suc (suc (suc (suc zero))))))
    TaoGrammar.AntiPossessionOperator
    Tao.nonPossession
    Tao.AntiPossessionEthic
    Tao.candidateOnlyQualifier
    Tao.NegativeBoundary
    complementaryRelation
    balanceToYangTransition
    complementPole
    QiTheory.QiDecomposition
    QiTheory.qiFunctionalReading
    "Anti-possession treats complementarity as a candidate decomposition row without promotion of authority."
  ∷ mkYinYangPolarityBoundaryRow
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
    TaoGrammar.ReversalOperator
    Tao.reversal
    Tao.ReversalGrammar
    Tao.translationDependentQualifier
    Tao.CandidateAnalogy
    reversingRelation
    reversalTransition
    reversalPole
    QiTheory.QiSpectrumTool
    QiTheory.qiSpectralReading
    "Reversal records the pivot from one pole to the other as a candidate-only spectral boundary row."
  ∷ mkYinYangPolarityBoundaryRow
    (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    TaoGrammar.ApophaticBoundaryOperator
    Tao.threshold
    Tao.ApophaticBoundary
    Tao.candidateOnlyQualifier
    Tao.NegativeBoundary
    bodyBoundarySeedRelation
    boundaryCutTransition
    bodyBoundarySeedPole
    QiTheory.QiBoundaryGate
    QiTheory.qiCategoryReading
    "Local body and boundary cut read together as a body-boundary-seed gate that stays candidate-only and fail-closed."
  ∷ mkYinYangPolarityBoundaryRow
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    TaoGrammar.UseThroughEmptinessOperator
    Tao.breath
    Tao.EmptinessUtilityGrammar
    Tao.candidateOnlyQualifier
    Tao.PracticeGrammar
    p31Plus0Plus1Relation
    successorTransition
    p31Plus0Plus1Pole
    QiTheory.QiOperator
    QiTheory.qiFunctionalReading
    "Recovered 31+0+1 keeps the opposite seed, carry, and successor in one candidate-only continuation grammar."
  ∷ []

canonicalYinYangPolarityBoundaryRowCount : Nat
canonicalYinYangPolarityBoundaryRowCount =
  listCount canonicalYinYangPolarityBoundaryRows

canonicalYinYangPolarityBoundaryRowReceipts : List (String)
canonicalYinYangPolarityBoundaryRowReceipts =
  "Apophatic boundary row receipt"
  ∷ "Use-through-emptiness row receipt"
  ∷ "Non-action governance row receipt"
  ∷ "Soft-over-hard row receipt"
  ∷ "Return-to-root row receipt"
  ∷ "Anti-excess row receipt"
  ∷ "Anti-possession row receipt"
  ∷ "Reversal row receipt"
  ∷ "Body-boundary-seed / boundary-cut row receipt"
  ∷ "Recovered 31+0+1 carry-successor row receipt"
  ∷ []

canonicalYinYangSymbolGeometryBoundaryModuleName : String
canonicalYinYangSymbolGeometryBoundaryModuleName =
  "DASHI.Culture.YinYangSymbolGeometryBoundary"

canonicalYinYangSymbolGeometryBoundarySurfaceName : String
canonicalYinYangSymbolGeometryBoundarySurfaceName =
  "canonicalYinYangSymbolGeometryBoundaryReceipt"

canonicalYinYangSymbolGeometryBoundarySummary : String
canonicalYinYangSymbolGeometryBoundarySummary =
  "Candidate-only yin/yang symbol geometry support surface covering enclosing-circle, inner-circle, eye-dot, teardrop, and S-curve boundary readings."

record YinYangGeometrySupportReference : Set where
  constructor yinYangGeometrySupportReference
  field
    geometryBoundaryModuleName : String
    geometryBoundarySurfaceName : String
    candidateOnly : Bool
    candidateOnlyTrue : candidateOnly ≡ true
    promoted : Bool
    promotedFalse : promoted ≡ false
    geometryBoundarySummary : String

open YinYangGeometrySupportReference public

canonicalYinYangGeometrySupportReference : YinYangGeometrySupportReference
canonicalYinYangGeometrySupportReference =
  yinYangGeometrySupportReference
    canonicalYinYangSymbolGeometryBoundaryModuleName
    canonicalYinYangSymbolGeometryBoundarySurfaceName
    true
    refl
    false
    refl
    canonicalYinYangSymbolGeometryBoundarySummary

record YinYangPolarityBoundaryReceipt : Set where
  constructor yinYangPolarityBoundaryReceipt
  field
    status :
      YinYangPolarityBoundaryStatus
    polarityTerms :
      List PolarityTerm
    polarityTermsAreCanonical :
      polarityTerms ≡ canonicalPolarityTerms
    relationKinds :
      List RelationKind
    relationKindsAreCanonical :
      relationKinds ≡ canonicalRelationKinds
    transitionKinds :
      List TransitionKind
    transitionKindsAreCanonical :
      transitionKinds ≡ canonicalTransitionKinds
    taoOperatorFamilySpanCount :
      Nat
    taoOperatorFamilySpanCountMatchesTaoGrammar :
      taoOperatorFamilySpanCount
        ≡ TaoGrammar.canonicalTaoOperatorFamilyCount
    boundaryRows :
      List YinYangPolarityBoundaryRow
    boundaryRowsAreCanonical :
      boundaryRows ≡ canonicalYinYangPolarityBoundaryRows
    geometrySupportReference :
      YinYangGeometrySupportReference
    geometrySupportReferenceIsCanonical :
      geometrySupportReference ≡ canonicalYinYangGeometrySupportReference
    boundaryRowCount :
      Nat
    boundaryRowCountMatchesCanonical :
      boundaryRowCount ≡ canonicalYinYangPolarityBoundaryRowCount
    authorityBits :
      YinYangAuthorityBits
    authorityBitsAreCanonical :
      authorityBits ≡ canonicalYinYangAuthorityBits
    authorityFailClosed :
      YinYangAuthorityFailClosed
    authorityFailClosedIsCanonical :
      authorityFailClosed ≡ canonicalYinYangAuthorityFailClosed
    candidateOnly :
      Bool
    candidateOnlyTrue :
      candidateOnly ≡ true
    promoted :
      Bool
    promotedFalse :
      promoted ≡ false
    nonPromoting :
      Bool
    nonPromotingTrue :
      nonPromoting ≡ true
    boundarySummary :
      String

open YinYangPolarityBoundaryReceipt public

canonicalYinYangPolarityBoundaryReceipt :
  YinYangPolarityBoundaryReceipt
canonicalYinYangPolarityBoundaryReceipt =
  record
    { status =
        candidateOnlyNonPromotingBoundary
    ; polarityTerms =
        canonicalPolarityTerms
    ; polarityTermsAreCanonical =
        refl
    ; relationKinds =
        canonicalRelationKinds
    ; relationKindsAreCanonical =
        refl
    ; transitionKinds =
        canonicalTransitionKinds
    ; transitionKindsAreCanonical =
        refl
    ; taoOperatorFamilySpanCount =
        canonicalYinYangPolarityBoundaryRowCount
    ; taoOperatorFamilySpanCountMatchesTaoGrammar =
        refl
    ; boundaryRows =
        canonicalYinYangPolarityBoundaryRows
    ; boundaryRowsAreCanonical =
        refl
    ; geometrySupportReference =
        canonicalYinYangGeometrySupportReference
    ; geometrySupportReferenceIsCanonical =
        refl
    ; boundaryRowCount =
        canonicalYinYangPolarityBoundaryRowCount
    ; boundaryRowCountMatchesCanonical =
        refl
    ; authorityBits =
        canonicalYinYangAuthorityBits
    ; authorityBitsAreCanonical =
        refl
    ; authorityFailClosed =
        canonicalYinYangAuthorityFailClosed
    ; authorityFailClosedIsCanonical =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyTrue =
        refl
    ; promoted =
        false
    ; promotedFalse =
        refl
    ; nonPromoting =
        true
    ; nonPromotingTrue =
        refl
    ; boundarySummary =
        "Candidate-only yin/yang polarity boundary linking Tao operator grammar to Qi formal-lens/operator grammar with fail-closed authority bits, a first-class yin/yang symbol geometry support reference, and a deeper 31+0+1/body-boundary-seed/carry successor middle layer."
    }
