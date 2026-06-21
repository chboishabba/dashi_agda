module DASHI.Culture.TaoOperatorGrammar where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Culture.TaoChapterReadingReceipt as TaoReceipt

------------------------------------------------------------------------
-- Tao operator grammar.
--
-- This module is candidate-only.  It consumes the chapter-reading receipt
-- surface and packages a set of operator families as blocked-authority
-- grammar rows with canonical receipts.  Nothing here promotes doctrinal,
-- empirical, clinical, political, metaphysical, or canonical authority.

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

five : Nat
five = suc four

six : Nat
six = suc five

seven : Nat
seven = suc six

data TaoOperatorFamily : Set where
  ApophaticBoundaryOperator : TaoOperatorFamily
  UseThroughEmptinessOperator : TaoOperatorFamily
  NonActionGovernanceOperator : TaoOperatorFamily
  SoftOverHardOperator : TaoOperatorFamily
  ReturnToRootOperator : TaoOperatorFamily
  AntiExcessOperator : TaoOperatorFamily
  AntiPossessionOperator : TaoOperatorFamily
  ReversalOperator : TaoOperatorFamily

operatorFamilyLabel : TaoOperatorFamily → String
operatorFamilyLabel ApophaticBoundaryOperator =
  "apophatic boundary"
operatorFamilyLabel UseThroughEmptinessOperator =
  "use through emptiness"
operatorFamilyLabel NonActionGovernanceOperator =
  "non-action governance"
operatorFamilyLabel SoftOverHardOperator =
  "soft over hard"
operatorFamilyLabel ReturnToRootOperator =
  "return to root"
operatorFamilyLabel AntiExcessOperator =
  "anti-excess"
operatorFamilyLabel AntiPossessionOperator =
  "anti-possession"
operatorFamilyLabel ReversalOperator =
  "reversal"

taoOperatorFamilyCount : List TaoOperatorFamily → Nat
taoOperatorFamilyCount [] =
  zero
taoOperatorFamilyCount (_ ∷ families) =
  suc (taoOperatorFamilyCount families)

canonicalTaoOperatorFamilies : List TaoOperatorFamily
canonicalTaoOperatorFamilies =
  ApophaticBoundaryOperator
  ∷ UseThroughEmptinessOperator
  ∷ NonActionGovernanceOperator
  ∷ SoftOverHardOperator
  ∷ ReturnToRootOperator
  ∷ AntiExcessOperator
  ∷ AntiPossessionOperator
  ∷ ReversalOperator
  ∷ []

canonicalTaoOperatorFamilyCount : Nat
canonicalTaoOperatorFamilyCount =
  taoOperatorFamilyCount canonicalTaoOperatorFamilies

record TaoOperatorRow : Set where
  constructor taoOperatorRow
  field
    operatorFamily : TaoOperatorFamily
    readingRow : TaoReceipt.TaoReadingRow
    blockedAuthority : Bool
    blockedAuthorityTrue : blockedAuthority ≡ true

open TaoOperatorRow public

record TaoOperatorReceipt : Set where
  constructor taoOperatorReceipt
  field
    operatorRow : TaoOperatorRow
    rowReceipt : TaoReceipt.TaoReadingRowReceipt (readingRow operatorRow)
    sourceReceipt : TaoReceipt.TaoSourceReceipt
    authorityBits : TaoReceipt.TaoAuthorityBits
    failClosed : TaoReceipt.TaoBoundaryFailClosed
    candidateOnly : Bool
    candidateOnlyTrue : candidateOnly ≡ true
    operatorSummary : String

open TaoOperatorReceipt public

record TaoOperatorGrammarReceipt : Set where
  constructor taoOperatorGrammarReceipt
  field
    sourceReceipt : TaoReceipt.TaoSourceReceipt
    chapterReceipt : TaoReceipt.TaoChapterReceipt
    operatorReceipts : List TaoOperatorReceipt
    operatorReceiptCount : Nat
    blockedAuthority : Bool
    blockedAuthorityTrue : blockedAuthority ≡ true
    candidateOnly : Bool
    candidateOnlyTrue : candidateOnly ≡ true
    authorityBits : TaoReceipt.TaoAuthorityBits
    failClosed : TaoReceipt.TaoBoundaryFailClosed
    grammarSummary : String

open TaoOperatorGrammarReceipt public

mkCanonicalTaoOperatorRow :
  TaoOperatorFamily →
  Nat →
  TaoReceipt.TaoChapterId →
  TaoReceipt.TaoReadingKind →
  TaoReceipt.TaoMotif →
  TaoReceipt.TaoRelation →
  TaoReceipt.TaoMotif →
  TaoReceipt.TaoQualifier →
  TaoReceipt.AssertionStrength →
  String →
  TaoOperatorRow
mkCanonicalTaoOperatorRow family rowId chapterId readingKind subject relation object qualifier strength reading =
  taoOperatorRow
    family
    (TaoReceipt.taoReadingRow
      rowId
      chapterId
      subject
      relation
      object
      qualifier
      readingKind
      strength
      false
      reading)
    true
    refl

mkCanonicalTaoOperatorReceipt :
  (operatorRow : TaoOperatorRow) →
  TaoReceipt.TaoReadingRowReceipt (readingRow operatorRow) →
  String →
  TaoOperatorReceipt
mkCanonicalTaoOperatorReceipt operatorRow rowReceipt summary =
  taoOperatorReceipt
    operatorRow
    rowReceipt
    TaoReceipt.canonicalTaoSourceReceipt
    TaoReceipt.canonicalTaoAuthorityBits
    TaoReceipt.canonicalTaoBoundaryFailClosed
    true
    refl
    summary

apophaticBoundaryOperatorReadingRow : TaoReceipt.TaoReadingRow
apophaticBoundaryOperatorReadingRow =
  TaoReceipt.taoReadingRow
    zero
    TaoReceipt.chapter1
    TaoReceipt.dao
    TaoReceipt.contrastsWith
    TaoReceipt.nameless
    TaoReceipt.translationDependentQualifier
    TaoReceipt.ApophaticBoundary
    TaoReceipt.NegativeBoundary
    false
    "Apophatic boundary operator: candidate-only reading that keeps the named Dao and the nameless Dao in contrast."

apophaticBoundaryOperatorRowReceipt :
  TaoReceipt.TaoReadingRowReceipt apophaticBoundaryOperatorReadingRow
apophaticBoundaryOperatorRowReceipt =
  TaoReceipt.taoReadingRowReceipt refl

apophaticBoundaryOperatorRow : TaoOperatorRow
apophaticBoundaryOperatorRow =
  taoOperatorRow
    ApophaticBoundaryOperator
    apophaticBoundaryOperatorReadingRow
    true
    refl

apophaticBoundaryOperatorReceipt : TaoOperatorReceipt
apophaticBoundaryOperatorReceipt =
  mkCanonicalTaoOperatorReceipt
    apophaticBoundaryOperatorRow
    apophaticBoundaryOperatorRowReceipt
    "Apophatic boundary is recorded only as a blocked-authority candidate row."

useThroughEmptinessOperatorReadingRow : TaoReceipt.TaoReadingRow
useThroughEmptinessOperatorReadingRow =
  TaoReceipt.taoReadingRow
    one
    TaoReceipt.chapter1
    TaoReceipt.emptiness
    TaoReceipt.enablesUse
    TaoReceipt.usefulnessThroughAbsence
    TaoReceipt.candidateOnlyQualifier
    TaoReceipt.NonBeingUsefulness
    TaoReceipt.CandidateAnalogy
    false
    "Use-through-emptiness operator: absence is carried as a candidate grammar for use."

useThroughEmptinessOperatorRowReceipt :
  TaoReceipt.TaoReadingRowReceipt useThroughEmptinessOperatorReadingRow
useThroughEmptinessOperatorRowReceipt =
  TaoReceipt.taoReadingRowReceipt refl

useThroughEmptinessOperatorRow : TaoOperatorRow
useThroughEmptinessOperatorRow =
  taoOperatorRow
    UseThroughEmptinessOperator
    useThroughEmptinessOperatorReadingRow
    true
    refl

useThroughEmptinessOperatorReceipt : TaoOperatorReceipt
useThroughEmptinessOperatorReceipt =
  mkCanonicalTaoOperatorReceipt
    useThroughEmptinessOperatorRow
    useThroughEmptinessOperatorRowReceipt
    "Use through emptiness is blocked-authority candidate grammar, not doctrine."

nonActionGovernanceOperatorReadingRow : TaoReceipt.TaoReadingRow
nonActionGovernanceOperatorReadingRow =
  TaoReceipt.taoReadingRow
    two
    TaoReceipt.chapter1
    TaoReceipt.nonAction
    TaoReceipt.practices
    TaoReceipt.spontaneousOrdering
    TaoReceipt.authorityBlockedQualifier
    TaoReceipt.NonActionGovernance
    TaoReceipt.PracticeGrammar
    false
    "Non-action governance operator: governance is sketched as non-action and spontaneous ordering."

nonActionGovernanceOperatorRowReceipt :
  TaoReceipt.TaoReadingRowReceipt nonActionGovernanceOperatorReadingRow
nonActionGovernanceOperatorRowReceipt =
  TaoReceipt.taoReadingRowReceipt refl

nonActionGovernanceOperatorRow : TaoOperatorRow
nonActionGovernanceOperatorRow =
  taoOperatorRow
    NonActionGovernanceOperator
    nonActionGovernanceOperatorReadingRow
    true
    refl

nonActionGovernanceOperatorReceipt : TaoOperatorReceipt
nonActionGovernanceOperatorReceipt =
  mkCanonicalTaoOperatorReceipt
    nonActionGovernanceOperatorRow
    nonActionGovernanceOperatorRowReceipt
    "Non-action governance remains candidate-only and blocked against authority promotion."

softOverHardOperatorReadingRow : TaoReceipt.TaoReadingRow
softOverHardOperatorReadingRow =
  TaoReceipt.taoReadingRow
    three
    TaoReceipt.chapter1
    TaoReceipt.softness
    TaoReceipt.overcomes
    TaoReceipt.uncarvedBlock
    TaoReceipt.metaphorOnlyQualifier
    TaoReceipt.SoftOverHardOperator
    TaoReceipt.ContrastiveReading
    false
    "Soft-over-hard operator: the soft side is recorded as a candidate contrast against rigidity."

softOverHardOperatorRowReceipt :
  TaoReceipt.TaoReadingRowReceipt softOverHardOperatorReadingRow
softOverHardOperatorRowReceipt =
  TaoReceipt.taoReadingRowReceipt refl

softOverHardOperatorRow : TaoOperatorRow
softOverHardOperatorRow =
  taoOperatorRow
    SoftOverHardOperator
    softOverHardOperatorReadingRow
    true
    refl

softOverHardOperatorReceipt : TaoOperatorReceipt
softOverHardOperatorReceipt =
  mkCanonicalTaoOperatorReceipt
    softOverHardOperatorRow
    softOverHardOperatorRowReceipt
    "Soft-over-hard is a formal candidate reading only."

returnToRootOperatorReadingRow : TaoReceipt.TaoReadingRow
returnToRootOperatorReadingRow =
  TaoReceipt.taoReadingRow
    four
    TaoReceipt.chapter1
    TaoReceipt.returnToRoot
    TaoReceipt.returnsTo
    TaoReceipt.dao
    TaoReceipt.accordingToDocstringReading
    TaoReceipt.ReturnToRootGrammar
    TaoReceipt.ConditionalAphorism
    false
    "Return-to-root operator: return is carried back to Dao as a candidate reading."

returnToRootOperatorRowReceipt :
  TaoReceipt.TaoReadingRowReceipt returnToRootOperatorReadingRow
returnToRootOperatorRowReceipt =
  TaoReceipt.taoReadingRowReceipt refl

returnToRootOperatorRow : TaoOperatorRow
returnToRootOperatorRow =
  taoOperatorRow
    ReturnToRootOperator
    returnToRootOperatorReadingRow
    true
    refl

returnToRootOperatorReceipt : TaoOperatorReceipt
returnToRootOperatorReceipt =
  mkCanonicalTaoOperatorReceipt
    returnToRootOperatorRow
    returnToRootOperatorRowReceipt
    "Return-to-root remains a candidate-only operator grammar row."

antiExcessOperatorReadingRow : TaoReceipt.TaoReadingRow
antiExcessOperatorReadingRow =
  TaoReceipt.taoReadingRow
    five
    TaoReceipt.chapter1
    TaoReceipt.antiExcess
    TaoReceipt.reduces
    TaoReceipt.desireReduction
    TaoReceipt.candidateOnlyQualifier
    TaoReceipt.AntiExcessGrammar
    TaoReceipt.PracticeGrammar
    false
    "Anti-excess operator: reduction of excess is recorded as a candidate practice row."

antiExcessOperatorRowReceipt :
  TaoReceipt.TaoReadingRowReceipt antiExcessOperatorReadingRow
antiExcessOperatorRowReceipt =
  TaoReceipt.taoReadingRowReceipt refl

antiExcessOperatorRow : TaoOperatorRow
antiExcessOperatorRow =
  taoOperatorRow
    AntiExcessOperator
    antiExcessOperatorReadingRow
    true
    refl

antiExcessOperatorReceipt : TaoOperatorReceipt
antiExcessOperatorReceipt =
  mkCanonicalTaoOperatorReceipt
    antiExcessOperatorRow
    antiExcessOperatorRowReceipt
    "Anti-excess is blocked-authority candidate grammar with no promoted command."

antiPossessionOperatorReadingRow : TaoReceipt.TaoReadingRow
antiPossessionOperatorReadingRow =
  TaoReceipt.taoReadingRow
    six
    TaoReceipt.chapter1
    TaoReceipt.nonPossession
    TaoReceipt.allowsWithoutPossessing
    TaoReceipt.worldAsVessel
    TaoReceipt.authorityBlockedQualifier
    TaoReceipt.AntiPossessionEthic
    TaoReceipt.PracticeGrammar
    false
    "Anti-possession operator: holding without owning is recorded as a candidate ethic."

antiPossessionOperatorRowReceipt :
  TaoReceipt.TaoReadingRowReceipt antiPossessionOperatorReadingRow
antiPossessionOperatorRowReceipt =
  TaoReceipt.taoReadingRowReceipt refl

antiPossessionOperatorRow : TaoOperatorRow
antiPossessionOperatorRow =
  taoOperatorRow
    AntiPossessionOperator
    antiPossessionOperatorReadingRow
    true
    refl

antiPossessionOperatorReceipt : TaoOperatorReceipt
antiPossessionOperatorReceipt =
  mkCanonicalTaoOperatorReceipt
    antiPossessionOperatorRow
    antiPossessionOperatorRowReceipt
    "Anti-possession stays candidate-only and blocked from authority promotion."

reversalOperatorReadingRow : TaoReceipt.TaoReadingRow
reversalOperatorReadingRow =
  TaoReceipt.taoReadingRow
    seven
    TaoReceipt.chapter1
    TaoReceipt.reversal
    TaoReceipt.resolves
    TaoReceipt.threshold
    TaoReceipt.metaphorOnlyQualifier
    TaoReceipt.ReversalGrammar
    TaoReceipt.CandidateAnalogy
    false
    "Reversal operator: turning at the threshold is held as a candidate analogy."

reversalOperatorRowReceipt :
  TaoReceipt.TaoReadingRowReceipt reversalOperatorReadingRow
reversalOperatorRowReceipt =
  TaoReceipt.taoReadingRowReceipt refl

reversalOperatorRow : TaoOperatorRow
reversalOperatorRow =
  taoOperatorRow
    ReversalOperator
    reversalOperatorReadingRow
    true
    refl

reversalOperatorReceipt : TaoOperatorReceipt
reversalOperatorReceipt =
  mkCanonicalTaoOperatorReceipt
    reversalOperatorRow
    reversalOperatorRowReceipt
    "Reversal is encoded as a blocked-authority candidate row."

canonicalTaoOperatorReceipts : List TaoOperatorReceipt
canonicalTaoOperatorReceipts =
  apophaticBoundaryOperatorReceipt
  ∷ useThroughEmptinessOperatorReceipt
  ∷ nonActionGovernanceOperatorReceipt
  ∷ softOverHardOperatorReceipt
  ∷ returnToRootOperatorReceipt
  ∷ antiExcessOperatorReceipt
  ∷ antiPossessionOperatorReceipt
  ∷ reversalOperatorReceipt
  ∷ []

taoOperatorReceiptCount : List TaoOperatorReceipt → Nat
taoOperatorReceiptCount [] =
  zero
taoOperatorReceiptCount (_ ∷ receipts) =
  suc (taoOperatorReceiptCount receipts)

canonicalTaoOperatorReceiptCount : Nat
canonicalTaoOperatorReceiptCount =
  taoOperatorReceiptCount canonicalTaoOperatorReceipts

canonicalTaoOperatorGrammarReceipt : TaoOperatorGrammarReceipt
canonicalTaoOperatorGrammarReceipt =
  taoOperatorGrammarReceipt
    TaoReceipt.canonicalTaoSourceReceipt
    TaoReceipt.chapter1Receipt
    canonicalTaoOperatorReceipts
    canonicalTaoOperatorReceiptCount
    true
    refl
    true
    refl
    TaoReceipt.canonicalTaoAuthorityBits
    TaoReceipt.canonicalTaoBoundaryFailClosed
    "Candidate-only Tao operator grammar over chapter 1 receipts; all operator rows are blocked-authority surfaces."
