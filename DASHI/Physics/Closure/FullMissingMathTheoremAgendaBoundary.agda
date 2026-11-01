module DASHI.Physics.Closure.FullMissingMathTheoremAgendaBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data AgendaStatus : Set where
  agendaOpen : AgendaStatus
  authorityIntake : AgendaStatus
  downstreamLocked : AgendaStatus

data TheoremId : Set where
  NS-A : TheoremId
  NS-B : TheoremId
  NS-C : TheoremId
  NS-D : TheoremId
  NS-E : TheoremId
  YM-A : TheoremId
  YM-B : TheoremId
  YM-C : TheoremId
  YM-D : TheoremId
  YM-E : TheoremId
  UCT-A : TheoremId
  UCT-B : TheoremId
  UCT-C : TheoremId
  UCT-D : TheoremId
  UCT-E : TheoremId
  UCT-F : TheoremId
  UCT-G : TheoremId
  UCT-H : TheoremId

record AgendaRow : Set where
  constructor mkAgendaRow
  field
    theoremId : TheoremId
    status : AgendaStatus
    openStatus : Bool
    authorityIntakeStatus : Bool
    downstreamLockedStatus : Bool
    promotionCandidate : Bool
    promoted : Bool

mkOpenRow : TheoremId → AgendaRow
mkOpenRow tid =
  mkAgendaRow tid agendaOpen true false false false false

mkAuthorityIntakeRow : TheoremId → AgendaRow
mkAuthorityIntakeRow tid =
  mkAgendaRow tid authorityIntake false true false false false

mkDownstreamLockedRow : TheoremId → AgendaRow
mkDownstreamLockedRow tid =
  mkAgendaRow tid downstreamLocked false false true false false

canonicalFullMissingMathTheoremAgenda : List AgendaRow
canonicalFullMissingMathTheoremAgenda =
  mkOpenRow NS-A
  ∷ mkOpenRow NS-B
  ∷ mkDownstreamLockedRow NS-C
  ∷ mkOpenRow NS-D
  ∷ mkDownstreamLockedRow NS-E
  ∷ mkOpenRow YM-A
  ∷ mkAuthorityIntakeRow YM-B
  ∷ mkDownstreamLockedRow YM-C
  ∷ mkDownstreamLockedRow YM-D
  ∷ mkOpenRow YM-E
  ∷ mkOpenRow UCT-A
  ∷ mkOpenRow UCT-B
  ∷ mkOpenRow UCT-C
  ∷ mkAuthorityIntakeRow UCT-D
  ∷ mkDownstreamLockedRow UCT-E
  ∷ mkDownstreamLockedRow UCT-F
  ∷ mkDownstreamLockedRow UCT-G
  ∷ mkDownstreamLockedRow UCT-H
  ∷ []

fullMissingMathTheoremAgendaCount : Nat
fullMissingMathTheoremAgendaCount =
  listLength canonicalFullMissingMathTheoremAgenda

fullMissingMathTheoremAgendaCountIs18 :
  fullMissingMathTheoremAgendaCount ≡ 18
fullMissingMathTheoremAgendaCountIs18 = refl

record DependencyFact : Set where
  constructor _dependsOn_
  field
    child : TheoremId
    parent : TheoremId

infix 4 _dependsOn_

canonicalFullMissingMathDependencyFacts : List DependencyFact
canonicalFullMissingMathDependencyFacts =
  (NS-C dependsOn NS-A)
  ∷ (NS-E dependsOn NS-A)
  ∷ (NS-E dependsOn NS-B)
  ∷ (NS-E dependsOn NS-C)
  ∷ (NS-E dependsOn NS-D)
  ∷ (YM-C dependsOn YM-B)
  ∷ (YM-D dependsOn YM-B)
  ∷ (UCT-E dependsOn UCT-D)
  ∷ (UCT-F dependsOn UCT-E)
  ∷ (UCT-G dependsOn UCT-F)
  ∷ (UCT-H dependsOn UCT-G)
  ∷ []

fullMissingMathDependencyFactCount : Nat
fullMissingMathDependencyFactCount =
  listLength canonicalFullMissingMathDependencyFacts

fullMissingMathDependencyFactCountIs11 :
  fullMissingMathDependencyFactCount ≡ 11
fullMissingMathDependencyFactCountIs11 = refl

NS-C-depends-on-NS-A : DependencyFact
NS-C-depends-on-NS-A = NS-C dependsOn NS-A

NS-E-depends-on-NS-A-through-NS-D : List DependencyFact
NS-E-depends-on-NS-A-through-NS-D =
  (NS-E dependsOn NS-A)
  ∷ (NS-E dependsOn NS-B)
  ∷ (NS-E dependsOn NS-C)
  ∷ (NS-E dependsOn NS-D)
  ∷ []

YM-C-depends-on-YM-B : DependencyFact
YM-C-depends-on-YM-B = YM-C dependsOn YM-B

YM-D-depends-on-YM-B : DependencyFact
YM-D-depends-on-YM-B = YM-D dependsOn YM-B

UCT-E-H-depend-on-UCT-D-chain : List DependencyFact
UCT-E-H-depend-on-UCT-D-chain =
  (UCT-E dependsOn UCT-D)
  ∷ (UCT-F dependsOn UCT-E)
  ∷ (UCT-G dependsOn UCT-F)
  ∷ (UCT-H dependsOn UCT-G)
  ∷ []

nsCDependsOnNSA : DependencyFact
nsCDependsOnNSA = NS-C-depends-on-NS-A

nsEDependsOnNSAToNSD : List DependencyFact
nsEDependsOnNSAToNSD = NS-E-depends-on-NS-A-through-NS-D

ymCDependsOnYMB : DependencyFact
ymCDependsOnYMB = YM-C-depends-on-YM-B

ymDDependsOnYMB : DependencyFact
ymDDependsOnYMB = YM-D-depends-on-YM-B

uctHDependsOnUCTDChain : List DependencyFact
uctHDependsOnUCTDChain = UCT-E-H-depend-on-UCT-D-chain

AbelTriadicDefectMeasureConstruction : String
AbelTriadicDefectMeasureConstruction =
  "NS-A AbelTriadicDefectMeasureConstruction"

HamiltonianDominatesDefectPlusHolonomy : String
HamiltonianDominatesDefectPlusHolonomy =
  "YM-A HamiltonianDominatesDefectPlusHolonomy"

H3aTraceNormTransfer : String
H3aTraceNormTransfer =
  "YM-B H3aTraceNormTransfer"

OverlapResidualPDE : String
OverlapResidualPDE =
  "UCT-A OverlapResidualPDE"

CrossTermNullity : String
CrossTermNullity =
  "UCT-D CrossTermNullity"

JordanVonNeumannRecovery : String
JordanVonNeumannRecovery =
  "UCT-H JordanVonNeumannRecovery"

fullMissingMathAgendaReceiptRecorded : Bool
fullMissingMathAgendaReceiptRecorded = true

failClosed : Bool
failClosed = true

promotionAllowed : Bool
promotionAllowed = false

clayPromotion : Bool
clayPromotion = false

terminalPromotion : Bool
terminalPromotion = false

nsPromotionFlag : Bool
nsPromotionFlag = false

ymPromotionFlag : Bool
ymPromotionFlag = false

uctPromotionFlag : Bool
uctPromotionFlag = false

anyTheoremPromotionFlag : Bool
anyTheoremPromotionFlag = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

unifiedClosureTheoremPromoted : Bool
unifiedClosureTheoremPromoted = false

fullMissingMathAgendaReceiptRecordedIsTrue :
  fullMissingMathAgendaReceiptRecorded ≡ true
fullMissingMathAgendaReceiptRecordedIsTrue = refl

failClosedIsTrue : failClosed ≡ true
failClosedIsTrue = refl

fullAgendaFailClosedIsTrue : failClosed ≡ true
fullAgendaFailClosedIsTrue = refl

promotionAllowedIsFalse : promotionAllowed ≡ false
promotionAllowedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

terminalPromotionIsFalse : terminalPromotion ≡ false
terminalPromotionIsFalse = refl

nsPromotionFlagIsFalse : nsPromotionFlag ≡ false
nsPromotionFlagIsFalse = refl

ymPromotionFlagIsFalse : ymPromotionFlag ≡ false
ymPromotionFlagIsFalse = refl

uctPromotionFlagIsFalse : uctPromotionFlag ≡ false
uctPromotionFlagIsFalse = refl

anyTheoremPromotionFlagIsFalse : anyTheoremPromotionFlag ≡ false
anyTheoremPromotionFlagIsFalse = refl

allPromotionFlagsFalse : Bool
allPromotionFlagsFalse = true

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse = refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

unifiedClosureTheoremPromotedIsFalse :
  unifiedClosureTheoremPromoted ≡ false
unifiedClosureTheoremPromotedIsFalse = refl

record FullMissingMathTheoremAgendaBoundary : Set where
  field
    agenda : List AgendaRow
    agendaIsCanonical :
      agenda ≡ canonicalFullMissingMathTheoremAgenda
    dependencyFacts : List DependencyFact
    dependencyFactsAreCanonical :
      dependencyFacts ≡ canonicalFullMissingMathDependencyFacts
    agendaCountIs18 :
      fullMissingMathTheoremAgendaCount ≡ 18
    dependencyFactCountIs11 :
      fullMissingMathDependencyFactCount ≡ 11
    receiptRecorded :
      fullMissingMathAgendaReceiptRecorded ≡ true
    failClosedGuard :
      failClosed ≡ true
    nsPromotionGuard :
      nsPromotionFlag ≡ false
    ymPromotionGuard :
      ymPromotionFlag ≡ false
    uctPromotionGuard :
      uctPromotionFlag ≡ false
    anyTheoremPromotionGuard :
      anyTheoremPromotionFlag ≡ false
    clayNavierStokesPromotionGuard :
      clayNavierStokesPromoted ≡ false
    clayYangMillsPromotionGuard :
      clayYangMillsPromoted ≡ false
    unifiedClosureTheoremPromotionGuard :
      unifiedClosureTheoremPromoted ≡ false

canonicalFullMissingMathTheoremAgendaBoundary :
  FullMissingMathTheoremAgendaBoundary
canonicalFullMissingMathTheoremAgendaBoundary =
  record
    { agenda = canonicalFullMissingMathTheoremAgenda
    ; agendaIsCanonical = refl
    ; dependencyFacts = canonicalFullMissingMathDependencyFacts
    ; dependencyFactsAreCanonical = refl
    ; agendaCountIs18 = refl
    ; dependencyFactCountIs11 = refl
    ; receiptRecorded = refl
    ; failClosedGuard = refl
    ; nsPromotionGuard = refl
    ; ymPromotionGuard = refl
    ; uctPromotionGuard = refl
    ; anyTheoremPromotionGuard = refl
    ; clayNavierStokesPromotionGuard = refl
    ; clayYangMillsPromotionGuard = refl
    ; unifiedClosureTheoremPromotionGuard = refl
    }

controlCardO : String
controlCardO =
  "O: Full missing math theorem agenda boundary receipt only."

controlCardR : String
controlCardR =
  "R: Record NS-A..NS-E, YM-A..YM-E, UCT-A..UCT-H without promotion."

controlCardC : String
controlCardC =
  "C: Builtin-only Agda receipt with exact dependency facts."

controlCardS : String
controlCardS =
  "S: Status fields are openStatus, authorityIntake, and downstreamLocked."

controlCardL : String
controlCardL =
  "L: Dependencies lock NS-C, NS-E, YM-C/YM-D, and UCT-E-H."

controlCardP : String
controlCardP =
  "P: failClosed true; all theorem promotion flags false."

controlCardG : String
controlCardG =
  "G: No proof, theorem discharge, or Clay promotion is claimed."

controlCardF : String
controlCardF =
  "F: Downstream work remains blocked until missing mathematics is supplied."
