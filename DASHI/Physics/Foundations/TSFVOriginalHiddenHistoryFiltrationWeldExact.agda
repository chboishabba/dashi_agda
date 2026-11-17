{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVOriginalHiddenHistoryFiltrationWeldExact where

------------------------------------------------------------------------
-- P01.L07-L10: ORIGINAL finite hidden-history choice -> ORIGINAL observer
-- visibility filtration. This is ONE selected finite history source,
-- not a parallel stand-in with freely assigned early and late records.
--
-- It consumes the *same* original Micro.pastAccessibleOutcome,
-- Micro.hiddenHistory and Micro.smoothedEstimate, and applies the
-- existing HistoryWeightFiltrationExact.visibleAt to decide when the
-- actual selected hidden terminal state becomes accessible.
--
-- Finite result:
-- * earlier observer receives the same past/hidden-terminal-inaccessible
--   record for both admissible later boundary choices;
-- * later observer can distinguish their original hidden terminal states;
-- * no decoder from early readout can recover both source histories;
-- * forgetting late readouts is a genuinely noninjective projection;
-- * the action of both actual selected histories is unchanged.
--
-- No claim of backwards intervention, true quantum class operators,
-- physical real clock, entropy law, emergent metric or OS Hamiltonian.
-- Original Aharonov--Bergmann--Lebowitz and original DASHI owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Foundations.FiniteHistoryOrientationExact as Micro
import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as Filtration

-- Nothing here manufactures an unrelated history carrier.
selectedFutureBoundary : Micro.LaterChoice → Micro.FutureBoundary
selectedFutureBoundary Micro.chooseMinusBoundary = Micro.futureMinus
selectedFutureBoundary Micro.choosePlusBoundary = Micro.futurePlus

actualSelectedSmoothing : Micro.LaterChoice → Micro.MicroState
actualSelectedSmoothing choice =
  Micro.smoothedEstimate (Micro.pastAccessibleOutcome choice)
    (selectedFutureBoundary choice)

-- The actual original two-boundary smoothing exactly picks the terminal
-- coordinate of the original selected hidden microscopic history.
smoothingIsOriginalHiddenTerminal :
  ∀ choice →
  actualSelectedSmoothing choice ≡ proj₂ (Micro.hiddenHistory choice)
smoothingIsOriginalHiddenTerminal Micro.chooseMinusBoundary = refl
smoothingIsOriginalHiddenTerminal Micro.choosePlusBoundary = refl

data TerminalAccess : Set where
  notYetAccessible : TerminalAccess
  observedMinus : TerminalAccess
  observedZero : TerminalAccess
  observedPlus : TerminalAccess

encodeSelectedTerminal : Micro.MicroState → TerminalAccess
encodeSelectedTerminal Micro.stateMinus = observedMinus
encodeSelectedTerminal Micro.stateZero = observedZero
encodeSelectedTerminal Micro.statePlus = observedPlus

-- The *original* visibility theorem decides when the selected source
-- hidden-state terminal may enter the observer's accessible algebra.
observedTerminal :
  Filtration.FiltrationLevel → Micro.LaterChoice → TerminalAccess
observedTerminal level choice with
  Filtration.visibleAt level Filtration.terminalEvent
... | false = notYetAccessible
... | true = encodeSelectedTerminal (actualSelectedSmoothing choice)

ObserverRecord : Set
ObserverRecord = Micro.PastRecord × TerminalAccess

actualObserverRecord :
  Filtration.FiltrationLevel → Micro.LaterChoice → ObserverRecord
actualObserverRecord level choice =
  Micro.pastAccessibleOutcome choice , observedTerminal level choice

originalEarlyRecordCannotSeeTerminal :
  ∀ choice →
  observedTerminal Filtration.initialFiltration choice
  ≡ notYetAccessible
originalEarlyRecordCannotSeeTerminal choice = refl

originalLateRecordReadsSameHiddenState :
  ∀ choice →
  observedTerminal Filtration.terminalFiltration choice
  ≡
  encodeSelectedTerminal (proj₂ (Micro.hiddenHistory choice))
originalLateRecordReadsSameHiddenState choice =
  cong encodeSelectedTerminal (smoothingIsOriginalHiddenTerminal choice)

-- The actual *pair* of selected past record and accessible terminal
-- data is observationally identical before the terminal visibility gate.
originalEarlyRecordsIndistinguishable :
  actualObserverRecord Filtration.initialFiltration
    Micro.chooseMinusBoundary
  ≡
  actualObserverRecord Filtration.initialFiltration
    Micro.choosePlusBoundary
originalEarlyRecordsIndistinguishable = refl

-- Once the *original* terminal event becomes visible, the two selected
-- histories have distinguishable terminal records.
originalLateMinusIsReadMinus :
  actualObserverRecord Filtration.terminalFiltration
    Micro.chooseMinusBoundary
  ≡ (Micro.recordQuiet , observedMinus)
originalLateMinusIsReadMinus = refl

originalLatePlusIsReadPlus :
  actualObserverRecord Filtration.terminalFiltration
    Micro.choosePlusBoundary
  ≡ (Micro.recordQuiet , observedPlus)
originalLatePlusIsReadPlus = refl

originalLateRecordsDiffer :
  actualObserverRecord Filtration.terminalFiltration
    Micro.chooseMinusBoundary
  ≡
  actualObserverRecord Filtration.terminalFiltration
    Micro.choosePlusBoundary →
  ⊥
originalLateRecordsDiffer ()

-- Exact operational noninvertibility on the SAME original chosen
-- histories. This is not a statement about entropy or the probability
-- of a macroscopic observer in an infinite quantum system.
noEarlyObserverHistoryDecoder :
  (decode : ObserverRecord → Micro.History2) →
  ((choice : Micro.LaterChoice) →
    decode (actualObserverRecord Filtration.initialFiltration choice)
    ≡ Micro.hiddenHistory choice) →
  ⊥
noEarlyObserverHistoryDecoder decode correct =
  Micro.futureBoundaryCanChangeHiddenHistory
    (trans (sym (correct Micro.chooseMinusBoundary))
      (trans (cong decode originalEarlyRecordsIndistinguishable)
        (correct Micro.choosePlusBoundary)))

forgetTerminalAccess : TerminalAccess → TerminalAccess
forgetTerminalAccess _ = notYetAccessible

forgetLateObserverRecord : ObserverRecord → ObserverRecord
forgetLateObserverRecord (past , terminal) =
  past , forgetTerminalAccess terminal

actualLateRecordsForgetToSameEarlyRecord :
  ∀ choice →
  forgetLateObserverRecord
    (actualObserverRecord Filtration.terminalFiltration choice)
  ≡ actualObserverRecord Filtration.initialFiltration choice
actualLateRecordsForgetToSameEarlyRecord
    Micro.chooseMinusBoundary = refl
actualLateRecordsForgetToSameEarlyRecord
    Micro.choosePlusBoundary = refl

forgettingLateRecordIsNotInjective :
  ((left right : ObserverRecord) →
    forgetLateObserverRecord left ≡ forgetLateObserverRecord right →
    left ≡ right) →
  ⊥
forgettingLateRecordIsNotInjective inject =
  originalLateRecordsDiffer
    (inject
      (actualObserverRecord Filtration.terminalFiltration
        Micro.chooseMinusBoundary)
      (actualObserverRecord Filtration.terminalFiltration
        Micro.choosePlusBoundary)
      refl)

-- Both selected physical *finite-source* histories have equal action
-- despite being distinct; do not infer which hidden history is selected
-- from a scalar action value or from the early accessible readout.
chosenHiddenHistoriesEqualAction :
  Micro.historyAction (Micro.hiddenHistory Micro.chooseMinusBoundary)
  ≡ Micro.historyAction (Micro.hiddenHistory Micro.choosePlusBoundary)
chosenHiddenHistoriesEqualAction = refl

-- NOTE: a noninvertible *forgetting map* does not itself prove that
-- physical forward-time dynamics is noninvertible. The real effective
-- observer semigroup and all-scale filtration must still be constructed.
