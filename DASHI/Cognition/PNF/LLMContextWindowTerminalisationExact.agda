module DASHI.Cognition.PNF.LLMContextWindowTerminalisationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CONTEXT WINDOW AS A TERMINALISATION BOUNDARY
--
-- A finite active window may collapse histories that agree locally but differ
-- in an older coordinate needed by a later query.  External memory/provenance
-- can retain that omitted coordinate as a reopening residual.
------------------------------------------------------------------------

record History : Set where
  constructor history
  field
    remoteFact : Bool
    localFact : Bool

open History public

data Query : Set where
  askLocal askRemote : Query

observeHistory : Query → History → Bool
observeHistory askLocal h = localFact h
observeHistory askRemote h = remoteFact h

-- One-token toy window: only the local coordinate remains active.
activeWindow : History → Bool
activeWindow h = localFact h

historyLeft historyRight : History
historyLeft = history false true
historyRight = history true true

sameActiveWindow : activeWindow historyLeft ≡ activeWindow historyRight
sameActiveWindow = refl

remoteQueryDistinguishesHistories :
  observeHistory askRemote historyLeft ≡ observeHistory askRemote historyRight → ⊥
remoteQueryDistinguishesHistories ()

record ContextWindowTerminalisationWitness : Set where
  constructor contextWindowTerminalisationWitness
  field
    left right : History
    sameWindow : activeWindow left ≡ activeWindow right
    futureQuery : Query
    querySeparates :
      observeHistory futureQuery left ≡ observeHistory futureQuery right → ⊥

open ContextWindowTerminalisationWitness public

canonicalContextWindowTerminalisation : ContextWindowTerminalisationWitness
canonicalContextWindowTerminalisation =
  contextWindowTerminalisationWitness
    historyLeft historyRight refl askRemote remoteQueryDistinguishesHistories

------------------------------------------------------------------------
-- External residual / reopening.
------------------------------------------------------------------------

remoteResidual : History → Bool
remoteResidual h = remoteFact h

reopenFromWindowAndResidual : Bool → Bool → History
reopenFromWindowAndResidual window residual = history residual window

reopenContextExact :
  (h : History) →
  reopenFromWindowAndResidual (activeWindow h) (remoteResidual h) ≡ h
reopenContextExact (history remote local) = refl

windowAndResidualDetermineHistory :
  {left right : History} →
  activeWindow left ≡ activeWindow right →
  remoteResidual left ≡ remoteResidual right →
  left ≡ right
windowAndResidualDetermineHistory {history remote local} {history .remote .local} refl refl = refl

------------------------------------------------------------------------
-- Retention and accessibility are type-separated: the remote residual can be
-- retained even while the active window does not expose it.
------------------------------------------------------------------------

data Accessibility : Set where
  accessible inaccessible : Accessibility

remoteAccessibilityInWindow : History → Accessibility
remoteAccessibilityInWindow h = inaccessible

retainedRemoteMayBeInaccessible :
  (h : History) → remoteAccessibilityInWindow h ≡ inaccessible
retainedRemoteMayBeInaccessible h = refl

-- No theorem turns `inaccessible` into absence/nonexistence.
