{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVOriginalObserverVisibilityCausalOrderExact where

------------------------------------------------------------------------
-- P01 -> P02: SOURCE-SELECTED OPERATIONAL ACCESS PREORDER.
--
-- Derive all causal-access relations from the ORIGINAL observer
-- filtration's observable predicate History.visibleAt, not from a
-- synthetic Lorentz-signature tag, fixed ShiftArrow, or an imposed
-- entropy/MDL clock.
--
-- a <=_obs b iff every event accessible at a remains accessible at b.
-- From the source's actual three access levels:
--   initial <_obs intermediate <_obs terminal.
-- Inclusion is reflexive/transitive; each strict step has an ORIGINAL
-- witness event; reverse inclusions are impossible.
--
-- This proves an operational *information* partial-order chain, not a
-- spacetime causal cone: signal propagation, local dimension four,
-- metric principal symbol, hyperbolicity, clock units, causal
-- isotropy, physical observer preparation and continuum still OPEN.
--
-- Reuses original HistoryWeightFiltrationExact. No new order axiom,
-- postulate, reversal of microscopic action, or fabricated physical
-- Lorentzian carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as History
import DASHI.Physics.Foundations.TSFVOriginalHiddenHistoryFiltrationWeldExact as Original
import DASHI.Physics.Foundations.FiniteHistoryOrientationExact as Micro

-- The observable order is computed from the SOURCE-owned visibility
-- of actual event labels. It does not require arbitrary pre-order data.
_⊑obs_ : History.FiltrationLevel → History.FiltrationLevel → Set
a ⊑obs b =
  (event : History.Event) →
  History.visibleAt a event ≡ true →
  History.visibleAt b event ≡ true

observableAccessReflexive :
  (level : History.FiltrationLevel) → level ⊑obs level
observableAccessReflexive level event witnessed = witnessed

observableAccessTransitive :
  ∀ {a b c : History.FiltrationLevel} →
  a ⊑obs b → b ⊑obs c → a ⊑obs c
observableAccessTransitive ab bc event witnessed =
  bc event (ab event witnessed)

initialAccessPrecedesIntermediate :
  History.initialFiltration ⊑obs History.intermediateFiltration
initialAccessPrecedesIntermediate History.preparationEvent _ = refl
initialAccessPrecedesIntermediate History.intermediateEvent ()
initialAccessPrecedesIntermediate History.terminalEvent ()

intermediateAccessPrecedesTerminal :
  History.intermediateFiltration ⊑obs History.terminalFiltration
intermediateAccessPrecedesTerminal History.preparationEvent _ = refl
intermediateAccessPrecedesTerminal History.intermediateEvent _ = refl
intermediateAccessPrecedesTerminal History.terminalEvent ()

initialAccessPrecedesTerminal :
  History.initialFiltration ⊑obs History.terminalFiltration
initialAccessPrecedesTerminal =
  observableAccessTransitive
    initialAccessPrecedesIntermediate
    intermediateAccessPrecedesTerminal

-- The strict part of the actually selected filtration means there is
-- some event newly accessible later, not a chosen temporal coordinate.
StrictlyAddsOriginalEvent :
  History.FiltrationLevel → History.FiltrationLevel → Set
StrictlyAddsOriginalEvent earlier later =
  Σ History.Event
    (λ event →
      History.visibleAt earlier event ≡ false
      × History.visibleAt later event ≡ true)

initialIntermediateActualStrictGain :
  StrictlyAddsOriginalEvent
    History.initialFiltration History.intermediateFiltration
initialIntermediateActualStrictGain =
  History.intermediateEvent , (refl , refl)

intermediateTerminalActualStrictGain :
  StrictlyAddsOriginalEvent
    History.intermediateFiltration History.terminalFiltration
intermediateTerminalActualStrictGain =
  History.terminalEvent , (refl , refl)

initialTerminalActualStrictGain :
  StrictlyAddsOriginalEvent
    History.initialFiltration History.terminalFiltration
initialTerminalActualStrictGain =
  History.terminalEvent , (refl , refl)

-- Strict operational precedence is asymmetric on the actual selected
-- three-level source, unlike the reversible microscopic involution.
terminalDoesNotAccessPrecedeIntermediate :
  History.terminalFiltration ⊑obs History.intermediateFiltration → ⊥
terminalDoesNotAccessPrecedeIntermediate backwards
  with backwards History.terminalEvent refl
... | ()

intermediateDoesNotAccessPrecedeInitial :
  History.intermediateFiltration ⊑obs History.initialFiltration → ⊥
intermediateDoesNotAccessPrecedeInitial backwards
  with backwards History.intermediateEvent refl
... | ()

terminalDoesNotAccessPrecedeInitial :
  History.terminalFiltration ⊑obs History.initialFiltration → ⊥
terminalDoesNotAccessPrecedeInitial backwards
  with backwards History.terminalEvent refl
... | ()

-- Antisymmetry follows by exhausting the ORIGINAL finite levels.
-- It is therefore an actual partial order on the declared records;
-- causal *spacetime* order needs a separate selected physical map.
observableAccessAntisymmetric :
  ∀ a b →
  a ⊑obs b → b ⊑obs a → a ≡ b
observableAccessAntisymmetric
  History.initialFiltration History.initialFiltration _ _ = refl
observableAccessAntisymmetric
  History.initialFiltration History.intermediateFiltration _ ba =
    ⊥-elim (intermediateDoesNotAccessPrecedeInitial ba)
observableAccessAntisymmetric
  History.initialFiltration History.terminalFiltration _ ba =
    ⊥-elim (terminalDoesNotAccessPrecedeInitial ba)
observableAccessAntisymmetric
  History.intermediateFiltration History.initialFiltration ab _ =
    ⊥-elim (intermediateDoesNotAccessPrecedeInitial ab)
observableAccessAntisymmetric
  History.intermediateFiltration History.intermediateFiltration _ _ = refl
observableAccessAntisymmetric
  History.intermediateFiltration History.terminalFiltration _ ba =
    ⊥-elim (terminalDoesNotAccessPrecedeIntermediate ba)
observableAccessAntisymmetric
  History.terminalFiltration History.initialFiltration ab _ =
    ⊥-elim (terminalDoesNotAccessPrecedeInitial ab)
observableAccessAntisymmetric
  History.terminalFiltration History.intermediateFiltration ab _ =
    ⊥-elim (terminalDoesNotAccessPrecedeIntermediate ab)
observableAccessAntisymmetric
  History.terminalFiltration History.terminalFiltration _ _ = refl

-- Both ORIGINAL hidden histories share the earliest observable record
-- and differ at the latest source level. This is the actual operational
-- time-information relation the 4D physical causal cone must extend.
selectedEarlyHistoryIndistinguishability :
  Original.actualObserverRecord History.initialFiltration
    Micro.chooseMinusBoundary
  ≡
  Original.actualObserverRecord History.initialFiltration
    Micro.choosePlusBoundary
selectedEarlyHistoryIndistinguishability =
  Original.originalEarlyRecordsIndistinguishable
