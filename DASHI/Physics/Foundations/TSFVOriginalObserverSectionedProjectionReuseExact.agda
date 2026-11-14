module DASHI.Physics.Foundations.TSFVOriginalObserverSectionedProjectionReuseExact where

------------------------------------------------------------------------
-- P01.L06-L10: REUSE the existing DASHI canonical
-- SectionedProjectionProvenanceBridgeExact instead of inventing a
-- second observer-quotient or conditional-expectation formalism.
--
-- Fine = ACTUAL original selected observer record (PastRecord,
--        TerminalAccess), coarse = ACTUAL original past record.
-- Projection forgets terminal access, and its canonical section
-- chooses the original inaccessible-terminal representative.
--
-- The original SectionedProjection owner reconstructs every
-- fibre-constant observable, including the actual early past record.
-- On the SAME original two-terminal histories, the later terminal
-- observable provably does NOT factor through this coarse map.
--
-- The missing fibre/residual coordinate is exactly the actual
-- selected late terminal readout, not a generic new observer label.
-- This module is NON-GOLDEN: original SectionedProjection imports
-- older non---safe owners. No Agda kernel acceptance is claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Prior
import DASHI.Physics.Foundations.FiniteHistoryOrientationExact as Micro
import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as History
import DASHI.Physics.Foundations.TSFVOriginalHiddenHistoryFiltrationWeldExact as Original

-- The canonical *existing* projection object, instantiated at the
-- actual records emitted by the chosen original histories and
-- original filtration. No alternate coarse carrier is substituted.
originalObserverPastProjection :
  Prior.SectionedProjection Original.ObserverRecord Micro.PastRecord
originalObserverPastProjection =
  record
    { Prior.SectionedProjection.project = proj₁
    ; Prior.SectionedProjection.representative =
        λ past → past , Original.notYetAccessible
    ; Prior.SectionedProjection.section = λ _ → refl
    }

-- Actual coarse information survives the quotient, hence is exactly
-- reconstructible by the existing section theorem.
originalPastObservableIsFibreConstant :
  Prior.FibreConstant
    (Prior.project originalObserverPastProjection)
    (Prior.pullbackObservable
      (Prior.project originalObserverPastProjection)
      (λ past → past))
originalPastObservableIsFibreConstant =
  Prior.pullbackObservableIsFibreConstant
    (Prior.project originalObserverPastProjection)
    (λ past → past)

originalPastReconstructedFromSection :
  ∀ record →
  Prior.pullbackObservable
    (Prior.project originalObserverPastProjection)
    (λ past → past)
    record
  ≡
  Prior.pullbackObservable
    (Prior.project originalObserverPastProjection)
    (Prior.representativeObservable originalObserverPastProjection
      (Prior.pullbackObservable
        (Prior.project originalObserverPastProjection)
        (λ past → past)))
    record
originalPastReconstructedFromSection record =
  Prior.fibreConstantObservableReconstructsFromSection
    originalObserverPastProjection
    (Prior.pullbackObservable
      (Prior.project originalObserverPastProjection)
      (λ past → past))
    originalPastObservableIsFibreConstant
    record

-- The actual later terminal readout is NOT fibre-constant on the
-- selected original records: both have the same past projection but
-- the original source distinguishes their terminal branch.
originalLateTerminalNotFibreConstant :
  Prior.FibreConstant
    (Prior.project originalObserverPastProjection)
    proj₂ →
  ⊥
originalLateTerminalNotFibreConstant constant with
  constant
    (Original.actualObserverRecord History.terminalFiltration
      Micro.chooseMinusBoundary)
    (Original.actualObserverRecord History.terminalFiltration
      Micro.choosePlusBoundary)
    refl
... | ()

-- No *arbitrary* function of just the actual early/past coarse record
-- can recover these two distinct original selected late terminal
-- observables. The fibre is proof-relevantly needed.
noLaterTerminalDecoderFromPast :
  (decode : Micro.PastRecord → Original.TerminalAccess) →
  ((choice : Micro.LaterChoice) →
    decode
      (proj₁
        (Original.actualObserverRecord
          History.terminalFiltration choice))
    ≡
    proj₂
      (Original.actualObserverRecord
        History.terminalFiltration choice)) →
  ⊥
noLaterTerminalDecoderFromPast decode correct with
  trans (sym (correct Micro.chooseMinusBoundary))
    (correct Micro.choosePlusBoundary)
... | ()

-- The old owner also provides ResidualReopening; the literal terminal
-- component is precisely the missing refinement needed for perfect
-- readout reconstruction. Construct the actual reopening.
originalObserverResidualReopening :
  Prior.ResidualReopening originalObserverPastProjection
originalObserverResidualReopening =
  record
    { Prior.ResidualReopening.Residual = Original.TerminalAccess
    ; Prior.ResidualReopening.residual = proj₂
    ; Prior.ResidualReopening.reopen = λ past terminal → past , terminal
    ; Prior.ResidualReopening.reopenExact = λ { (past , terminal) → refl }
    }
