module DASHI.Cognition.WhitlamPineGapSovereigntyHistoricalBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Holt / Whitlam historical disambiguation and sovereignty boundary.
------------------------------------------------------------------------

record WhitlamPineGapBoundary : Set where
  constructor whitlam-pine-gap-boundary
  field
    holtGovernmentApprovedPineGapPaid : Bool
    holtMemorialSwimmingCentrePaid : Bool
    whitlamSuspiciousOfCIAAndPineGapPaid : Bool
    whitlamOrderedASIOCutCIATiesPaid : Bool
    whitlamOpposedExtensionOfForeignBasesPaid : Bool
    dismissalCoincidedWithPineGapCIACrisisPaid : Bool
    ciaCausedWhitlamDismissalEstablished : Bool
    whitlamSimplyAntiZionistEstablished : Bool
    whitlamAffirmedIsraeliSovereigntyPaid : Bool
    whitlamCondemnedIsraeliLebanonRaidPaid : Bool
open WhitlamPineGapBoundary public

canonicalWhitlamPineGapBoundary : WhitlamPineGapBoundary
canonicalWhitlamPineGapBoundary = whitlam-pine-gap-boundary
  true true true true true true false false true true

record HistoricalReceipt : Set where
  constructor historical-receipt
  field
    source : String
    boundedFinding : String
    relationPaid : Bool
open HistoricalReceipt public

holtReceipt : HistoricalReceipt
holtReceipt = historical-receipt
  "National Archives of Australia Harold Holt timeline"
  "Holt's government approved the US-associated Pine Gap facility in 1967. The later Harold Holt Memorial Swimming Centre commemorates Holt after his disappearance while swimming; the naming is historically real but does not evidence foul play."
  true

whitlamIntelligenceReceipt : HistoricalReceipt
whitlamIntelligenceReceipt = historical-receipt
  "ABC 2015 ASIO official-history reporting; ABC Expanse 2024/2025"
  "Whitlam was suspicious of the CIA/Pine Gap, ordered ASIO to cease CIA liaison, publicly opposed prolongation of foreign bases, and was dismissed amid a contemporaneous Pine Gap/CIA political crisis. Public records do not conclusively establish CIA causation of the dismissal."
  true

whitlamIsraelReceipt : HistoricalReceipt
whitlamIsraelReceipt = historical-receipt
  "Prime Ministerial transcripts 1973-1974"
  "Whitlam explicitly affirmed Israel's sovereignty and right to exist while also supporting a more independent Australian line and condemning particular Israeli military actions. 'Anti-Zionist' is therefore too coarse as a blanket historical label."
  true

data TemporalCoincidenceImpliesCIAOperationalCause : Set where
data MemorialIronyImpliesAssassination : Set where
data PolicyCriticismImpliesAntiZionistIdentity : Set where

timingDoesNotCreateCIAOperationalCause :
  TemporalCoincidenceImpliesCIAOperationalCause → ⊥
timingDoesNotCreateCIAOperationalCause ()

memorialIronyDoesNotCreateAssassination : MemorialIronyImpliesAssassination → ⊥
memorialIronyDoesNotCreateAssassination ()

criticismDoesNotCreateIdentityLabel : PolicyCriticismImpliesAntiZionistIdentity → ⊥
criticismDoesNotCreateIdentityLabel ()
