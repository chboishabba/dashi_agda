module DASHI.Physics.Closure.PillaiResonanceBoundaryReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

data PillaiResonanceBoundaryStatus : Set where
  option4KnownCatalanOpenPillaiNoNSPromotion :
    PillaiResonanceBoundaryStatus

data PillaiResonanceBoundaryEntry : Set where
  catalanMihailescuOneGapTheoremKnown :
    PillaiResonanceBoundaryEntry

  pillaiFiniteResonanceConjectureExternalOpen :
    PillaiResonanceBoundaryEntry

  finiteCrossBaseResonanceNotImported :
    PillaiResonanceBoundaryEntry

  vorticityLInfinityUseSpeculative :
    PillaiResonanceBoundaryEntry

  clayNavierStokesPromotionNotCloseable :
    PillaiResonanceBoundaryEntry

canonicalPillaiResonanceBoundaryEntries :
  List PillaiResonanceBoundaryEntry
canonicalPillaiResonanceBoundaryEntries =
  catalanMihailescuOneGapTheoremKnown
  ∷ pillaiFiniteResonanceConjectureExternalOpen
  ∷ finiteCrossBaseResonanceNotImported
  ∷ vorticityLInfinityUseSpeculative
  ∷ clayNavierStokesPromotionNotCloseable
  ∷ []

pillaiResonanceBoundaryStatement : String
pillaiResonanceBoundaryStatement =
  "Option 4: Catalan-Mihailescu is recorded as the known one-gap theorem; Pillai finite-resonance remains external/open, so using it for vorticity L-infinity is speculative and not currently closeable."

record PillaiResonanceBoundaryReceipt : Setω where
  field
    status :
      PillaiResonanceBoundaryStatus

    boundaryEntries :
      List PillaiResonanceBoundaryEntry

    boundaryEntriesAreCanonical :
      boundaryEntries ≡ canonicalPillaiResonanceBoundaryEntries

    catalanMihailescuKnown :
      Bool

    catalanMihailescuKnownIsTrue :
      catalanMihailescuKnown ≡ true

    pillaiConjectureAvailable :
      Bool

    pillaiConjectureAvailableIsFalse :
      pillaiConjectureAvailable ≡ false

    finiteCrossBaseResonanceImported :
      Bool

    finiteCrossBaseResonanceImportedIsFalse :
      finiteCrossBaseResonanceImported ≡ false

    vorticityBoundFromNumberTheory :
      Bool

    vorticityBoundFromNumberTheoryIsFalse :
      vorticityBoundFromNumberTheory ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ pillaiResonanceBoundaryStatement

    receiptBoundary :
      List String

open PillaiResonanceBoundaryReceipt public

canonicalPillaiResonanceBoundaryReceipt :
  PillaiResonanceBoundaryReceipt
canonicalPillaiResonanceBoundaryReceipt =
  record
    { status =
        option4KnownCatalanOpenPillaiNoNSPromotion
    ; boundaryEntries =
        canonicalPillaiResonanceBoundaryEntries
    ; boundaryEntriesAreCanonical =
        refl
    ; catalanMihailescuKnown =
        true
    ; catalanMihailescuKnownIsTrue =
        refl
    ; pillaiConjectureAvailable =
        false
    ; pillaiConjectureAvailableIsFalse =
        refl
    ; finiteCrossBaseResonanceImported =
        false
    ; finiteCrossBaseResonanceImportedIsFalse =
        refl
    ; vorticityBoundFromNumberTheory =
        false
    ; vorticityBoundFromNumberTheoryIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        pillaiResonanceBoundaryStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        pillaiResonanceBoundaryStatement ∷ []
    }
