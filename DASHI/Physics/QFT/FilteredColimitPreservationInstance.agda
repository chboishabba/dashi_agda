module DASHI.Physics.QFT.FilteredColimitPreservationInstance where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as AQFT

------------------------------------------------------------------------
-- Concrete filtered-colimit witness for Gate 1.
--
-- The repo exports a concrete colimit universality target on the AQFT
-- side, but it does not export an inhabited left-adjoint theorem or a
-- proof that the Gate 1 interpretation functor preserves filtered
-- colimits.  This module packages the exact concrete lemma that is in
-- scope and records the remaining theorem gap honestly.

record FilteredColimitPreservationInstance : Setω where
  field
    missingLeftAdjointTheoremName :
      String

    nearestConcreteLemmaName :
      String

    filteredColimitPreservationPromoted :
      Bool

    filteredColimitPreservationPromotedIsFalse :
      filteredColimitPreservationPromoted ≡ false

    boundary :
      List String

open FilteredColimitPreservationInstance public

canonicalConcreteFilteredColimitUniversalityTarget :
  AQFT.ColimitUniversalityReceiptTarget
canonicalConcreteFilteredColimitUniversalityTarget =
  AQFT.canonicalConcreteColimitUniversalityReceiptTarget

canonicalFilteredColimitPreservationInstance :
  FilteredColimitPreservationInstance
canonicalFilteredColimitPreservationInstance =
  record
    { missingLeftAdjointTheoremName =
        "missingLeftAdjointPreservesFilteredColimitsTheorem"
    ; nearestConcreteLemmaName =
        "AQFT.canonicalConcreteColimitUniversalityReceiptTarget"
    ; filteredColimitPreservationPromoted =
        false
    ; filteredColimitPreservationPromotedIsFalse =
        refl
    ; boundary =
        "The repo exports a concrete filtered-colimit universality target, not an inhabited Gate 1 left-adjoint theorem"
        ∷ "This module records the exact concrete lemma in scope and keeps the left-adjoint preservation claim unpromoted"
        ∷ "The missing theorem remains missingLeftAdjointPreservesFilteredColimitsTheorem"
        ∷ []
    }

canonicalFilteredColimitUniversalityTargetName :
  String
canonicalFilteredColimitUniversalityTargetName =
  nearestConcreteLemmaName
    canonicalFilteredColimitPreservationInstance

missingLeftAdjointTheoremExactName :
  String
missingLeftAdjointTheoremExactName =
  missingLeftAdjointTheoremName
    canonicalFilteredColimitPreservationInstance

filteredColimitPreservationInstanceStatus :
  Bool
filteredColimitPreservationInstanceStatus =
  filteredColimitPreservationPromoted
    canonicalFilteredColimitPreservationInstance

