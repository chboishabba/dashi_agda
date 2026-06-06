module DASHI.Physics.Closure.YMSprint101ClayBoundaryReconciliationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMClayPromotionBoundary as Legacy
import DASHI.Physics.Closure.YMSprint100TerminalStateRollupReceipt as Sprint100

------------------------------------------------------------------------
-- Sprint 101 Clay boundary reconciliation.
--
-- The older YMClayPromotionBoundary is a legacy authority-boundary surface:
-- it remains fail-closed because that lane does not self-issue provider
-- derivations or external acceptance.
--
-- Sprint 100 is a newer receipt-layer rollup for the Sprint 91-99 candidate
-- chain: it records the internal candidate chain as complete in that receipt
-- layer, while still leaving external acceptance unavailable.
--
-- These are compatible because neither promotes Clay/YM.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

record ClayBoundaryReconciliation : Set₁ where
  constructor mkClayBoundaryReconciliation
  field
    sprint100Rollup :
      Sprint100.YMSprint100TerminalStateRollupReceipt
    legacyPromotionBoundary :
      Legacy.ClayPromotionBoundary
    sprint100InternalCandidateComplete :
      Sprint100.internalCandidateChainCompleteInRepo ≡ true
    sprint100ExternalAcceptanceUnavailable :
      Sprint100.externalAcceptanceTokenAvailable ≡ false
    legacyAllProvidersStillFalse :
      Legacy.allProvidersDerivedInRepo ≡ false
    legacyClayStatementBoundaryStillFalse :
      Legacy.clayStatementBoundaryDischarged ≡ false
    legacyNoClayPromotion :
      Legacy.clayYangMillsPromoted ≡ false
    sprint100NoClayPromotion :
      Sprint100.clayYangMillsPromoted ≡ false
    reconciledStatement :
      String
    noClayPromotion :
      clayYangMillsPromoted ≡ false

reconciledStatementCanonical : String
reconciledStatementCanonical =
  "Legacy authority boundary remains fail-closed; Sprint 91-100 candidate chain is complete only in the receipt layer; both keep clayYangMillsPromoted=false."

canonicalClayBoundaryReconciliation :
  ClayBoundaryReconciliation
canonicalClayBoundaryReconciliation =
  mkClayBoundaryReconciliation
    Sprint100.canonicalYMSprint100TerminalStateRollupReceipt
    Legacy.clayPromotionBoundary
    refl
    refl
    refl
    refl
    refl
    refl
    reconciledStatementCanonical
    refl

record YMSprint101ClayBoundaryReconciliationReceipt : Set₁ where
  field
    reconciliation :
      ClayBoundaryReconciliation
    legacyBoundaryStillFailClosed :
      Legacy.clayYangMillsPromoted ≡ false
    sprint100BoundaryStillFailClosed :
      Sprint100.clayYangMillsPromoted ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint101ClayBoundaryReconciliationReceipt :
  YMSprint101ClayBoundaryReconciliationReceipt
canonicalYMSprint101ClayBoundaryReconciliationReceipt =
  record
    { reconciliation =
        canonicalClayBoundaryReconciliation
    ; legacyBoundaryStillFailClosed =
        refl
    ; sprint100BoundaryStillFailClosed =
        refl
    ; noClayPromotion =
        refl
    }
