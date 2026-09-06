module DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CROSS-PROVER RETURN: §38 ACTUAL-ZETA LOCAL COUNT INSTANCE
--
-- Lean owner:
--   Zeta23Bridge/Zeta23Bridge/NearCoreZetaLocalCountInstance.lean
--
-- Checked imported producer:
--   Zeta23.RvM.zetaZeroConfig_local_count
--
-- Mathematical source attribution carried by the Zeta23 local-count lane:
--   E. C. Titchmarsh, revised by D. R. Heath-Brown,
--   The Theory of the Riemann Zeta-Function, 2nd edition,
--   Theorem 9.2, Oxford University Press, ISBN 0-19-853369-1.
--
-- FIREWALL:
-- A checked imported Lean theorem is not an unproved authority receipt, but it
-- is also not an Agda proof.  This owner makes all three statuses distinct.
------------------------------------------------------------------------

data ZetaCountAuthority : Set where
  checkedImportedLeanTheorem unprovedAuthorityReceipt openAgdaTransport
    : ZetaCountAuthority

record ZetaLocalCountLeanReturn : Set where
  constructor zeta-local-count-lean-return
  field
    leanOwner : String
    importedLeanProducer : String
    sourceAuthor : String
    sourceTitle : String
    stableIdentifier : String
    theoremLocator : String
    authority : ZetaCountAuthority

    importedProducerCheckedInLean : Bool
    importedProducerCheckedInLeanIsTrue : importedProducerCheckedInLean ≡ true

    importedProducerIsUnprovedAuthorityReceipt : Bool
    importedProducerIsUnprovedAuthorityReceiptIsFalse :
      importedProducerIsUnprovedAuthorityReceipt ≡ false

    transportedIntoAgda : Bool
    transportedIntoAgdaIsFalse : transportedIntoAgda ≡ false

    zetaCriterionNeverOwnedInLean : Bool
    zetaCriterionNeverOwnedInLeanIsTrue : zetaCriterionNeverOwnedInLean ≡ true

    zetaShortWindowUpperCountOwnedInLean : Bool
    zetaShortWindowUpperCountOwnedInLeanIsTrue :
      zetaShortWindowUpperCountOwnedInLean ≡ true

    boundedCutoffZetaOwnedInLean : Bool
    boundedCutoffZetaOwnedInLeanIsTrue : boundedCutoffZetaOwnedInLean ≡ true

    quarterPeriodDensityForceZetaOwnedInLean : Bool
    quarterPeriodDensityForceZetaOwnedInLeanIsTrue :
      quarterPeriodDensityForceZetaOwnedInLean ≡ true

    zetaUpperCountingHypothesisStillOpen : Bool
    zetaUpperCountingHypothesisStillOpenIsFalse :
      zetaUpperCountingHypothesisStillOpen ≡ false

    zetaLongWindowLowerDensityClosed : Bool
    zetaLongWindowLowerDensityClosedIsFalse :
      zetaLongWindowLowerDensityClosed ≡ false

    actualZetaClusteringClosed : Bool
    actualZetaClusteringClosedIsFalse : actualZetaClusteringClosed ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    localCountReading : String
    shortWindowReading : String
    proofAuthorityReading : String
    openFrontierReading : String

open ZetaLocalCountLeanReturn public

canonicalZetaLocalCountLeanReturn : ZetaLocalCountLeanReturn
canonicalZetaLocalCountLeanReturn =
  zeta-local-count-lean-return
    "Zeta23Bridge.Zeta23Bridge.NearCoreZetaLocalCountInstance"
    "Zeta23.RvM.zetaZeroConfig_local_count"
    "E. C. Titchmarsh; revised by D. R. Heath-Brown"
    "The Theory of the Riemann Zeta-Function, 2nd edition"
    "ISBN 0-19-853369-1"
    "Theorem 9.2"
    checkedImportedLeanTheorem
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "The checked Lean producer supplies a constant A_zeta >= 1 with unit-window zero count N(t,t+1] <= A_zeta log(|t|+3) for the repository's actual zetaZeroConfig."
    "Lean covers the required interval by finitely many unit windows and derives N(t-D-1,t+D] <= (A_zeta log(|t|+D+4)) (2D+2); no stronger long-window density theorem is smuggled in."
    "checked imported theorem != unproved authority/Boolean receipt != Agda proof.  This distinction replaces the over-broad phrase 'no imported authority'."
    "The upper local-count hypothesis is discharged for zeta.  The long-window lower-density input and the genuine clustering inequality (4/pi^2) highGapMass < lowGapMass remain open; RH is not derived."
