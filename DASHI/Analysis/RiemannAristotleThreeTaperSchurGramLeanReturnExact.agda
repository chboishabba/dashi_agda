module DASHI.Analysis.RiemannAristotleThreeTaperSchurGramLeanReturnExact where

------------------------------------------------------------------------
-- KERNEL-CHECKED LEAN RETURN: THREE-TAPER SCHUR GRAM
--
-- Source report: Zeta23Bridge/ThreeTaperSchurGram.lean is wired into the
-- aggregate Zeta23Bridge build.  The supplied return reports 8885 successful
-- jobs and the standard axiom audit only.
--
-- This is provenance/status in Agda; it does not import Lean proof terms.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record ThreeTaperSchurGramLeanReturn : Set where
  constructor three-taper-schur-gram-lean-return
  field
    leanModule : String
    aggregateBuildJobs : String

    aggregateLeanBuildKernelChecked : Bool
    aggregateLeanBuildKernelCheckedIsTrue : aggregateLeanBuildKernelChecked ≡ true

    standardAxiomAuditOnly : Bool
    standardAxiomAuditOnlyIsTrue : standardAxiomAuditOnly ≡ true

    bilinearDeterminantIdentityKernelChecked : Bool
    bilinearDeterminantIdentityKernelCheckedIsTrue :
      bilinearDeterminantIdentityKernelChecked ≡ true

    finiteSignedGramLedgerKernelChecked : Bool
    finiteSignedGramLedgerKernelCheckedIsTrue :
      finiteSignedGramLedgerKernelChecked ≡ true

    scalarSquareOfSumEnergyIdentityKernelChecked : Bool
    scalarSquareOfSumEnergyIdentityKernelCheckedIsTrue :
      scalarSquareOfSumEnergyIdentityKernelChecked ≡ true

    scalarGramDebtIdentityKernelChecked : Bool
    scalarGramDebtIdentityKernelCheckedIsTrue :
      scalarGramDebtIdentityKernelChecked ≡ true

    equalCellPositiveDuplicateNoGoKernelChecked : Bool
    equalCellPositiveDuplicateNoGoKernelCheckedIsTrue :
      equalCellPositiveDuplicateNoGoKernelChecked ≡ true

    leanProofTransportedIntoAgda : Bool
    leanProofTransportedIntoAgdaIsFalse : leanProofTransportedIntoAgda ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

open ThreeTaperSchurGramLeanReturn public

canonicalThreeTaperSchurGramLeanReturn : ThreeTaperSchurGramLeanReturn
canonicalThreeTaperSchurGramLeanReturn =
  three-taper-schur-gram-lean-return
    "Zeta23Bridge/Zeta23Bridge/ThreeTaperSchurGram.lean"
    "8885"
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
