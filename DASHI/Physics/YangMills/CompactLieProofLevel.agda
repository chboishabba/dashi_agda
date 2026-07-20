module DASHI.Physics.YangMills.CompactLieProofLevel where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- A claim can be computationally closed, proved in Agda, imported from a
-- standard external theorem, conditional on explicit hypotheses, or remain a
-- frontier target.  Only the first two levels are locally promotable.
------------------------------------------------------------------------

data ProofLevel : Set where
  computed          : ProofLevel
  machineChecked    : ProofLevel
  standardImported  : ProofLevel
  conditional       : ProofLevel
  conjectural       : ProofLevel

promotable : ProofLevel → Bool
promotable computed         = true
promotable machineChecked   = true
promotable standardImported = false
promotable conditional      = false
promotable conjectural      = false

data Evidence (P : Set) : ProofLevel → Set where
  computedEvidence : P → Evidence P computed
  checkedEvidence  : P → Evidence P machineChecked
  importedEvidence : P → Evidence P standardImported
  conditionalEvidence : P → Evidence P conditional
  openTarget : Evidence P conjectural

record NamedClaim : Set₁ where
  constructor namedClaim
  field
    label : String
    Proposition : Set
    level : ProofLevel
    evidence : Evidence Proposition level

open NamedClaim public

computedPromotes : promotable computed ≡ true
computedPromotes = refl

machineCheckedPromotes : promotable machineChecked ≡ true
machineCheckedPromotes = refl

standardImportedDoesNotSelfPromote : promotable standardImported ≡ false
standardImportedDoesNotSelfPromote = refl

conditionalDoesNotSelfPromote : promotable conditional ≡ false
conditionalDoesNotSelfPromote = refl

conjecturalDoesNotPromote : promotable conjectural ≡ false
conjecturalDoesNotPromote = refl
