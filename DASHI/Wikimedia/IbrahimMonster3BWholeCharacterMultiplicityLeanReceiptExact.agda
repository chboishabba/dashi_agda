module DASHI.Wikimedia.IbrahimMonster3BWholeCharacterMultiplicityLeanReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- WHOLE-CHARACTER MULTIPLICITY LEAN SOURCE RECEIPT
--
-- This source-level tranche is intentionally weaker than the final isotypic
-- theorem.  It only records the two character-pairing consequences needed by
-- that theorem:
--
--   char(V) = n * char(H) -> dim Hom_G(H,V) = n,
--
-- and, for simple U not isomorphic to H,
--
--   char(V) = n * char(H) -> dim Hom_G(U,V) = 0.
--
-- Source presence is not kernel certification and does not identify any
-- Monster-specific carrier.  OEIS/dimension coincidences do not pay either
-- multiplicity statement.
------------------------------------------------------------------------

record WholeCharacterMultiplicityLeanReceipt : Set where
  constructor whole-character-multiplicity-lean-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    regressionPath : String
    targetMultiplicityTheorem : String
    otherSimpleZeroTheorem : String
    redCommit : String
    sourceCommit : String
    rootIntegrationCommit : String
open WholeCharacterMultiplicityLeanReceipt public

currentWholeCharacterMultiplicityLeanReceipt : WholeCharacterMultiplicityLeanReceipt
currentWholeCharacterMultiplicityLeanReceipt =
  whole-character-multiplicity-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/monster3b-multiplicity-nsmul-probe"
    "Synthesis/MonsterCharacterDetermination.lean"
    "Synthesis/MonsterWholeCharacterMultiplicityRegression.lean"
    "Synthesis.cast_finrank_hom_eq_nat_of_character_eq_nsmul"
    "Synthesis.cast_finrank_hom_other_eq_zero_of_character_eq_nsmul"
    "d59c0db2d185a2eb78298f7d420a2e8ebb5fcf06"
    "b5f0d228faef4cd402ec6e4613fb3f559cd7a52e"
    "15626714d134235f8d4fc5e991cfc9bcc9c22c67"

------------------------------------------------------------------------
-- WrongType / certification firewalls.
------------------------------------------------------------------------

data SourceCreatesKernelReceipt : Set where
data MultiplicityLemmasCreateIsotypicTheorem : Set where
data OEISCreatesMultiplicityTheorem : Set where

data DimensionIdentityCreatesMultiplicityTheorem : Set where

sourceDoesNotCreateKernelReceipt : SourceCreatesKernelReceipt -> ⊥
sourceDoesNotCreateKernelReceipt ()

multiplicityDoesNotCreateIsotypicTheorem :
  MultiplicityLemmasCreateIsotypicTheorem -> ⊥
multiplicityDoesNotCreateIsotypicTheorem ()

oeisDoesNotCreateMultiplicityTheorem : OEISCreatesMultiplicityTheorem -> ⊥
oeisDoesNotCreateMultiplicityTheorem ()

dimensionIdentityDoesNotCreateMultiplicityTheorem :
  DimensionIdentityCreatesMultiplicityTheorem -> ⊥
dimensionIdentityDoesNotCreateMultiplicityTheorem ()

record WholeCharacterMultiplicityLeanBoundary : Set where
  constructor whole-character-multiplicity-lean-boundary
  field
    sourceWritten : Bool
    targetMultiplicityLemmaWritten : Bool
    otherSimpleMultiplicityZeroLemmaWritten : Bool
    wholeCharacterIsotypicTheoremPaid : Bool
    leanKernelReceiptObserved : Bool
    agdaTransportObserved : Bool
    oeisCreatesMultiplicityTheorem : Bool
    dimensionIdentityCreatesMultiplicityTheorem : Bool
    nextResidual : String
open WholeCharacterMultiplicityLeanBoundary public

canonicalWholeCharacterMultiplicityLeanBoundary :
  WholeCharacterMultiplicityLeanBoundary
canonicalWholeCharacterMultiplicityLeanBoundary =
  whole-character-multiplicity-lean-boundary
    true true true
    false false false
    false false
    "Kernel-check the two generic repeated-character multiplicity lemmas. Then use the existing FDRep/group-algebra action and submodule adapters to prove only the remaining consumer theorem: every simple k[G]-submodule type of the semisimple restricted module is H_zeta. Multiplicity statements alone do not construct the isotypic equivalence, and 65610=90*729 or OEIS matches remain non-promoting."
