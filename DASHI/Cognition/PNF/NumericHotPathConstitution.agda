module DASHI.Cognition.PNF.NumericHotPathConstitution where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- Numeric semantic hot-path constitution.
--
-- Once the parser has emitted numeric observations, ordinary semantic
-- execution is over numeric ids / finite numeric coordinates.  Human strings
-- remain boundary material.  Regex is allowed at ingestion/boundary adapters,
-- but has no semantic-authority constructor.
------------------------------------------------------------------------

data TextBoundaryReason : Set where
  ingestNormalization rawQuotation externalProtocol userVisibleRendering :
    TextBoundaryReason

record TextBoundaryException : Set where
  constructor textBoundaryException
  field
    reason : TextBoundaryReason
    boundaryText : String

open TextBoundaryException public

data RegexSemanticHotPathPermission : Set where

regexCannotEnterSemanticHotPath : RegexSemanticHotPathPermission → ⊥
regexCannotEnterSemanticHotPath ()

record NumericSemanticCoordinate : Set where
  constructor numericSemanticCoordinate
  field
    symbol : SymbolId
    token : TokenId
    region : RegionId

open NumericSemanticCoordinate public

------------------------------------------------------------------------
-- Numeric cue automata.
--
-- The concrete trie/DFA/Aho-Corasick implementation belongs to the runtime.
-- Agda records the contract that the input and matches are numeric and that an
-- implementation may only claim linear-plus-match work after supplying the
-- corresponding empirical/executable witness.
------------------------------------------------------------------------

record NumericAutomatonReceipt : Set where
  constructor numericAutomatonReceipt
  field
    inputSymbols : Nat
    matchCount : Nat
    workUnits : Nat
    workWithinLinearPlusMatches :
      workUnits ≤ᶜ (inputSymbols +ᶜ matchCount)

open NumericAutomatonReceipt public

record NumericCueAutomatonResult : Set where
  constructor numericCueAutomatonResult
  field
    consumed : List SymbolId
    matchedPatternIds : List Nat
    cost : NumericAutomatonReceipt

open NumericCueAutomatonResult public

------------------------------------------------------------------------
-- Boundary: numeric execution is the default.  Any text exception is explicit
-- and cannot itself establish semantic identity.
------------------------------------------------------------------------

data TextBoundaryIdentityPromotionPermission : Set where

textBoundaryCannotPromoteIdentity : TextBoundaryIdentityPromotionPermission → ⊥
textBoundaryCannotPromoteIdentity ()

record NumericHotPathBoundary : Set where
  constructor numericHotPathBoundary
  field
    postTokenSemanticCarrierNumeric : Bool
    postTokenSemanticCarrierNumericIsTrue :
      postTokenSemanticCarrierNumeric ≡ true
    regexCoreSemanticMechanism : Bool
    regexCoreSemanticMechanismIsFalse : regexCoreSemanticMechanism ≡ false
    textRequiresExplicitBoundaryReason : Bool
    textRequiresExplicitBoundaryReasonIsTrue :
      textRequiresExplicitBoundaryReason ≡ true
    numericAutomataPreferredForFiniteCueLanguages : Bool
    numericAutomataPreferredForFiniteCueLanguagesIsTrue :
      numericAutomataPreferredForFiniteCueLanguages ≡ true

open NumericHotPathBoundary public

canonicalNumericHotPathBoundary : NumericHotPathBoundary
canonicalNumericHotPathBoundary =
  numericHotPathBoundary true refl false refl true refl true refl
