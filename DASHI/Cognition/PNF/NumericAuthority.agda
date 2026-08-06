module DASHI.Cognition.PNF.NumericAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Identity strata.
--
-- Dense numeric ids are authority-local join keys. Stable digests are a
-- separate transfer/rebuild identity. Human labels are kept outside the hot
-- numeric carrier so hexadecimal or textual compatibility references cannot
-- accidentally become graph identity.
------------------------------------------------------------------------

record RunId : Set where
  constructor runId
  field runValue : Nat

record DocumentId : Set where
  constructor documentId
  field documentValue : Nat

record SentenceId : Set where
  constructor sentenceId
  field sentenceValue : Nat

record TokenId : Set where
  constructor tokenId
  field tokenValue : Nat

record SymbolId : Set where
  constructor symbolId
  field symbolValue : Nat

record MorphSetId : Set where
  constructor morphSetId
  field morphSetValue : Nat

record RegionId : Set where
  constructor regionId
  field regionValue : Nat

record InterfaceId : Set where
  constructor interfaceId
  field interfaceValue : Nat

record FactorId : Set where
  constructor factorId
  field factorValue : Nat

record ObjectId : Set where
  constructor objectId
  field objectValue : Nat

record DemandId : Set where
  constructor demandId
  field demandValue : Nat

data SymbolKind : Set where
  orthSymbol lemmaSymbol posSymbol tagSymbol dependencySymbol : SymbolKind
  morphFeatureSymbol morphValueSymbol entityTypeSymbol : SymbolKind
  factorTypeSymbol predicateSymbol roleSymbol residualTypeSymbol : SymbolKind
  objectKindSymbol : SymbolKind

record NumericScope : Set where
  constructor numericScope
  field
    run : RunId
    document : DocumentId

open NumericScope public

record NumericSymbol (Digest : Set) : Set where
  constructor numericSymbol
  field
    symbolKind : SymbolKind
    localSymbolId : SymbolId
    stableSymbolDigest : Digest

open NumericSymbol public

record RebuildCorrespondence {Digest : Set}
    (left right : NumericSymbol Digest) : Set where
  constructor rebuildCorrespondence
  field
    sameKind : symbolKind left ≡ symbolKind right
    sameDigest : stableSymbolDigest left ≡ stableSymbolDigest right

open RebuildCorrespondence public

record HumanReference : Set where
  constructor humanReference
  field humanText : String

open HumanReference public

data NumericLookupKey : Set where
  lexicalKey : SymbolId → NumericLookupKey
  typedPairKey : SymbolId → SymbolId → NumericLookupKey
  factorKey : SymbolId → SymbolId → NumericLookupKey
  demandKey : SymbolId → SymbolId → NumericLookupKey

record NumericIdentityBoundary : Set where
  constructor numericIdentityBoundary
  field
    hotPathCarriesHumanText : Bool
    hotPathCarriesHumanTextIsFalse : hotPathCarriesHumanText ≡ false
    localSurrogateGuaranteedStableAcrossRebuilds : Bool
    localSurrogateGuaranteedStableAcrossRebuildsIsFalse :
      localSurrogateGuaranteedStableAcrossRebuilds ≡ false
    stableDigestRequiredForTransferIdentity : Bool
    stableDigestRequiredForTransferIdentityIsTrue :
      stableDigestRequiredForTransferIdentity ≡ true
    hexadecimalUsedForJoins : Bool
    hexadecimalUsedForJoinsIsFalse : hexadecimalUsedForJoins ≡ false

canonicalNumericIdentityBoundary : NumericIdentityBoundary
canonicalNumericIdentityBoundary =
  numericIdentityBoundary false refl false refl true refl false refl
