{-# OPTIONS --safe #-}
module DASHI.Interop.SLRNoPathFirewallExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

-- These types are admissibility judgments, not claims that legacy files
-- or local diagnostic stores do not exist. A forbidden authority route
-- has no constructor, so it cannot produce an admissible witness.
data CanonicalAuthority : Set where
  reviewedPostgresWorld : CanonicalAuthority

data LegacyRoute : Set where
  sqliteRuntime : LegacyRoute
  jsonLedger : LegacyRoute
  slrwBagOfWords : LegacyRoute
  unconfiguredPostgres : LegacyRoute
  rawRegexPNF : LegacyRoute
  regexFormalInvariant : LegacyRoute
  substringLikeOwner : LegacyRoute
  hardcodedSlot : LegacyRoute
  alphabeticalSlice : LegacyRoute
  positionalRosterZip : LegacyRoute
  unwitnessedCrossDomainJoin : LegacyRoute
  passiveCoherenceDispatch : LegacyRoute

data AdmissibleRoute : LegacyRoute → Set where

SQLiteIsCanonicalRuntimeStore : Set
SQLiteIsCanonicalRuntimeStore = AdmissibleRoute sqliteRuntime

JSONLedgerIsCanonicalStateStore : Set
JSONLedgerIsCanonicalStateStore = AdmissibleRoute jsonLedger

SLRWBagOfWordsFileIsSemanticSource : Set
SLRWBagOfWordsFileIsSemanticSource = AdmissibleRoute slrwBagOfWords

UnconfiguredPGWithoutCanonicalSLRDSNAdmissible : Set
UnconfiguredPGWithoutCanonicalSLRDSNAdmissible = AdmissibleRoute unconfiguredPostgres

RawRegexConstructsSemanticTokenOrPNF : Set
RawRegexConstructsSemanticTokenOrPNF = AdmissibleRoute rawRegexPNF

RegexIdentifierScrapeConstructsFormalInvariant : Set
RegexIdentifierScrapeConstructsFormalInvariant = AdmissibleRoute regexFormalInvariant

SubstringSymbolLikeQueryConstructsFormalOwner : Set
SubstringSymbolLikeQueryConstructsFormalOwner = AdmissibleRoute substringLikeOwner

HardcodedSlotDomainTableSelectsModules : Set
HardcodedSlotDomainTableSelectsModules = AdmissibleRoute hardcodedSlot

AlphabeticalDirectorySliceConstructsProofTarget : Set
AlphabeticalDirectorySliceConstructsProofTarget = AdmissibleRoute alphabeticalSlice

PositionalRosterZipAssignsWorkerTopic : Set
PositionalRosterZipAssignsWorkerTopic = AdmissibleRoute positionalRosterZip

UnwitnessedCrossDomainJoinAdmissible : Set
UnwitnessedCrossDomainJoinAdmissible = AdmissibleRoute unwitnessedCrossDomainJoin

PassiveCoherenceFlagAllowsDispatch : Set
PassiveCoherenceFlagAllowsDispatch = AdmissibleRoute passiveCoherenceDispatch

SQLiteIsCanonicalRuntimeStore→⊥ : SQLiteIsCanonicalRuntimeStore → ⊥
SQLiteIsCanonicalRuntimeStore→⊥ ()

JSONLedgerIsCanonicalStateStore→⊥ : JSONLedgerIsCanonicalStateStore → ⊥
JSONLedgerIsCanonicalStateStore→⊥ ()

SLRWBagOfWordsFileIsSemanticSource→⊥ : SLRWBagOfWordsFileIsSemanticSource → ⊥
SLRWBagOfWordsFileIsSemanticSource→⊥ ()

UnconfiguredPGWithoutCanonicalSLRDSNAdmissible→⊥ : UnconfiguredPGWithoutCanonicalSLRDSNAdmissible → ⊥
UnconfiguredPGWithoutCanonicalSLRDSNAdmissible→⊥ ()

RawRegexConstructsSemanticTokenOrPNF→⊥ : RawRegexConstructsSemanticTokenOrPNF → ⊥
RawRegexConstructsSemanticTokenOrPNF→⊥ ()

RegexIdentifierScrapeConstructsFormalInvariant→⊥ : RegexIdentifierScrapeConstructsFormalInvariant → ⊥
RegexIdentifierScrapeConstructsFormalInvariant→⊥ ()

SubstringSymbolLikeQueryConstructsFormalOwner→⊥ : SubstringSymbolLikeQueryConstructsFormalOwner → ⊥
SubstringSymbolLikeQueryConstructsFormalOwner→⊥ ()

HardcodedSlotDomainTableSelectsModules→⊥ : HardcodedSlotDomainTableSelectsModules → ⊥
HardcodedSlotDomainTableSelectsModules→⊥ ()

AlphabeticalDirectorySliceConstructsProofTarget→⊥ : AlphabeticalDirectorySliceConstructsProofTarget → ⊥
AlphabeticalDirectorySliceConstructsProofTarget→⊥ ()

PositionalRosterZipAssignsWorkerTopic→⊥ : PositionalRosterZipAssignsWorkerTopic → ⊥
PositionalRosterZipAssignsWorkerTopic→⊥ ()

UnwitnessedCrossDomainJoinAdmissible→⊥ : UnwitnessedCrossDomainJoinAdmissible → ⊥
UnwitnessedCrossDomainJoinAdmissible→⊥ ()

PassiveCoherenceFlagAllowsDispatch→⊥ : PassiveCoherenceFlagAllowsDispatch → ⊥
PassiveCoherenceFlagAllowsDispatch→⊥ ()

-- A witness must be supplied by the reviewed PostgreSQL route.
data ReviewedWitness : CanonicalAuthority → Set where
  reviewed : ReviewedWitness reviewedPostgresWorld

canonicalWorldHasWitness : ReviewedWitness reviewedPostgresWorld
canonicalWorldHasWitness = reviewed
