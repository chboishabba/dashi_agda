{-# OPTIONS --safe #-}
module DASHI.Interop.SLRStructuralReceiptFirewallExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRPostgresWorldPersistenceExact as PG
import DASHI.Interop.SLRProtectedPNFFleetReductionExact as Fleet
import DASHI.Interop.SLRActorCriticPromotionExact as Critic
import DASHI.Interop.SLRSharedEvidenceReducerExact as Evidence
import DASHI.Interop.SLRProductionRoadmapParityExact as Roadmap

data StoreKind : Set where
  postgresCanonicalDSN : StoreKind
  sqliteLocal : StoreKind
  jsonLedger : StoreKind
  slrwStream : StoreKind
  unconfiguredPG : StoreKind

record StorageReceipt : Set where
  constructor storageReceipt
  field
    storeKind : StoreKind
    dsnConfigured : Bool

record StorageAdmissible (r : StorageReceipt) : Set where
  constructor storageAdmissible
  field
    canonical : StorageReceipt.storeKind r ≡ postgresCanonicalDSN
    configured : StorageReceipt.dsnConfigured r ≡ true

data ExtractorKind : Set where
  sensiblawSharedReducerOrSLRCompiler : ExtractorKind
  rawRegex : ExtractorKind
  regexAgdaDeclarationScrape : ExtractorKind

record ExtractionReceipt : Set where
  constructor extractionReceipt
  field extractorKind : ExtractorKind

record ExtractionAdmissible (r : ExtractionReceipt) : Set where
  constructor extractionAdmissible
  field checked : ExtractionReceipt.extractorKind r ≡ sensiblawSharedReducerOrSLRCompiler

data MatcherKind : Set where
  astExactSymbolAndType : MatcherKind
  sqlLikeProseSubstring : MatcherKind

record SymbolLinkReceipt : Set where
  constructor symbolLinkReceipt
  field matcherKind : MatcherKind

record SymbolLinkAdmissible (r : SymbolLinkReceipt) : Set where
  constructor symbolLinkAdmissible
  field checked : SymbolLinkReceipt.matcherKind r ≡ astExactSymbolAndType

data RouterKind : Set where
  pgPNFCostedParetoConductor : RouterKind
  hardcodedSlotTable : RouterKind
  alphabeticalFileSlice : RouterKind
  positionalRosterZip : RouterKind

record RoutingReceipt : Set where
  constructor routingReceipt
  field routerKind : RouterKind

record RoutingAdmissible (r : RoutingReceipt) : Set where
  constructor routingAdmissible
  field checked : RoutingReceipt.routerKind r ≡ pgPNFCostedParetoConductor

record CrossDomainJoinReceipt : Set where
  constructor crossDomainJoinReceipt
  field
    hasExplicitASTBridge : Bool
    hasCoboundaryNoTypedMeetWitness : Bool

record CrossDomainJoinAdmissible (r : CrossDomainJoinReceipt) : Set where
  constructor crossDomainJoinAdmissible
  field
    astBridge : CrossDomainJoinReceipt.hasExplicitASTBridge r ≡ true
    coboundary : CrossDomainJoinReceipt.hasCoboundaryNoTypedMeetWitness r ≡ true

record CoherenceGateReceipt : Set where
  constructor coherenceGateReceipt
  field
    noiseDetected : Bool
    dispatchPermitted : Bool

record CoherenceAdmissible (r : CoherenceGateReceipt) : Set where
  constructor coherenceAdmissible
  field
    noiseBlocksDispatch : CoherenceGateReceipt.noiseDetected r ≡ true →
                          CoherenceGateReceipt.dispatchPermitted r ≡ false

sqliteNoPath : (dsn : Bool) → StorageAdmissible (storageReceipt sqliteLocal dsn) → ⊥
sqliteNoPath dsn (storageAdmissible () _)

jsonNoPath : (dsn : Bool) → StorageAdmissible (storageReceipt jsonLedger dsn) → ⊥
jsonNoPath dsn (storageAdmissible () _)

slrwNoPath : (dsn : Bool) → StorageAdmissible (storageReceipt slrwStream dsn) → ⊥
slrwNoPath dsn (storageAdmissible () _)

unconfiguredPGNoPath : StorageAdmissible (storageReceipt unconfiguredPG false) → ⊥
unconfiguredPGNoPath (storageAdmissible () _)

canonicalPGNeedsDSN : StorageAdmissible (storageReceipt postgresCanonicalDSN false) → ⊥
canonicalPGNeedsDSN (storageAdmissible _ ())

rawRegexNoPath : ExtractionAdmissible (extractionReceipt rawRegex) → ⊥
rawRegexNoPath (extractionAdmissible ())

regexAgdaScrapeNoPath : ExtractionAdmissible (extractionReceipt regexAgdaDeclarationScrape) → ⊥
regexAgdaScrapeNoPath (extractionAdmissible ())

substringLikeNoPath : SymbolLinkAdmissible (symbolLinkReceipt sqlLikeProseSubstring) → ⊥
substringLikeNoPath (symbolLinkAdmissible ())

hardcodedSlotNoPath : RoutingAdmissible (routingReceipt hardcodedSlotTable) → ⊥
hardcodedSlotNoPath (routingAdmissible ())

alphabeticalSliceNoPath : RoutingAdmissible (routingReceipt alphabeticalFileSlice) → ⊥
alphabeticalSliceNoPath (routingAdmissible ())

positionalRosterNoPath : RoutingAdmissible (routingReceipt positionalRosterZip) → ⊥
positionalRosterNoPath (routingAdmissible ())

missingASTBridgeNoPath : (c : Bool) →
  CrossDomainJoinAdmissible (crossDomainJoinReceipt false c) → ⊥
missingASTBridgeNoPath c (crossDomainJoinAdmissible () _)

missingCoboundaryNoPath : (a : Bool) →
  CrossDomainJoinAdmissible (crossDomainJoinReceipt a false) → ⊥
missingCoboundaryNoPath a (crossDomainJoinAdmissible _ ())

passiveCoherenceNoPath :
  CoherenceAdmissible (coherenceGateReceipt true true) → ⊥
passiveCoherenceNoPath (coherenceAdmissible blocks) with blocks refl
... | ()
