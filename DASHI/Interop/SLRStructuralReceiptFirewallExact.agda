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


-- These are links to the original mathematical owners, not new models.
postgresOwner : PG.PostgresWorldPersistenceBoundary
postgresOwner = PG.canonicalPostgresWorldPersistenceBoundary

fleetOwner : Set
fleetOwner = Fleet.SlotPartition

productionOwner : Roadmap.ProductionGoldenSplit
productionOwner = Roadmap.canonicalProductionGoldenSplit

-- Feature-set receipt gates. Each rejection is a constructor mismatch.
record SourceStoreDeliberationReceipt : Set where
  constructor sourceStoreDeliberationReceipt
  field
    ingest1CanonicalWikiSource : Bool
    atomicS29DeliberationSidecar : Bool
    k14ToK17ClosurePolicyWitness : Bool

record SourceStoreDeliberationAdmissible (r : SourceStoreDeliberationReceipt) : Set where
  constructor sourceStoreDeliberationAdmissible
  field
    ingest : SourceStoreDeliberationReceipt.ingest1CanonicalWikiSource r ≡ true
    sidecar : SourceStoreDeliberationReceipt.atomicS29DeliberationSidecar r ≡ true
    closure : SourceStoreDeliberationReceipt.k14ToK17ClosurePolicyWitness r ≡ true

missingIngest1NoPath : (s k : Bool) →
  SourceStoreDeliberationAdmissible (sourceStoreDeliberationReceipt false s k) → ⊥
missingIngest1NoPath s k (sourceStoreDeliberationAdmissible () _ _)

missingS29SidecarNoPath : (i k : Bool) →
  SourceStoreDeliberationAdmissible (sourceStoreDeliberationReceipt i false k) → ⊥
missingS29SidecarNoPath i k (sourceStoreDeliberationAdmissible _ () _)

missingK14K17WitnessNoPath : (i s : Bool) →
  SourceStoreDeliberationAdmissible (sourceStoreDeliberationReceipt i s false) → ⊥
missingK14K17WitnessNoPath i s (sourceStoreDeliberationAdmissible _ _ ())

record CFFISessionLifecycleReceipt : Set where
  constructor cffiSessionLifecycleReceipt
  field
    browserUsedInRefreshOrPrecommit : Bool
    staleCookieFailsClosed : Bool
    healthStoreClosedCleanly : Bool

record CFFISessionLifecycleAdmissible (r : CFFISessionLifecycleReceipt) : Set where
  constructor cffiSessionLifecycleAdmissible
  field
    headless : CFFISessionLifecycleReceipt.browserUsedInRefreshOrPrecommit r ≡ false
    stale : CFFISessionLifecycleReceipt.staleCookieFailsClosed r ≡ true
    closed : CFFISessionLifecycleReceipt.healthStoreClosedCleanly r ≡ true

browserRefreshFallbackNoPath : (s c : Bool) →
  CFFISessionLifecycleAdmissible (cffiSessionLifecycleReceipt true s c) → ⊥
browserRefreshFallbackNoPath s c (cffiSessionLifecycleAdmissible () _ _)

silentStaleSessionNoPath : (b c : Bool) →
  CFFISessionLifecycleAdmissible (cffiSessionLifecycleReceipt b false c) → ⊥
silentStaleSessionNoPath b c (cffiSessionLifecycleAdmissible _ () _)

unclosedAdapterHealthStoreNoPath : (b s : Bool) →
  CFFISessionLifecycleAdmissible (cffiSessionLifecycleReceipt b s false) → ⊥
unclosedAdapterHealthStoreNoPath b s (cffiSessionLifecycleAdmissible _ _ ())

record MultiParentRevivalReceipt : Set where
  constructor multiParentRevivalReceipt
  field
    parentCountInRange2To10 : Bool
    trimmedParentsDistinctAndNonEmpty : Bool
    requestIdAtMost128 : Bool
    validatedBeforeAdapterAndFilesystem : Bool
    retriedOnUncertainCommit : Bool

record MultiParentRevivalAdmissible (r : MultiParentRevivalReceipt) : Set where
  constructor multiParentRevivalAdmissible
  field
    count : MultiParentRevivalReceipt.parentCountInRange2To10 r ≡ true
    distinct : MultiParentRevivalReceipt.trimmedParentsDistinctAndNonEmpty r ≡ true
    request : MultiParentRevivalReceipt.requestIdAtMost128 r ≡ true
    early : MultiParentRevivalReceipt.validatedBeforeAdapterAndFilesystem r ≡ true
    noRetry : MultiParentRevivalReceipt.retriedOnUncertainCommit r ≡ false

invalidParentCountNoPath : (d r v u : Bool) →
  MultiParentRevivalAdmissible (multiParentRevivalReceipt false d r v u) → ⊥
invalidParentCountNoPath d r v u (multiParentRevivalAdmissible () _ _ _ _)

duplicateOrEmptyParentNoPath : (c r v u : Bool) →
  MultiParentRevivalAdmissible (multiParentRevivalReceipt c false r v u) → ⊥
duplicateOrEmptyParentNoPath c r v u (multiParentRevivalAdmissible _ () _ _ _)

oversizedRequestIdNoPath : (c d v u : Bool) →
  MultiParentRevivalAdmissible (multiParentRevivalReceipt c d false v u) → ⊥
oversizedRequestIdNoPath c d v u (multiParentRevivalAdmissible _ _ () _ _)

preGateAdapterTouchNoPath : (c d r u : Bool) →
  MultiParentRevivalAdmissible (multiParentRevivalReceipt c d r false u) → ⊥
preGateAdapterTouchNoPath c d r u (multiParentRevivalAdmissible _ _ _ () _)

uncertainCommitRetryNoPath : (c d r v : Bool) →
  MultiParentRevivalAdmissible (multiParentRevivalReceipt c d r v true) → ⊥
uncertainCommitRetryNoPath c d r v (multiParentRevivalAdmissible _ _ _ _ ())

record MacroPresetExpansionReceipt : Set where
  constructor macroPresetExpansionReceipt
  field
    hyphenNormalizedToUnderscore : Bool
    multiMacroLineFullyExpanded : Bool
    literalMacroTokenLeaked : Bool

record MacroPresetExpansionAdmissible (r : MacroPresetExpansionReceipt) : Set where
  constructor macroPresetExpansionAdmissible
  field
    normalized : MacroPresetExpansionReceipt.hyphenNormalizedToUnderscore r ≡ true
    expanded : MacroPresetExpansionReceipt.multiMacroLineFullyExpanded r ≡ true
    noLeak : MacroPresetExpansionReceipt.literalMacroTokenLeaked r ≡ false

unnormalizedHyphenMacroNoPath : (e l : Bool) →
  MacroPresetExpansionAdmissible (macroPresetExpansionReceipt false e l) → ⊥
unnormalizedHyphenMacroNoPath e l (macroPresetExpansionAdmissible () _ _)

incompleteMacroChainNoPath : (n l : Bool) →
  MacroPresetExpansionAdmissible (macroPresetExpansionReceipt n false l) → ⊥
incompleteMacroChainNoPath n l (macroPresetExpansionAdmissible _ () _)

leakedLiteralMacroTokenNoPath : (n e : Bool) →
  MacroPresetExpansionAdmissible (macroPresetExpansionReceipt n e true) → ⊥
leakedLiteralMacroTokenNoPath n e (macroPresetExpansionAdmissible _ _ ())
