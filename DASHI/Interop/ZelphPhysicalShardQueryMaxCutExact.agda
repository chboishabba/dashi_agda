module DASHI.Interop.ZelphPhysicalShardQueryMaxCutExact where

-- Conditional mathematical maximum cut for Zelph physical shards.
-- No manifest bytes, Cap'n Proto correctness, live revisions or native
-- Wikibase statements are assumed to have been checked by this module.
-- The physical producers MUST instantiate the premises below.
--
-- Existing owners: prefix geometry (BalancedTernaryUltrametricExact),
-- query factorisation (QueryIndexedProjectionAdequacyExact),
-- source-indexed gluing (TypedHyperfabricCore), and coverage abstention
-- (ZelphBoundedGraphCoverageExact).  Do not invent a competing trie.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Fabric
import DASHI.Reasoning.TypedHyperfabricCore as Hyper
import DASHI.Foundations.BalancedTernaryUltrametricExact as Prefix
import DASHI.Interop.ZelphBoundedGraphCoverageExact as Coverage
import DASHI.Interop.ExternalContextSafetyBoundary as Safety

------------------------------------------------------------------------
-- A1. Explicit finite-domain physical partition: a declared key is
-- contained in its routed shard, and no other shard can claim that key.
-- This is a conditional theorem, NOT a receipt for actual HF bytes.
-- A non-unique name should instead use a multi-result fibre and must
-- not supply this singleton certificate.
------------------------------------------------------------------------

record NameShardPartition
    (Key Shard : Set)
    (route : Key → Shard)
    (contains : Key → Shard → Set) : Set₁ where
  field
    indexedCoverage : (key : Key) → contains key (route key)
    indexedExclusivity :
      (key : Key) (shard : Shard) →
      contains key shard → shard ≡ route key

open NameShardPartition public

zelphPhysicalNameShardPartitionExact :
  ∀ {Key Shard : Set}
    {route : Key → Shard}
    {contains : Key → Shard → Set} →
  NameShardPartition Key Shard route contains →
  (key : Key) →
  Σ Shard (λ shard →
    contains key shard ×
    ((other : Shard) → contains key other → other ≡ shard))
zelphPhysicalNameShardPartitionExact cert key =
  route key ,
  (indexedCoverage cert key ,
   indexedExclusivity cert key)

------------------------------------------------------------------------
-- A2. Query-family completeness is stronger than finding a name.
-- A graph answer is preserved only under a query-indexed closure
-- witness that equates the original answer to the selected view.
------------------------------------------------------------------------

record QueryFamilyClosure
    (Graph View Query Answer : Set)
    (select : Graph → View)
    (original : Query.QuerySemantics Graph Query Answer)
    (selected : Query.QuerySemantics View Query Answer)
    (InFamily : Query → Set) : Set₁ where
  field
    edgeClosure :
      (query : Query) → InFamily query → (graph : Graph) →
      Query.answer original query graph
      ≡ Query.answer selected query (select graph)

open QueryFamilyClosure public

zelphBoundedShardQueryFamilyCompleteness :
  ∀ {Graph View Query Answer : Set}
    {select : Graph → View}
    {original : Query.QuerySemantics Graph Query Answer}
    {selected : Query.QuerySemantics View Query Answer}
    {InFamily : Query → Set} →
  QueryFamilyClosure Graph View Query Answer select original selected InFamily →
  (query : Query) → InFamily query →
  Query.AdequateFor select original query
zelphBoundedShardQueryFamilyCompleteness
  {select = select} {original = original} {selected = selected}
  closure query within =
  Query.factorsForQuery
    {project = select}
    {semantics = original}
    {query = query}
    (Query.answer selected query)
    (edgeClosure closure query within)

-- The two worlds share a name shard while disagreeing about an edge.
-- Therefore a successful name route alone cannot prove A2.
data EdgeWorld : Set where edgeMissing edgePresent : EdgeWorld
data NameSurface : Set where sameNameShard : NameSurface
data EdgeResult : Set where noEdge hasEdge : EdgeResult

nameOnly : EdgeWorld → NameSurface
nameOnly _ = sameNameShard

edgeAnswer : EdgeWorld → EdgeResult
edgeAnswer edgeMissing = noEdge
edgeAnswer edgePresent = hasEdge

nameOnlyCollision : NF.NonFactorabilityWitness nameOnly edgeAnswer
nameOnlyCollision =
  NF.nonFactorabilityWitness edgeMissing edgePresent refl (λ ())

nameOnlyCannotCertifyAdjacency :
  NF.FactorsThrough nameOnly edgeAnswer → ⊥
nameOnlyCannotCertifyAdjacency =
  NF.witnessRulesOutEveryFlatFactorisation nameOnlyCollision

------------------------------------------------------------------------
-- A3. Reuse the original typed stalk/incidence carrier.  A claimed
-- global section requires each overlap equality; there is no gluing
-- from shared labels or equal QIDs alone.
------------------------------------------------------------------------

record CompatibleShardSections
    {Vertex Edge : Set}
    (fabric : Hyper.TypedHyperfabric Vertex Edge) : Set₁ where
  field
    localVertex : (vertex : Vertex) → Hyper.vertexStalk fabric vertex
    localEdge : (edge : Edge) → Hyper.edgeStalk fabric edge
    overlapAgreement :
      ∀ {vertex edge}
        (member : Hyper.incidence fabric vertex edge) →
      Hyper.restrict fabric member (localVertex vertex) ≡ localEdge edge
    sourceRevisionReceipt : String

open CompatibleShardSections public

zelphHyperformalShardGluingSound :
  ∀ {Vertex Edge : Set}
    {fabric : Hyper.TypedHyperfabric Vertex Edge} →
  CompatibleShardSections fabric → Hyper.GlobalSection fabric
zelphHyperformalShardGluingSound compat = record
  { vertexValue = localVertex compat
  ; edgeValue = localEdge compat
  ; compatible = overlapAgreement compat
  ; sectionReceipt = sourceRevisionReceipt compat
  }

-- No valid global section exists for a stalk model demanding two
-- unequal values of the same edge: the overlap premise is essential.
data OverlapValue : Set where oldValue newValue : OverlapValue
differentOverlap : oldValue ≡ newValue → ⊥
differentOverlap ()

conflictingOverlapsCannotGlue :
  (common : OverlapValue) →
  oldValue ≡ common → newValue ≡ common → ⊥
conflictingOverlapsCannotGlue common left right =
  differentOverlap (trans left (sym right))

------------------------------------------------------------------------
-- A4. Exact fibre-constancy criterion under an explicit representative
-- for each observed fibre.  This is the existing factorisation criterion
-- specialised to a physical projection, not a new metric theorem.
------------------------------------------------------------------------

FibreConstant :
  ∀ {State View Answer : Set} →
  (project : State → View) → (respond : State → Answer) → Set
FibreConstant {State = State} project respond =
  (left right : State) →
  project left ≡ project right → respond left ≡ respond right

zelphPrefixQuotientQueryAdequacyIffForward :
  ∀ {State View Answer : Set}
    {project : State → View} {respond : State → Answer} →
  NF.FactorsThrough project respond → FibreConstant project respond
zelphPrefixQuotientQueryAdequacyIffForward factor left right same =
  trans (NF.factorisation factor left)
    (trans (cong (NF.interpretFlat factor) same)
      (sym (NF.factorisation factor right)))

-- An explicitly supplied representative need only be a section on the
-- *image* of project.  It cannot be guessed from a manifest name.
zelphPrefixQuotientQueryAdequacyIffBackward :
  ∀ {State View Answer : Set}
    {project : State → View} {respond : State → Answer} →
  (representative : View → State) →
  ((state : State) →
    project (representative (project state)) ≡ project state) →
  FibreConstant project respond →
  NF.FactorsThrough project respond
zelphPrefixQuotientQueryAdequacyIffBackward
  {project = project} {respond = respond} representative onImage constant =
  NF.factorsThrough
    (λ view → respond (representative view))
    (λ state → constant state (representative (project state))
                  (sym (onImage state)))

nameOnlyIsNotAdequateForEdgeQuery :
  FibreConstant nameOnly edgeAnswer → ⊥
nameOnlyIsNotAdequateForEdgeQuery constant =
  differentOverlap-helper (constant edgeMissing edgePresent refl)
  where
  differentOverlap-helper : noEdge ≡ hasEdge → ⊥
  differentOverlap-helper ()

------------------------------------------------------------------------
-- A5. Revision/partition changes do not transport node IDs by default.
-- Only explicitly stable semantic fibres may be transported.
------------------------------------------------------------------------

record RevisionFibreTransport (Old New Key Value : Set)
    (oldValue : Old → Key → Value)
    (newValue : New → Key → Value)
    (rebase : Old → New)
    (Stable : Key → Set) : Set₁ where
  field
    sourceAndRevisionCorrespondence : String
    stableFibreCorrespondence :
      (old : Old) (key : Key) → Stable key →
      oldValue old key ≡ newValue (rebase old) key

open RevisionFibreTransport public

zelphRevisionRefinementTransportCoherent :
  ∀ {Old New Key Value : Set}
    {oldValue : Old → Key → Value}
    {newValue : New → Key → Value}
    {rebase : Old → New}
    {Stable : Key → Set} →
  RevisionFibreTransport Old New Key Value oldValue newValue rebase Stable →
  (old : Old) (key : Key) → Stable key →
  oldValue old key ≡ newValue (rebase old) key
zelphRevisionRefinementTransportCoherent cert old key stable =
  stableFibreCorrespondence cert old key stable

------------------------------------------------------------------------
-- A6. Only certified scoped negatives can be returned as scoped absence.
-- A missing or incomplete certificate produces 'unresolved', never a
-- Wikibase novalue assertion or a statement about all of Wikidata.
------------------------------------------------------------------------

data NegativeDisposition : Set where
  scopedAbsent unresolved : NegativeDisposition

record ScopedNegativeCertificate
    (World Query : Set)
    (originalMiss : World → Query → Bool)
    (viewMiss : World → Query → Bool)
    (InScope : Query → Set) : Set₁ where
  field
    checkedFamilyAndClosedWorldReference : String
    sameRevisionAndDecoderReference : String
    missingAnswerPreserved :
      (world : World) (query : Query) → InScope query →
      viewMiss world query ≡ true →
      originalMiss world query ≡ true
    missingAnswerReflected :
      (world : World) (query : Query) → InScope query →
      originalMiss world query ≡ true →
      viewMiss world query ≡ true

open ScopedNegativeCertificate public

zelphQueryScopedNegativeCompletenessIff :
  ∀ {World Query : Set}
    {originalMiss viewMiss : World → Query → Bool}
    {InScope : Query → Set} →
  ScopedNegativeCertificate World Query originalMiss viewMiss InScope →
  (world : World) (query : Query) → InScope query →
  viewMiss world query ≡ true →
  (viewMiss world query ≡ true → originalMiss world query ≡ true)
  ×
  (originalMiss world query ≡ true → viewMiss world query ≡ true)
zelphQueryScopedNegativeCompletenessIff cert world query within =
  missingAnswerPreserved cert world query within ,
  missingAnswerReflected cert world query within

data NegativeEvidence (Proof : Set) : Set where
  noCertificate : NegativeEvidence Proof
  withCertificate : Proof → NegativeEvidence Proof

negativeDisposition :
  ∀ {Proof : Set} → NegativeEvidence Proof → NegativeDisposition
negativeDisposition noCertificate = unresolved
negativeDisposition (withCertificate _) = scopedAbsent

uninspectedCannotGiveNegative :
  ∀ {Proof : Set} →
  negativeDisposition (noCertificate {Proof}) ≡ unresolved
uninspectedCannotGiveNegative = refl

-- Reused original prefix/coverage owners, not asserted HF layout facts.
prefixTransitivityReused :
  ∀ {n xs ys zs} →
  Prefix.PrefixAgreement n xs ys →
  Prefix.PrefixAgreement n ys zs →
  Prefix.PrefixAgreement n xs zs
prefixTransitivityReused = Prefix.prefixAgreementTransitive

uninspectedCoverageAbstentionReused :
  Safety.dispositionForCoverage
    (Coverage.safetyCoverage Coverage.queryCoverageUninspected)
  ≡ Safety.abstainForCoverage
uninspectedCoverageAbstentionReused =
  Coverage.uninspectedQueryCoverageAbstains
