module DASHI.Interop.AristotleSchemaCoverageProfileBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact as Query
import DASHI.Interop.SensibLawWikidataRequiredPropertyCoverageExact as Coverage

-- Archive donor: RequestProject.Schemas. This owner records only the reusable
-- schema-scoped completeness pattern; it does not transport Lean proof terms.
record AristotleSchemaContract : Set where
  constructor aristotle-schema-contract
  field
    sourceModule : String
    declaration : String
    contractReference : String
open AristotleSchemaContract public

completeForContract : AristotleSchemaContract
completeForContract =
  aristotle-schema-contract
    "RequestProject.Schemas"
    "completeFor / conformsB_minShape theorem family"
    "schema conformity may certify completeness for the named finite query shape"

record CoverageSchemaReceipt : Set where
  constructor coverage-schema-receipt
  field
    schemaReference : String
    subjectReference : String
    queryReference : String
    conformsReference : String
    completeForQueryReference : String
    completeForNamedQuery : Bool
    completeForNamedQueryIsTrue : completeForNamedQuery ≡ true
    completeForEveryQuery : Bool
open CoverageSchemaReceipt public

data SchemaCompleteForOneQueryImpliesGlobalCompleteness : Set where
schemaCompletenessIsQueryScoped :
  SchemaCompleteForOneQueryImpliesGlobalCompleteness → ⊥
schemaCompletenessIsQueryScoped ()

record AristotleSchemaCoverageBoundary : Set where
  constructor aristotle-schema-coverage-boundary
  field
    namedSchemaMayReplaceAdHocPropertyList : Bool
    completenessIsConsumerIndexed : Bool
    oneQueryCompletenessIsGlobalCompleteness : Bool
    schemaConformityCreatesPromotionAuthority : Bool

canonicalAristotleSchemaCoverageBoundary : AristotleSchemaCoverageBoundary
canonicalAristotleSchemaCoverageBoundary =
  aristotle-schema-coverage-boundary true true false false

schemaCoverageStatement : String
schemaCoverageStatement =
  "A named finite Aristotle-style coverage schema can certify completeness for a declared query/consumer and replace ad-hoc required-property lists where the exact schema theorem is reconstructed. Such completeness remains query-scoped: complete-for-one-consumer is not whole-item or whole-Wikidata completeness and creates no promotion authority."
