module DASHI.Cognition.PNF.ParserArgumentSupportGluing where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Core.StructuralSupportEdge as SupportCore
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Foundations.StratifiedResolutionTowerExact as Resolution
import DASHI.Physics.Closure.NSTriadKNIndexedGluingRound32Exact as Gluing
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity

------------------------------------------------------------------------
-- Parser/name representation -> argument-bearing PNF object.
------------------------------------------------------------------------

record ParserRepresentation : Set where
  constructor parserRepresentation
  field
    representationToken : TokenId
    representationObject : ObjectId

open ParserRepresentation public

record ParserArgumentProjection : Set where
  constructor parserArgumentProjection
  field
    projectArgument : ParserRepresentation → ObjectId

open ParserArgumentProjection public

ParserArgumentGluing : ParserArgumentProjection → Set
ParserArgumentGluing projection =
  Gluing.IndexedGluing
    ParserRepresentation
    ObjectId
    (projectArgument projection)

record ParserArgumentSupportRelation
    (projection : ParserArgumentProjection)
    (source : ParserRepresentation)
    (target : ObjectId) : Set where
  constructor parserArgumentSupportRelation
  field
    projectionMatchesTarget :
      projectArgument projection source ≡ target

open ParserArgumentSupportRelation public

ParserArgumentSupportWitness : ParserArgumentProjection → Set
ParserArgumentSupportWitness projection =
  SupportCore.StructuralSupportEdge
    (ParserArgumentSupportRelation projection)

supportWitnessFromGluing :
  (projection : ParserArgumentProjection) →
  (gluing : ParserArgumentGluing projection) →
  String → String →
  ParserArgumentSupportWitness projection
supportWitnessFromGluing projection gluing provenance scope =
  SupportCore.structuralSupportEdgeAt
    Dependency.relationalLayer
    Dependency.requiredDependency
    (Gluing.externalBase gluing)
    (Gluing.internalBase gluing)
    (parserArgumentSupportRelation (Gluing.glueExact gluing))
    provenance
    scope

------------------------------------------------------------------------
-- Resolution naturality.
------------------------------------------------------------------------

record ParserArgumentResolutionNaturality
    (parserTower argumentTower : Resolution.ResolutionTower) : Set₁ where
  constructor parserArgumentResolutionNaturality
  field
    supportAtResolution :
      (r : Nat) →
      Resolution.Carrier parserTower r →
      Resolution.Carrier argumentTower r
    supportCommutesWithCoarsening :
      ∀ {r}
        (fineParser : Resolution.Carrier parserTower (suc r)) →
      supportAtResolution r
        (Resolution.project parserTower fineParser)
      ≡
      Resolution.project argumentTower
        (supportAtResolution (suc r) fineParser)

open ParserArgumentResolutionNaturality public

------------------------------------------------------------------------
-- Authority boundary: support/gluing alone cannot create identity.
------------------------------------------------------------------------

data SupportIdentityPromotionPermission : Set where

supportAloneCannotCreateIdentity : SupportIdentityPromotionPermission → ⊥
supportAloneCannotCreateIdentity ()

------------------------------------------------------------------------
-- If identity is to be transported across a representation seam, both ends
-- must already carry admitted identity proofs landing on the same canonical
-- entity. The structural support witness can explain why the representations
-- should be compared; it does not manufacture either proof.
------------------------------------------------------------------------

record SupportAlignedIdentity
    (projection : ParserArgumentProjection) : Set where
  constructor supportAlignedIdentity
  field
    support : ParserArgumentSupportWitness projection
    sourceIdentity : Identity.AdmittedIdentityWitness
    targetIdentity : Identity.AdmittedIdentityWitness
    sourceObjectMatchesSupport :
      Identity.witnessSourceObject
        (Identity.admittedWitness sourceIdentity)
      ≡ representationObject (Dependency.source support)
    targetObjectMatchesSupport :
      Identity.witnessSourceObject
        (Identity.admittedWitness targetIdentity)
      ≡ Dependency.target support
    sameCanonicalEntity :
      Identity.canonicalEntityIdentity
        (Identity.witnessTargetEntity
          (Identity.admittedWitness sourceIdentity))
      ≡
      Identity.canonicalEntityIdentity
        (Identity.witnessTargetEntity
          (Identity.admittedWitness targetIdentity))

open SupportAlignedIdentity public

record ParserArgumentSupportBoundary : Set where
  constructor parserArgumentSupportBoundary
  field
    structuralSupportIsNotIdentity : SupportIdentityPromotionPermission → ⊥
    transportRequiresExactIndexedSeam :
      (projection : ParserArgumentProjection) → Set
    identityAcrossSeamRequiresProofAtBothEnds :
      (projection : ParserArgumentProjection) → Set
    multiscaleSupportRequiresNaturalityWitness :
      (parserTower argumentTower : Resolution.ResolutionTower) → Set
    canonicalStructuralSupportCoreReused : Bool
    canonicalStructuralSupportCoreReusedIsTrue :
      canonicalStructuralSupportCoreReused ≡ true

open ParserArgumentSupportBoundary public

canonicalParserArgumentSupportBoundary : ParserArgumentSupportBoundary
canonicalParserArgumentSupportBoundary =
  parserArgumentSupportBoundary
    supportAloneCannotCreateIdentity
    ParserArgumentGluing
    SupportAlignedIdentity
    ParserArgumentResolutionNaturality
    true refl
