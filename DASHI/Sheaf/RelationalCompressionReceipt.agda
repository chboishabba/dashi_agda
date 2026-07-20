module DASHI.Sheaf.RelationalCompressionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Product using (Σ; _,_)

import DASHI.Sheaf.TemporalNoodleSheafBridge as Temporal

record RelationalCompressionSurface : Set₁ where
  field
    Context Model ProvenanceCarrier ResidualCarrier Global : Set
    compress : Context → Model
    source : Context → ProvenanceCarrier
    remainder : Context → ResidualCarrier
    Compatible : Context → Context → Set
    Glues : Global → Context → Context → Set
    glue : ∀ left right → Compatible left right → Σ Global (λ g → Glues g left right)

data LocalContext : Set where
  sensoryContext ecologicalContext : LocalContext

data CompressedModel : Set where
  relationalTeachingModel : CompressedModel

data ExampleProvenance : Set where
  suppliedSensoryProvenance suppliedEcologicalProvenance : ExampleProvenance

data ExampleResidual : Set where
  sensoryOmission ecologicalOmission : ExampleResidual

data GlobalAccount : Set where
  joinedRelationalAccount : GlobalAccount

compressLocal : LocalContext → CompressedModel
compressLocal sensoryContext = relationalTeachingModel
compressLocal ecologicalContext = relationalTeachingModel

sourceLocal : LocalContext → ExampleProvenance
sourceLocal sensoryContext = suppliedSensoryProvenance
sourceLocal ecologicalContext = suppliedEcologicalProvenance

remainderLocal : LocalContext → ExampleResidual
remainderLocal sensoryContext = sensoryOmission
remainderLocal ecologicalContext = ecologicalOmission

data CompatibleLocal : LocalContext → LocalContext → Set where
  sensorySelfCompatible : CompatibleLocal sensoryContext sensoryContext
  ecologicalSelfCompatible : CompatibleLocal ecologicalContext ecologicalContext
  sensoryEcologicalCompatible : CompatibleLocal sensoryContext ecologicalContext
  ecologicalSensoryCompatible : CompatibleLocal ecologicalContext sensoryContext

data GluesLocal : GlobalAccount → LocalContext → LocalContext → Set where
  gluesSensorySelf : GluesLocal joinedRelationalAccount sensoryContext sensoryContext
  gluesEcologicalSelf : GluesLocal joinedRelationalAccount ecologicalContext ecologicalContext
  gluesSensoryEcological : GluesLocal joinedRelationalAccount sensoryContext ecologicalContext
  gluesEcologicalSensory : GluesLocal joinedRelationalAccount ecologicalContext sensoryContext

glueLocal : ∀ left right → CompatibleLocal left right → Σ GlobalAccount (λ g → GluesLocal g left right)
glueLocal sensoryContext sensoryContext sensorySelfCompatible = joinedRelationalAccount , gluesSensorySelf
glueLocal ecologicalContext ecologicalContext ecologicalSelfCompatible = joinedRelationalAccount , gluesEcologicalSelf
glueLocal sensoryContext ecologicalContext sensoryEcologicalCompatible = joinedRelationalAccount , gluesSensoryEcological
glueLocal ecologicalContext sensoryContext ecologicalSensoryCompatible = joinedRelationalAccount , gluesEcologicalSensory

canonicalRelationalCompressionSurface : RelationalCompressionSurface
canonicalRelationalCompressionSurface = record
  { Context = LocalContext
  ; Model = CompressedModel
  ; ProvenanceCarrier = ExampleProvenance
  ; ResidualCarrier = ExampleResidual
  ; Global = GlobalAccount
  ; compress = compressLocal
  ; source = sourceLocal
  ; remainder = remainderLocal
  ; Compatible = CompatibleLocal
  ; Glues = GluesLocal
  ; glue = glueLocal
  }

ecologicalResidualRetained : remainderLocal ecologicalContext ≡ ecologicalOmission
ecologicalResidualRetained = refl

record RelationalCompressionBoundary : Set where
  constructor relationalCompressionBoundary
  field
    temporalApplicationBoundary : Temporal.QITSheafificationApplicationBoundary
    provenanceRetained residualRetained overlapCompatibilityRequired : Bool
    localCompressionIsGlobalTruth : Bool
    localCompressionIsGlobalTruthIsFalse : localCompressionIsGlobalTruth ≡ false
    omissionMeansIrrelevance : Bool
    omissionMeansIrrelevanceIsFalse : omissionMeansIrrelevance ≡ false
    compressionCreatesCommunityAuthority : Bool
    compressionCreatesCommunityAuthorityIsFalse : compressionCreatesCommunityAuthority ≡ false
    interpretation : String

canonicalRelationalCompressionBoundary : RelationalCompressionBoundary
canonicalRelationalCompressionBoundary =
  relationalCompressionBoundary
    Temporal.canonicalQITSheafificationApplicationBoundary
    true true true
    false refl
    false refl
    false refl
    "relational compression retains provenance, remainder, and gluing authority; a local compressed story is not universal or community-authoritative truth"
