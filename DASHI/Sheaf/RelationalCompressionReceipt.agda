module DASHI.Sheaf.RelationalCompressionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Product using (Σ; _,_)

import DASHI.Sheaf.TemporalNoodleSheafBridge as Temporal

------------------------------------------------------------------------
-- Relational compression retains model, provenance, remainder, and gluing
-- authority.  It is not a flat summary with the omitted context discarded.

record RelationalCompressionSurface : Set₁ where
  field
    Context Model Provenance Residual Global : Set
    compress : Context → Model
    source : Context → Provenance
    remainder : Context → Residual
    Compatible : Context → Context → Set
    Glues : Global → Context → Context → Set
    glue :
      ∀ left right →
      Compatible left right →
      Σ Global (λ global → Glues global left right)

------------------------------------------------------------------------
-- One finite checked instance.

data LocalContext : Set where
  sensoryContext ecologicalContext : LocalContext

data CompressedModel : Set where
  relationalTeachingModel : CompressedModel

data Provenance : Set where
  suppliedSensoryProvenance suppliedEcologicalProvenance : Provenance

data Residual : Set where
  sensoryOmission ecologicalOmission : Residual

data GlobalAccount : Set where
  joinedRelationalAccount : GlobalAccount

compressLocal : LocalContext → CompressedModel
compressLocal sensoryContext = relationalTeachingModel
compressLocal ecologicalContext = relationalTeachingModel

sourceLocal : LocalContext → Provenance
sourceLocal sensoryContext = suppliedSensoryProvenance
sourceLocal ecologicalContext = suppliedEcologicalProvenance

remainderLocal : LocalContext → Residual
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

glueLocal :
  ∀ left right →
  CompatibleLocal left right →
  Σ GlobalAccount (λ global → GluesLocal global left right)
glueLocal sensoryContext sensoryContext sensorySelfCompatible =
  joinedRelationalAccount , gluesSensorySelf
glueLocal ecologicalContext ecologicalContext ecologicalSelfCompatible =
  joinedRelationalAccount , gluesEcologicalSelf
glueLocal sensoryContext ecologicalContext sensoryEcologicalCompatible =
  joinedRelationalAccount , gluesSensoryEcological
glueLocal ecologicalContext sensoryContext ecologicalSensoryCompatible =
  joinedRelationalAccount , gluesEcologicalSensory

canonicalRelationalCompressionSurface : RelationalCompressionSurface
canonicalRelationalCompressionSurface =
  record
    { Context = LocalContext
    ; Model = CompressedModel
    ; Provenance = Provenance
    ; Residual = Residual
    ; Global = GlobalAccount
    ; compress = compressLocal
    ; source = sourceLocal
    ; remainder = remainderLocal
    ; Compatible = CompatibleLocal
    ; Glues = GluesLocal
    ; glue = glueLocal
    }

sensoryModelChecks : compressLocal sensoryContext ≡ relationalTeachingModel
sensoryModelChecks = refl

ecologicalResidualRetained : remainderLocal ecologicalContext ≡ ecologicalOmission
ecologicalResidualRetained = refl

record RelationalCompressionBoundary : Set where
  constructor relationalCompressionBoundary
  field
    temporalApplicationBoundary : Temporal.QITSheafificationApplicationBoundary
    provenanceRetained : Bool
    residualRetained : Bool
    overlapCompatibilityRequired : Bool
    localCompressionIsGlobalTruth : Bool
    localCompressionIsGlobalTruthIsFalse : localCompressionIsGlobalTruth ≡ false
    omissionMeansIrrelevance : Bool
    omissionMeansIrrelevanceIsFalse : omissionMeansIrrelevance ≡ false
    compressionCreatesCommunityAuthority : Bool
    compressionCreatesCommunityAuthorityIsFalse :
      compressionCreatesCommunityAuthority ≡ false
    interpretation : String

canonicalRelationalCompressionBoundary : RelationalCompressionBoundary
canonicalRelationalCompressionBoundary =
  relationalCompressionBoundary
    Temporal.canonicalQITSheafificationApplicationBoundary
    true
    true
    true
    false refl
    false refl
    false refl
    "relational compression carries a model, provenance, retained remainder, and overlap/gluing receipt; a local compressed story is not promoted to universal or community-authoritative truth"
