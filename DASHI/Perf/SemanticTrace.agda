module DASHI.Perf.SemanticTrace where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.String

-- Minimal Dashi-owned semantic vocabulary for perf/DA51 traces.
-- The vocabulary is deliberately small: it establishes the annotation and
-- erasure seam without claiming that the initial classifier is complete.
data DashiClass : Set where
  proof-check      : DashiClass
  witness-export   : DashiClass
  compression-step : DashiClass
  fractran-step    : DashiClass
  shard-transport  : DashiClass
  unknown-class    : DashiClass

data DashiFamily : Set where
  proof-family       : DashiFamily
  witness-family     : DashiFamily
  compression-family : DashiFamily
  execution-family   : DashiFamily
  transport-family   : DashiFamily
  unknown-family     : DashiFamily

record SurfacePerfRow : Set where
  constructor surface-row
  field
    step          : Nat
    event         : String
    timestamp     : Nat
    period        : Nat
    pid           : Nat
    tid           : Nat
    kernelMode    : Bool
    contentId     : String

open SurfacePerfRow public

record SemanticPerfRow : Set where
  constructor semantic-row
  field
    surface     : SurfacePerfRow
    dashiClass  : DashiClass
    dashiFamily : DashiFamily

open SemanticPerfRow public

record Classifier : Set where
  field
    classifyClass  : SurfacePerfRow → DashiClass
    classifyFamily : SurfacePerfRow → DashiFamily

open Classifier public

annotate : Classifier → SurfacePerfRow → SemanticPerfRow
annotate classifier row =
  semantic-row row (classifyClass classifier row) (classifyFamily classifier row)

erase : SemanticPerfRow → SurfacePerfRow
erase row = surface row

-- Semantic annotation is structure-preserving: no surface field is changed or
-- discarded by the Dashi labelling pass.
erase-annotate :
  (classifier : Classifier) →
  (row : SurfacePerfRow) →
  erase (annotate classifier row) ≡ row
erase-annotate classifier row = refl

record SemanticMotifToken : Set where
  constructor semantic-token
  field
    tokenClass  : DashiClass
    tokenFamily : DashiFamily

open SemanticMotifToken public

semanticToken : SemanticPerfRow → SemanticMotifToken
semanticToken row = semantic-token (dashiClass row) (dashiFamily row)

-- The semantic motif projection depends only on the attached Dashi labels.
-- Surface counters and process identifiers remain available in `surface` for
-- exact reconstruction, but do not define motif identity.
semanticToken-annotate :
  (classifier : Classifier) →
  (row : SurfacePerfRow) →
  semanticToken (annotate classifier row)
    ≡ semantic-token
        (classifyClass classifier row)
        (classifyFamily classifier row)
semanticToken-annotate classifier row = refl

record SemanticTraceContract : Set₁ where
  field
    classifier       : Classifier
    annotationExact  : (row : SurfacePerfRow) →
                       erase (annotate classifier row) ≡ row
    motifProjection  : SemanticPerfRow → SemanticMotifToken

canonicalSemanticTraceContract : Classifier → SemanticTraceContract
canonicalSemanticTraceContract classifier = record
  { classifier      = classifier
  ; annotationExact = erase-annotate classifier
  ; motifProjection = semanticToken
  }
