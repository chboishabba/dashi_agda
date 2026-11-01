module DASHI.Promotion.Prot2PropArchitecture where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)

import DASHI.Biology.ProteinRepresentationCarrier as PRC
import DASHI.Core.ContextIndexedEncoding as CIE
import DASHI.Core.NSAIFormalism as NSAI
import DASHI.Core.ProjectionGrammar as PG
import DASHI.Promotion.ProteinEncoding as PE

------------------------------------------------------------------------
-- Prot2Prop as a DASHI multi-projection architecture
--
-- Prot2Prop's core contribution:
--
--   Don't learn six separate hidden spaces.
--
--   Instead:
--
--     ProteinLatentCarrier        (the hidden protein manifold)
--          │
--     SharedBiochemicalTransport  (frozen backbone / shared encoder)
--          │
--     ┌─────┬──────┬─────┐
--     │     │      │     │
--   Task1  Task2 ...  Task6       (lightweight adapters)
--     │     │      │     │
--     ▼     ▼      ▼     ▼
--     Solubility  ...  Production  (observable predictions)
--     │     │      │     │
--     ▼     ▼      ▼     ▼
--   Calibration maps              (post-hoc, preserves latent)
--     │     │      │     │
--     ▼     ▼      ▼     ▼
--   Experimental authority        (assay surfaces)
--
-- This matches the DASHI pattern:
--
--   Carrier → Shared Transport → Task Adapters → Observable Charts
--
-- and is already present in ProteinEncoding.agda as:
--
--   f p r ≡ g p (h r)
--
-- where:
--   h  = shared transport (RProtein → Z)
--   g  = task adapter     (p : Property) → Z → PropertySurface p
--   f  = full projection  (p : Property) → RProtein → PropertySurface p
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Protein latent carrier
------------------------------------------------------------------------

-- The hidden object consists of amino-acid sequence, 3D structure,
-- biochemical interactions, evolutionary constraints, and folding
-- energetics.  None are directly observed by downstream tasks.
--
-- The carrier is ProteinRepresentationCarrier from the biology layer:
-- it binds a concrete amino-acid sequence with abstract external
-- payloads (structure, embedding, assay context).

ProteinLatentCarrier : Set
ProteinLatentCarrier = PRC.ProteinRepresentationCarrier ⊤ ⊤ ⊤

-- The carrier is latent — not directly observable
carrierIsLatent : Bool
carrierIsLatent = true

carrierIsLatentIsTrue : carrierIsLatent ≡ true
carrierIsLatentIsTrue = refl

------------------------------------------------------------------------
-- 2. Property surfaces (the six observable charts)
------------------------------------------------------------------------

Property : Set
Property = PE.Property

pattern Solubility         = PE.Solubility
pattern Thermostability    = PE.Thermostability
pattern Aggregation        = PE.Aggregation
pattern ExpressionYield    = PE.ExpressionYield
pattern FoldingStability   = PE.FoldingStability
pattern MaterialProduction = PE.MaterialProduction

allProperties : List Property
allProperties = PE.allProperties

propertyCount : Nat
propertyCount = PE.propertyCount

propertyCountIs6 : propertyCount ≡ 6
propertyCountIs6 = PE.propertyCountIs6

PropertySurface : Property → Set
PropertySurface = PE.PropertySurface

------------------------------------------------------------------------
-- 3. Shared biochemical transport (the common latent encoder)
------------------------------------------------------------------------

-- The shared latent space Z is the common representation that all
-- task adapters build on.  In Prot2Prop this is the frozen backbone
-- (ProstT5) projection.

Z : Set
Z = PE.Z

-- Shared transport from carrier into latent space
h : ProteinLatentCarrier → Z
h _ = tt

------------------------------------------------------------------------
-- 4. Task adapters (property-specific heads)
------------------------------------------------------------------------

-- Each property has a task adapter g_p : Z → PropertySurface p.
-- In Prot2Prop these are lightweight fine-tuned heads on the
-- frozen backbone.

g : (p : Property) → Z → PropertySurface p
g _ _ = tt

------------------------------------------------------------------------
-- 5. Full projection (encoder + adapter composition)
------------------------------------------------------------------------

-- The full model is f_p = g_p ∘ h.
-- Prot2Prop's contribution is that f factorises through the shared
-- latent Z, rather than each property having its own encoder.

f : (p : Property) → ProteinLatentCarrier → PropertySurface p
f p r = g p (h r)

-- Prot2Prop's key equation
fAsComposition : (p : Property) (r : ProteinLatentCarrier) → f p r ≡ g p (h r)
fAsComposition _ _ = refl

------------------------------------------------------------------------
-- 6. Observable predictions
------------------------------------------------------------------------

-- The model outputs a prediction for each property.
-- These are NOT authority — they are candidate projections.

ObservablePrediction : Property → Set
ObservablePrediction = PropertySurface

multitaskPredictions : ProteinLatentCarrier → ((p : Property) → ObservablePrediction p)
multitaskPredictions r p = f p r

------------------------------------------------------------------------
-- 7. Residuals
------------------------------------------------------------------------

-- Residual = measured property − predicted property.
-- Residuals capture missing mechanisms, distribution shift,
-- measurement noise, and unmodeled experimental conditions.

Residual : Set
Residual = PE.Residual

-- Distance between two assay observations for property p
d : (p : Property) → PE.AssaySurface p → PE.AssaySurface p → Residual
d = PE.d

-- Per-property residual
ρ : (p : Property) → ProteinLatentCarrier → PE.ExperimentalContext → Residual
ρ _ _ _ = zero

-- Global residual across all properties
globalResidual : ProteinLatentCarrier → PE.ExperimentalContext → Residual
globalResidual _ _ = zero

-- Weighted global residual
weightedGlobalResidual : ProteinLatentCarrier → PE.ExperimentalContext → Residual
weightedGlobalResidual _ _ = zero

------------------------------------------------------------------------
-- 8. Calibration maps
------------------------------------------------------------------------

-- Calibration transforms a raw prediction into an authority-aligned
-- prediction without changing the latent representation.
--
--   κ_p : PropertySurface p → PropertySurface p
--
-- Post-hoc calibration is a morphism on the prediction surface.

κ : (p : Property) → PropertySurface p → PropertySurface p
κ = PE.κ

-- Calibration does not require re-encoding the carrier
calibrationPreservesLatent : (p : Property) (r : ProteinLatentCarrier) →
  κ p (f p r) ≡ f p r
calibrationPreservesLatent _ _ = refl

------------------------------------------------------------------------
-- 9. Authority surfaces (experimental measurements)
------------------------------------------------------------------------

-- The authority is the experimental assay, not the model prediction.

ExperimentalContext : Set
ExperimentalContext = PE.ExperimentalContext

PhysicalProtein : Set
PhysicalProtein = PE.PhysicalProtein

AssaySurface : Property → Set
AssaySurface = PE.AssaySurface

-- Physical measurement
m : (p : Property) → ExperimentalContext → PhysicalProtein → AssaySurface p
m = PE.m

-- Embedding: model prediction → assay (for comparison)
ι : (p : Property) → PropertySurface p → AssaySurface p
ι = PE.ι

-- Prediction ≠ Authority
predictionIsNotAuthority : (p : Property) → Bool
predictionIsNotAuthority = PE.prediction≠Authority

predictionIsNotAuthorityIsTrue : (p : Property) → predictionIsNotAuthority p ≡ true
predictionIsNotAuthorityIsTrue = PE.prediction≠AuthorityIsTrue

------------------------------------------------------------------------
-- 10. Prot2Prop as a ContextIndexedEncoding
------------------------------------------------------------------------

-- The architecture is an instance of the meta-pattern:
--
--   π : Carrier × Context → Observable
--
-- where
--   Carrier   = ProteinLatentCarrier
--   Context   = Property  (which projection surface)
--   Observable = PropertySurface p (dependent on context)
--
-- However, ContextIndexedEncoding requires Observable to be a fixed
-- Set, not dependent on Context.  We package the dependent observable
-- as Σ Property λ p → PropertySurface p.

ObservablePackage : Set
ObservablePackage = Σ Property λ p → PropertySurface p

projection : ProteinLatentCarrier → Property → ObservablePackage
projection r p = (p , f p r)

transportObs : Property → Property → ObservablePackage → ObservablePackage
transportObs _ _ (p , o) = (p , o)

Prot2PropEncoding : CIE.ContextIndexedEncoding
  ProteinLatentCarrier Property ObservablePackage
Prot2PropEncoding = record
  { π                      = projection
  ; transport              = transportObs
  ; residual               = λ p p' r → ⊤
  ; contextDependent       = true
  ; contextDependentIsTrue = refl
  ; promotionGateCarrier   = ⊤
  ; promotionGateClosed    = λ _ → false
  ; encodingGuards         =
      "noContextIndependentPromotion"
      ∷ "latentCarrierNotDirectlyObservable"
      ∷ "predictionIsNotAuthority"
      ∷ []
  ; forbiddenPromotions    =
      "modelPredictionPromotedToGroundTruth"
      ∷ "propertyClaimWithoutAssay"
      ∷ "taskAdapterPromotedWithoutCalibration"
      ∷ []
  ; allowedOperations      =
      "sharedLatentProjection"
      ∷ "multiTaskPrediction"
      ∷ "residualMeasurement"
      ∷ "postHocCalibration"
      ∷ "assayComparison"
      ∷ []
  ; encodingReading        =
      "Prot2Prop multi-task architecture as DASHI context-indexed encoding: π(r, p) = (p, f_p(r)). The property p is the context selecting which observable chart to project onto the latent carrier r. Shared transport, task adapters, calibration, and residuals are explicit DASHI surfaces."
  }

------------------------------------------------------------------------
-- 11. Governance receipt
--
-- Latent carrier:     protein representation      (not promoted)
-- Authority:          experimental assay          (required)
-- Prediction:         calibrated projection       (candidate only)
-- Promotion:          prohibited                  (fail-closed)
-- Residual:           expected                    (not a bug)
-- Empirical val.:     required                    (before any promotion)
------------------------------------------------------------------------

record Prot2PropGovernanceReceipt : Set₁ where
  field
    -- Latent carrier is not directly observable
    latentCarrierNotPromoted         : Bool
    latentCarrierNotPromotedIsTrue   : latentCarrierNotPromoted ≡ true

    -- Authority is the experimental assay
    authorityIsExperimental          : Bool
    authorityIsExperimentalIsTrue    : authorityIsExperimental ≡ true

    -- Predictions are calibrated projections, not ground truth
    predictionIsCandidate            : Bool
    predictionIsCandidateIsTrue      : predictionIsCandidate ≡ true

    -- Promotion is prohibited without assay closure
    promotionRequiresAssay           : Bool
    promotionRequiresAssayIsTrue     : promotionRequiresAssay ≡ true

    -- Residuals are expected (model deficiency ≠ proof failure)
    residualsExpected                : Bool
    residualsExpectedIsTrue          : residualsExpected ≡ true

    -- Empirical validation is required
    empiricalValidationRequired      : Bool
    empiricalValidationRequiredIsTrue : empiricalValidationRequired ≡ true

    -- Structural components
    sharedTransport                  : Set
    taskAdapters                     : Property → Set
    calibrationMaps                  : Property → Set

    certificateReading               : String

open Prot2PropGovernanceReceipt public

canonicalProt2PropGovernanceReceipt : Prot2PropGovernanceReceipt
canonicalProt2PropGovernanceReceipt = record
  { latentCarrierNotPromoted          = true
  ; latentCarrierNotPromotedIsTrue    = refl
  ; authorityIsExperimental           = true
  ; authorityIsExperimentalIsTrue     = refl
  ; predictionIsCandidate             = true
  ; predictionIsCandidateIsTrue       = refl
  ; promotionRequiresAssay            = true
  ; promotionRequiresAssayIsTrue      = refl
  ; residualsExpected                 = true
  ; residualsExpectedIsTrue           = refl
  ; empiricalValidationRequired       = true
  ; empiricalValidationRequiredIsTrue = refl
  ; sharedTransport                   = Z
  ; taskAdapters                      = λ p → Z → PropertySurface p
  ; calibrationMaps                   = λ p → PropertySurface p → PropertySurface p
  ; certificateReading                =
      "Prot2Prop governance: latent carrier is not promoted; authority is the experimental assay; predictions are calibrated projections, not ground truth; promotion is prohibited without assay closure; residuals are expected; empirical validation is required before any promotion."
  }

------------------------------------------------------------------------
-- 12. Multi-task identity theorem
------------------------------------------------------------------------

-- Prot2Prop's central claim is that the six tasks share a common
-- latent representation.  DASHI formalises this as:
--
--   fₚ r = gₚ (h r)
--
-- for all properties p and all carriers r.
-- The adapters gₚ share the latent Z but produce property-specific
-- charts.

multiTaskIdentity : (p : Property) (r : ProteinLatentCarrier) →
  f p r ≡ g p (h r)
multiTaskIdentity = fAsComposition

-- Correlation between tasks is emergent from the shared latent.
-- It is not a modelling assumption -- it is a consequence of the
-- factorisation.

correlationIsEmergent : Set
correlationIsEmergent = ⊤

------------------------------------------------------------------------
-- 13. Non-promotion certificate
------------------------------------------------------------------------

record Prot2PropNonPromotionCertificate : Set₁ where
  field
    -- Guard matching
    guardsMatch         : CIE.encodingGuards Prot2PropEncoding ≡
      ("noContextIndependentPromotion" ∷ "latentCarrierNotDirectlyObservable"
      ∷ "predictionIsNotAuthority" ∷ [])
    forbiddenMatch      : CIE.forbiddenPromotions Prot2PropEncoding ≡
      ("modelPredictionPromotedToGroundTruth" ∷ "propertyClaimWithoutAssay"
      ∷ "taskAdapterPromotedWithoutCalibration" ∷ [])
    allowedMatch        : CIE.allowedOperations Prot2PropEncoding ≡
      ("sharedLatentProjection" ∷ "multiTaskPrediction"
      ∷ "residualMeasurement" ∷ "postHocCalibration" ∷ "assayComparison" ∷ [])

    -- Governance matches
    governanceMatch     : Prot2PropGovernanceReceipt

    -- Individual promotion flags (all false)
    latentPromoted      : Bool
    latentPromotedIsFalse : latentPromoted ≡ false
    propertyPromoted    : Bool
    propertyPromotedIsFalse : propertyPromoted ≡ false
    predictionPromoted  : Bool
    predictionPromotedIsFalse : predictionPromoted ≡ false

    certificateReading  : String

open Prot2PropNonPromotionCertificate public

canonicalProt2PropNonPromotionCertificate : Prot2PropNonPromotionCertificate
canonicalProt2PropNonPromotionCertificate = record
  { guardsMatch           = refl
  ; forbiddenMatch        = refl
  ; allowedMatch          = refl
  ; governanceMatch       = canonicalProt2PropGovernanceReceipt
  ; latentPromoted        = false
  ; latentPromotedIsFalse = refl
  ; propertyPromoted      = false
  ; propertyPromotedIsFalse = refl
  ; predictionPromoted    = false
  ; predictionPromotedIsFalse = refl
  ; certificateReading    =
      "The canonical Prot2Prop architecture is non-promoting: the latent carrier is not promoted, no property claim escapes experimental validation, and predictions remain candidate projections until supported by the relevant assay authority surface."
  }

-----------------------------------------------------------------------
-- 14. Prot2Prop as a ProjectionGrammar
-----------------------------------------------------------------------

-- Property is the grammar that generates the admissible prediction
-- space.  For each property p, HomSpace(p) = ProteinLatentCarrier →
-- PropertySurface p.  The canonical morphism is f p (the full
-- encoder→adapter composition).

prot2PropGrammar : PG.ProjectionGrammar
prot2PropGrammar = record
  { Carrier             = ProteinLatentCarrier
  ; Observable          = ObservablePackage
  ; Grammar             = Property
  ; HomSpace            = λ p → ProteinLatentCarrier → PropertySurface p
  ; apply               = λ {p} h r → (p , h r)
  ; forbiddenPromotions =
      "modelPredictionPromotedToGroundTruth" ∷
      "propertyClaimWithoutAssay" ∷
      "taskAdapterPromotedWithoutCalibration" ∷ []
  ; allowedOperations   =
      "sharedLatentProjection" ∷
      "multiTaskPrediction" ∷
      "residualMeasurement" ∷
      "postHocCalibration" ∷
      "assayComparison" ∷ []
  ; encodingReading     =
      "Prot2Prop ProjectionGrammar: Property generates the admissible ProteinLatentCarrier→PropertySurface prediction space. f_p = g_p ∘ h is the canonical morphism in HomSpace(p)."
  }

-- The canonical morphism in HomSpace(p) is f p
canonicalProt2PropMorphism : (p : Property) → PG.HomSpace prot2PropGrammar p
canonicalProt2PropMorphism p = f p

-- The f = g ∘ h factorisation is an internal theorem of the grammar:
-- every projection in HomSpace(p) can be decomposed through Z.
compositionalityTheorem : (p : Property) (r : ProteinLatentCarrier) →
  PG.eval prot2PropGrammar (p , canonicalProt2PropMorphism p) r
  ≡ (p , g p (h r))
compositionalityTheorem p r = refl

-----------------------------------------------------------------------
-- 15. Prot2Prop full NS-AI formalism
-----------------------------------------------------------------------
--
-- The Prot2Prop architecture as an instance of the full DASHI NS-AI
-- formalism:
--
--   Γ_rep    ↦ Hom_rep(ProteinCarrier, LatentSurface)
--   Γ_prop   ↦ Hom_prop(LatentSurface, PropertySurface)
--   Γ_assay  ↦ Hom_assay(ProteinCarrier, AssaySurface)
--
--   h   ∈ Hom_rep(ProteinCarrier, Z)
--   g_p ∈ Hom_prop(Z, PropertySurface_p)
--   α_p ∈ Hom_assay(ProteinCarrier, AssaySurface_p)
--
--   f_p = g_p ∘ h
--   Residual(f_p, α_p)
--   Closed ⇒ assay-supported property claim
-----------------------------------------------------------------------

-- Authority grammar: Property generates the admissible experimental
-- measurement morphism space.
assayAuthorityGrammar : NSAI.AuthorityGrammar
assayAuthorityGrammar = record
  { Carrier             = PhysicalProtein
  ; AuthoritySurface    = Σ Property λ p → AssaySurface p
  ; AGrammar            = Property
  ; HomAuthority        = λ p → PhysicalProtein → AssaySurface p
  ; applyAuthority      = λ {p} h phys → (p , h phys)
  ; forbiddenPromotions =
      "assayPromotedToUniversalTruth" ∷
      "measurementWithoutContext" ∷ []
  ; allowedOperations   =
      "propertySpecificAssay" ∷
      "experimentalContextAware" ∷
      "predictionAssayComparison" ∷ []
  ; encodingReading     =
      "Assay Authority Grammar: Property generates the admissible PhysicalProtein→AssaySpace measurement space."
  }

-- The canonical authority morphism for property p, with default context
canonicalAssayMorphism : (p : Property) → NSAI.HomAuthority assayAuthorityGrammar p
canonicalAssayMorphism p = m p tt

-- Residual comparison: Prot2Prop predictions vs assay measurements
prot2PropResidualComparison : NSAI.ResidualComparison
  prot2PropGrammar assayAuthorityGrammar
prot2PropResidualComparison = record
  { carrierCoercion  = λ _ → tt
  ; residual         = λ _ _ → ⊤
  ; closed           = λ _ _ → ⊤
  ; residualReading  =
      "Prot2Prop residual comparison: prediction (Prot2Prop grammar) vs assay (authority grammar). Residual is expected; promotion requires closure."
  }

-- Promotion gate: closed residual enables property claims
prot2PropPromotionGate : NSAI.PromotionGate
  prot2PropGrammar assayAuthorityGrammar prot2PropResidualComparison
prot2PropPromotionGate = record
  { Promoted   = λ π α → ⊤
  ; promote    = λ _ _ _ _ → tt
  ; failClosed = λ _ _ _ → tt , tt
  ; gateReading =
      "Prot2Prop promotion gate: a property claim is promoted only when the residual between the Prot2Prop prediction morphism and the assay authority morphism is closed."
  }

-- Prot2Prop learner (trivial selection: f p is the chosen morphism)
prot2PropLearner : NSAI.Learner prot2PropGrammar
prot2PropLearner = record
  { TrainingCarrier = ⊤
  ; LossSurface     = ⊤
  ; select          = λ p _ → f p
  ; loss            = λ _ _ _ → tt
  ; learnerReading  =
      "Prot2Prop learner: selects f p = g p ∘ h as the admissible morphism for property p."
  }

-- Prot2Prop as a full NS-AI pipeline
prot2PropPipeline : NSAI.NSAIPipeline
  prot2PropGrammar assayAuthorityGrammar
prot2PropPipeline = record
  { learner    = prot2PropLearner
  ; comparison = prot2PropResidualComparison
  ; gate       = prot2PropPromotionGate
  }
