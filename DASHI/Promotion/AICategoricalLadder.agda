module DASHI.Promotion.AICategoricalLadder where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ResidualNaturality as RN

import DASHI.Promotion.TensorFlowCategoricalLoom as TF
import DASHI.Promotion.TFLEncodingCategoricalLoom as TFL
import DASHI.Physics.NSAIEncoding as NS
import DASHI.Physics.NSAIEncodingCategoricalLoom as NSAI

----------------------------------------------------------------------
-- AI categorical ladder
--
--   TF ⊑ TFL ⊑ NS-AI ⊑ DASHI
--
-- The order is grammar refinement, not definitional inclusion of carrier
-- types.  Richer grammars forget structure into weaker grammars.  The
-- reverse direction is partial and requires admissibility evidence.
----------------------------------------------------------------------

data LadderRung : Set where
  rungPlainTF : LadderRung
  rungTFL     : LadderRung
  rungNSAI    : LadderRung
  rungDASHI   : LadderRung

data _⊑_ : LadderRung → LadderRung → Set where
  tf⊑tfl     : rungPlainTF ⊑ rungTFL
  tfl⊑nsai   : rungTFL ⊑ rungNSAI
  nsai⊑dashi : rungNSAI ⊑ rungDASHI

record GrammarRefinement
  (Weak Strong : GGC.GrammarGeneratedCategory) : Set₁ where
  field
    forgetGrammar : GGC.Grammar Strong → GGC.Grammar Weak
    forgetCategory :
      (γ : GGC.Grammar Strong) →
      RN.ResidualNaturality
        (GGC.𝓟 Strong γ)
        (GGC.𝓟 Weak (forgetGrammar γ))
    refinementReading : String

open GrammarRefinement public

----------------------------------------------------------------------
-- TFL → TF grammar erasure.
----------------------------------------------------------------------

tflToTFGrammar : TFL.TFLGrammar → TF.TFGrammar
tflToTFGrammar Γ = record
  { inputSchema         = tt
  ; architecture        = tt
  ; layerTypes          = tt
  ; activationFunctions = tt
  ; parameterShapes     = tt
  ; lossFunction        = tt
  ; optimiser           = tt
  ; learningRate        = tt
  ; regularisation      = tt
  ; trainingData        = tt
  ; batchingOrder       = tt
  ; stoppingCriterion   = tt
  ; grammarReading      = "forget Gamma_TFL to Gamma_TF"
  }

-- Object map for the forgetful comparison.
tflToTFObj : TFL.TFLObj → TF.TFObj
tflToTFObj TFL.rawFeature        = TF.rawInput
tflToTFObj TFL.calibratedFeature = TF.tensorSurface
tflToTFObj TFL.latticeCell       = TF.hiddenRepr
tflToTFObj TFL.interpolated      = TF.hiddenRepr
tflToTFObj TFL.prediction        = TF.predictionSurface
tflToTFObj TFL.outputCalibrated  = TF.predictionSurface

-- Carrier codecs make the ontology change explicit.  They are not
-- assumed to be definitional equalities.
record TFLTFCarrierBridge : Set₁ where
  field
    encode : (A : TFL.TFLObj) →
      TFL.Underlying A → TF.Underlying (tflToTFObj A)
    decode : (A : TFL.TFLObj) →
      TF.Underlying (tflToTFObj A) → TFL.Underlying A
    encodeDecode : (A : TFL.TFLObj)
      (x : TF.Underlying (tflToTFObj A)) →
      encode A (decode A x) ≡ x
    decodeEncode : (A : TFL.TFLObj)
      (x : TFL.Underlying A) →
      decode A (encode A x) ≡ x
    bridgeReading : String

open TFLTFCarrierBridge public

tflToTFHom : (B : TFLTFCarrierBridge) →
  ∀ {A C} → (TFL.Underlying A → TFL.Underlying C) →
  TF.Underlying (tflToTFObj A) → TF.Underlying (tflToTFObj C)
tflToTFHom B {A} {C} f x = encode B C (f (decode B A x))

-- Function equality is not definitional after carrier encoding/decoding;
-- these are the exact functor-law proof obligations.
postulate
  tflToTF-id : (B : TFLTFCarrierBridge) → ∀ {A} →
    tflToTFHom B (λ (x : TFL.Underlying A) → x) ≡
    (λ (x : TF.Underlying (tflToTFObj A)) → x)

  tflToTF-comp : (B : TFLTFCarrierBridge) →
    ∀ {A C D}
    (f : TFL.Underlying C → TFL.Underlying D)
    (g : TFL.Underlying A → TFL.Underlying C) →
    tflToTFHom B (λ x → f (g x)) ≡
    (λ x → tflToTFHom B f (tflToTFHom B g x))

tflToTFCategory : (B : TFLTFCarrierBridge) (Γ : TFL.TFLGrammar) →
  RN.ResidualNaturality TFL.tflProjectionCategory TF.tfProjectionCategory
tflToTFCategory B Γ = record
  { FObj            = tflToTFObj
  ; FHom            = tflToTFHom B
  ; F-id            = tflToTF-id B
  ; F-comp          = tflToTF-comp B
  ; residual        = λ f α → ∀ x → tflToTFHom B f x ≡ α x
  ; closed          = λ f α → ∀ x → tflToTFHom B f x ≡ α x
  ; residualReading = "TFL to TF: constraint erasure with explicit object/carrier codecs"
  }

record TFLRefinesTF : Set₁ where
  field
    carrierBridge : TFLTFCarrierBridge

  refinement : GrammarRefinement TF.tfGrammarCategory TFL.tflGrammarCategory
  refinement = record
    { forgetGrammar     = tflToTFGrammar
    ; forgetCategory    = tflToTFCategory carrierBridge
    ; refinementReading =
        "TF <= TFL: TFL forgets lattice constraints through an explicit carrier bridge."
    }

open TFLRefinesTF public

----------------------------------------------------------------------
-- TF → TFL strengthening is partial.
----------------------------------------------------------------------

record TFLAdmissibility (Γ : TF.TFGrammar) : Set₁ where
  field
    calibratableFeatures       : Set
    finiteLatticeWitness       : Set
    constraintConsistency      : Set
    interactionCompatibility   : Set
    outputCalibrationWitness   : Set
    admissibilityReading       : String

open TFLAdmissibility public

record LatticeRefinement (Γ : TF.TFGrammar) : Set₁ where
  field
    refine : TFLAdmissibility Γ → TFL.TFLGrammar
    reading : String

open LatticeRefinement public

----------------------------------------------------------------------
-- NS-AI → TFL categorical comparison through feature/prediction codecs.
----------------------------------------------------------------------

nsaiToTFLObj : NSAI.NSAIObj → TFL.TFLObj
nsaiToTFLObj NSAI.carrierPkg = TFL.rawFeature
nsaiToTFLObj NSAI.observable = TFL.outputCalibrated

record NSAITFLCarrierBridge : Set₁ where
  field
    encodeNS : (A : NSAI.NSAIObj) →
      NSAI.Underlying A → TFL.Underlying (nsaiToTFLObj A)
    decodeNS : (A : NSAI.NSAIObj) →
      TFL.Underlying (nsaiToTFLObj A) → NSAI.Underlying A
    encodeDecodeNS : (A : NSAI.NSAIObj)
      (x : TFL.Underlying (nsaiToTFLObj A)) →
      encodeNS A (decodeNS A x) ≡ x
    decodeEncodeNS : (A : NSAI.NSAIObj)
      (x : NSAI.Underlying A) →
      decodeNS A (encodeNS A x) ≡ x
    bridgeReading : String

open NSAITFLCarrierBridge public

nsaiToTFLHom : (B : NSAITFLCarrierBridge) →
  ∀ {A C} → (NSAI.Underlying A → NSAI.Underlying C) →
  TFL.Underlying (nsaiToTFLObj A) → TFL.Underlying (nsaiToTFLObj C)
nsaiToTFLHom B {A} {C} f x = encodeNS B C (f (decodeNS B A x))

postulate
  nsaiToTFL-id : (B : NSAITFLCarrierBridge) → ∀ {A} →
    nsaiToTFLHom B (λ (x : NSAI.Underlying A) → x) ≡
    (λ (x : TFL.Underlying (nsaiToTFLObj A)) → x)

  nsaiToTFL-comp : (B : NSAITFLCarrierBridge) →
    ∀ {A C D}
    (f : NSAI.Underlying C → NSAI.Underlying D)
    (g : NSAI.Underlying A → NSAI.Underlying C) →
    nsaiToTFLHom B (λ x → f (g x)) ≡
    (λ x → nsaiToTFLHom B f (nsaiToTFLHom B g x))

nsaiToTFLCategory : (B : NSAITFLCarrierBridge)
  (o : NS.FlowObservable) →
  RN.ResidualNaturality
    (NSAI.nsaiProjectionCategory o)
    TFL.tflProjectionCategory
nsaiToTFLCategory B o = record
  { FObj            = nsaiToTFLObj
  ; FHom            = nsaiToTFLHom B
  ; F-id            = nsaiToTFL-id B
  ; F-comp          = nsaiToTFL-comp B
  ; residual        = λ f α → ∀ x → nsaiToTFLHom B f x ≡ α x
  ; closed          = λ f α → ∀ x → nsaiToTFLHom B f x ≡ α x
  ; residualReading = "NS-AI to TFL: flow carrier/observable encoded as feature/prediction surfaces"
  }

record NSAICategoricalRefinement (Γ : TFL.TFLGrammar) : Set₁ where
  field
    observable    : NS.FlowObservable
    carrierBridge : NSAITFLCarrierBridge

  forgetNSAIToTFL :
    RN.ResidualNaturality
      (NSAI.nsaiProjectionCategory observable)
      TFL.tflProjectionCategory
  forgetNSAIToTFL = nsaiToTFLCategory carrierBridge observable

  refinementReading : String
  refinementReading =
    "TFL <= NS-AI: a selected flow-observable category forgets symbolic/domain structure through explicit feature codecs."

open NSAICategoricalRefinement public

----------------------------------------------------------------------
-- Complete ladder package.
----------------------------------------------------------------------

record AICategoricalLadder : Set₁ where
  field
    tfGrammar  : TF.TFGrammar
    tflGrammar : TFL.TFLGrammar
    tflRefinesTFWitness    : TFLRefinesTF
    tfToTFLAdmissibility   : LatticeRefinement tfGrammar
    tflToNSAIComparison    : NSAICategoricalRefinement tflGrammar
    ladderReading          : String

  rungDescription : LadderRung → String
  rungDescription rungPlainTF =
    "TF: architecture/training grammar generates differentiable tensor programs"
  rungDescription rungTFL =
    "TFL: TF grammar plus lattice/calibration/shape constraints generates constrained predictors"
  rungDescription rungNSAI =
    "NS-AI: learned projections compose with symbolic/proof/reasoning grammars"
  rungDescription rungDASHI =
    "DASHI: arbitrary grammar-generated categories with fibres, looms, authority comparison, promotion and homology"

open AICategoricalLadder public

postulate
  canonicalTFLRefinesTF : TFLRefinesTF
  canonicalLatticeRefinement : LatticeRefinement TF.canonicalTFGrammar
  canonicalNSAICategoricalRefinement :
    NSAICategoricalRefinement TFL.canonicalTFLGrammar

canonicalAICategoricalLadder : AICategoricalLadder
canonicalAICategoricalLadder = record
  { tfGrammar              = TF.canonicalTFGrammar
  ; tflGrammar             = TFL.canonicalTFLGrammar
  ; tflRefinesTFWitness    = canonicalTFLRefinesTF
  ; tfToTFLAdmissibility   = canonicalLatticeRefinement
  ; tflToNSAIComparison    = canonicalNSAICategoricalRefinement
  ; ladderReading          =
      "TF <= TFL <= NS-AI <= DASHI with dependent fibres, concrete looms, explicit carrier codecs and partial strengthening."
  }
