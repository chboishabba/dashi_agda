module DASHI.Promotion.AICategoricalLadder where

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
-- This is a refinement order on grammars, not a claim that the carrier
-- types or generated categories are definitionally equal.
--
-- A richer grammar forgets structure into a weaker grammar.  The
-- categorical witness therefore runs from the richer generated category
-- to the weaker one.  A map in the opposite direction requires a
-- separate admissibility witness and is not automatic.
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

----------------------------------------------------------------------
-- Generic grammar refinement.
--
-- Strong refines Weak when every strong grammar can be forgotten to a
-- weak grammar and the generated category admits a functorial comparison
-- to the corresponding weak category.
----------------------------------------------------------------------

record GrammarRefinement
  (Weak Strong : GGC.GrammarGeneratedCategory)
  : Set₁ where

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

-- TFL and TF use distinct object and carrier families.  The forgetful
-- category map is therefore an explicit bridge obligation rather than a
-- false definitional inclusion.
postulate
  tflToTFCategory :
    (Γ : TFL.TFLGrammar) →
    RN.ResidualNaturality
      TFL.tflProjectionCategory
      TF.tfProjectionCategory

tflRefinesTF :
  GrammarRefinement
    TF.tfGrammarCategory
    TFL.tflGrammarCategory
tflRefinesTF = record
  { forgetGrammar     = tflToTFGrammar
  ; forgetCategory    = tflToTFCategory
  ; refinementReading =
      "TF <= TFL: TFL forgets lattice constraints to TF; the carrier-level functor remains an explicit bridge obligation."
  }

----------------------------------------------------------------------
-- Weak → strong construction is partial.
----------------------------------------------------------------------

record LatticeRefinement (Γ : TF.TFGrammar) : Set₁ where
  field
    admissible : Set
    refine     : admissible → TFL.TFLGrammar
    reading    : String

open LatticeRefinement public

----------------------------------------------------------------------
-- NS-AI refinement bridge.
--
-- The current NS-AI companion is flow-observable-indexed, while TFL is
-- feature/lattice-indexed.  The bridge is indexed by a selected
-- FlowObservable and remains an explicit categorical transport
-- obligation.
----------------------------------------------------------------------

record NSAICategoricalRefinement (Γ : TFL.TFLGrammar) : Set₁ where
  field
    observable : NS.FlowObservable

    forgetNSAIToTFL :
      RN.ResidualNaturality
        (NSAI.nsaiProjectionCategory observable)
        TFL.tflProjectionCategory

    refinementReading : String

open NSAICategoricalRefinement public

----------------------------------------------------------------------
-- Complete ladder package.
----------------------------------------------------------------------

record AICategoricalLadder : Set₁ where
  field
    tfGrammar   : TF.TFGrammar
    tflGrammar  : TFL.TFLGrammar

    tfToTFLAdmissibility : LatticeRefinement tfGrammar
    tflToNSAIComparison  : NSAICategoricalRefinement tflGrammar

    ladderReading : String

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

----------------------------------------------------------------------
-- Canonical package.
----------------------------------------------------------------------

postulate
  canonicalLatticeRefinement :
    LatticeRefinement TF.canonicalTFGrammar

  canonicalNSAICategoricalRefinement :
    NSAICategoricalRefinement TFL.canonicalTFLGrammar

canonicalAICategoricalLadder : AICategoricalLadder
canonicalAICategoricalLadder = record
  { tfGrammar              = TF.canonicalTFGrammar
  ; tflGrammar             = TFL.canonicalTFLGrammar
  ; tfToTFLAdmissibility   = canonicalLatticeRefinement
  ; tflToNSAIComparison    = canonicalNSAICategoricalRefinement
  ; ladderReading          =
      "TF <= TFL <= NS-AI <= DASHI, with richer-to-weaker forgetful maps and weaker-to-richer admissibility obligations."
  }
