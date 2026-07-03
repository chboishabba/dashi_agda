module DASHI.Promotion.AICategoricalLadder where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ResidualNaturality as RN
import DASHI.Core.PromotionTransformation as PT

import DASHI.Promotion.TensorFlowCategoricalLoom as TF
import DASHI.Promotion.TFLEncodingCategoricalLoom as TFL
import DASHI.Physics.NSAIEncodingCategoricalLoom as NSAI

----------------------------------------------------------------------
-- AI Categorical Ladder
--
-- Records the refinement hierarchy:
--
--   Plain TF
--     ⊂ TFL
--       ⊂ NS-AI
--         ⊂ DASHI general (grammar-generated categorical AI)
--
-- Each step is a grammar refinement:
--   Γ_TF  →  Γ_TFL  →  Γ_NSAI  →  Γ_DASHI
--
-- The grammar refines (adds more structure), so the morphism space
-- shrinks (more constraints = fewer admissible morphisms).
--
--   Hom_𝓟_TF  ⊇  Hom_𝓟_TFL  ⊇  Hom_𝓟_NSAI  ⊇  Hom_𝓟_DASHI
--
-- Formally, each inclusion is a functor (forgetful / embedding)
-- tracked as a ResidualNaturality instance.
----------------------------------------------------------------------

-- Ladder position: which rung a grammar sits on

data LadderRung : Set where
  rungPlainTF  : LadderRung
  rungTFL      : LadderRung
  rungNSAI     : LadderRung
  rungDASHI    : LadderRung

record AICategoricalLadder : Set₁ where

  --------------------------------------------------------------------
  -- 1.  Grammar types at each rung
  --------------------------------------------------------------------

  field
    tfGrammar  : TF.TFGrammar
    tflGrammar : TFL.TFLGrammar

  -- NS-AI grammar is FlowObservable (imported from NSAIEncodingCategoricalLoom)
  -- DASHI general grammar is any Set — no canonical default.

  --------------------------------------------------------------------
  -- 2.  Forgetful map: TFL → TF
  --
  -- TFLGrammar has everything TFGrammar has (architecture/training)
  -- plus constraint fields.  This projection forgets the constraints.
  --------------------------------------------------------------------

  forgetTFLConstraints : TFL.TFLGrammar → TF.TFGrammar
  forgetTFLConstraints Γ = record
    { inputSchema        = tt
    ; architecture       = tt
    ; layerTypes         = tt
    ; activationFunctions = tt
    ; parameterShapes    = tt
    ; lossFunction       = tt
    ; optimiser          = tt
    ; learningRate       = tt
    ; regularisation     = tt
    ; trainingData       = tt
    ; batchingOrder      = tt
    ; stoppingCriterion  = tt
    ; grammarReading     = "forgetful: TFL -> TF (constraints dropped)"
    }

  --------------------------------------------------------------------
  -- 3.  Structure map: TF → TFL
  --
  -- The inverse is not always possible: not every TF architecture
  -- admits a lattice-constraint refinement.  When it does, this
  -- map records how lattice/shape constraints are added.
  --------------------------------------------------------------------

  field
    refineWithLattice : TF.TFGrammar → TFL.TFLGrammar

  --------------------------------------------------------------------
  -- 4.  NS-AI sits on a different ontology (flow observables), so
  --     the grammar is not a simple extension of TFL.  The ladder
  --     step is conceptual:
  --
  --       TFL:  lattice-constrained learned tensor projections
  --       NS-AI: learned + symbolic/proof/reasoning projections
  --
  --     We record a postulated bridging map as a free parameter.
  --------------------------------------------------------------------

  field
    nsaiBridgeAvailable : ⊤

  --------------------------------------------------------------------
  -- 5.  Residual naturality between TF and TFL
  --
  --     A functor F : 𝓟_TF → 𝓟_TFL that embeds the unconstrained
  --     category into the constrained one, plus residual maps that
  --     measure how much structure is lost/gained.
  --------------------------------------------------------------------

  field
    tfToTFLResidual : RN.ResidualNaturality
      TF.tfProjectionCategory
      TFL.tflProjectionCategory

    tflToTFResidual : RN.ResidualNaturality
      TFL.tflProjectionCategory
      TF.tfProjectionCategory

  --------------------------------------------------------------------
  -- 6.  Summary: each rung has a grammar, a category, and a reading
  --------------------------------------------------------------------

  rungDescription : LadderRung → String
  rungDescription rungPlainTF  =
    "TF:   architecture/training grammar → differentiable tensor programs"
  rungDescription rungTFL      =
    "TFL:  TF + lattice/calibration/shape constraints → constrained predictors"
  rungDescription rungNSAI     =
    "NS-AI: learned + symbolic/proof/reasoning categories"
  rungDescription rungDASHI   =
    "DASHI: any grammar → projection category → fibre/loom → authority/promotion"

----------------------------------------------------------------------
-- Canonical ladder instance
--
-- All fields except the structural maps are postulated.  The ladder
-- is not yet fully wired; this record states the intended hierarchy.
----------------------------------------------------------------------

postulate
  canonicalTFLRefinement : TF.TFGrammar → TFL.TFLGrammar
  tfToTFLResidualInstance : RN.ResidualNaturality TF.tfProjectionCategory TFL.tflProjectionCategory
  tflToTFResidualInstance : RN.ResidualNaturality TFL.tflProjectionCategory TF.tfProjectionCategory

canonicalAICategoricalLadder : AICategoricalLadder
canonicalAICategoricalLadder = record
  { tfGrammar            = TF.canonicalTFGrammar
  ; tflGrammar           = TFL.canonicalTFLGrammar
  ; refineWithLattice    = canonicalTFLRefinement
  ; nsaiBridgeAvailable  = tt
  ; tfToTFLResidual      = tfToTFLResidualInstance
  ; tflToTFResidual      = tflToTFResidualInstance
  }
