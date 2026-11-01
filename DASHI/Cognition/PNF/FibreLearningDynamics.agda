module DASHI.Cognition.PNF.FibreLearningDynamics where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning

record FibreLearningUpdate : Set where
  constructor fibreLearningUpdate
  field
    before after : Memory.MemoryFibre
    publicLabelBefore publicLabelAfter : String
    transitionGraphBefore transitionGraphAfter : List Learning.WeightedTransition
    rememberedPNFPreserved :
      Memory.rememberedEvent after ≡ Memory.rememberedEvent before
    publicCategoryPreserved : publicLabelAfter ≡ publicLabelBefore
    updateReceipt : String

open FibreLearningUpdate public

reweightWithinFibre :
  Memory.MemoryFibre →
  String →
  List Learning.WeightedTransition →
  List Learning.WeightedTransition →
  FibreLearningUpdate
reweightWithinFibre memory publicLabel oldGraph newGraph =
  fibreLearningUpdate
    memory
    (Memory.reinforce memory)
    publicLabel
    publicLabel
    oldGraph
    newGraph
    refl
    refl
    "transition weights changed inside one public PNF fibre"

rewireWithinFibre :
  Memory.MemoryFibre →
  String →
  List Learning.WeightedTransition →
  List Learning.WeightedTransition →
  FibreLearningUpdate
rewireWithinFibre memory publicLabel oldGraph newGraph =
  fibreLearningUpdate
    memory
    (Memory.extinguishActionDominance memory)
    publicLabel
    publicLabel
    oldGraph
    newGraph
    refl
    refl
    "transition topology changed while remembered PNF and public category remained fixed"
