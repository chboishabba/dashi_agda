module DASHI.Cognition.PNF.LearningAlgebra where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.MemoryFibre as Memory

data LearningKind : Set where
  revaluationLearning habituationLearning reinforcementLearning : LearningKind
  extinctionLearning trustFormationLearning contextGeneralisationLearning : LearningKind
  contextSpecificInhibitionLearning phaseRealignmentLearning : LearningKind

record WeightedTransition : Set where
  constructor weightedTransition
  field
    fromLabel toLabel : String
    transitionWeight : Nat
    transitionReceipt : String

open WeightedTransition public

record PNFMemoryField : Set where
  constructor pnfMemoryField
  field
    memories : List Memory.MemoryFibre
    transitionGraph : List WeightedTransition
    fieldRevision : Nat

open PNFMemoryField public

record LearningReceipt : Set where
  constructor learningReceipt
  field
    learningKind : LearningKind
    before after : Memory.MemoryFibre
    publicSemanticContentPreserved : Bool
    publicSemanticContentPreservedIsTrue :
      publicSemanticContentPreserved ≡ true
    learningReceiptId : String

open LearningReceipt public

revaluationReceipt : Memory.MemoryFibre → Nat → LearningReceipt
revaluationReceipt memory value =
  learningReceipt revaluationLearning memory (Memory.revalue memory value)
    true refl "revaluation preserves PNF event identity"

habituationReceipt : Memory.MemoryFibre → LearningReceipt
habituationReceipt memory =
  learningReceipt habituationLearning memory (Memory.habituate memory)
    true refl "habituation lowers salience without deleting content"

reinforcementReceipt : Memory.MemoryFibre → LearningReceipt
reinforcementReceipt memory =
  learningReceipt reinforcementLearning memory (Memory.reinforce memory)
    true refl "reinforcement increases transition weight"

extinctionReceipt : Memory.MemoryFibre → LearningReceipt
extinctionReceipt memory =
  learningReceipt extinctionLearning memory
    (Memory.extinguishActionDominance memory)
    true refl "extinction inhibits action dominance without erasure"

phaseRealignmentReceipt : Memory.MemoryFibre → Nat → LearningReceipt
phaseRealignmentReceipt memory phase =
  learningReceipt phaseRealignmentLearning memory (Memory.realignPhase memory phase)
    true refl "phase realignment preserves remembered event"

record ContextGeneralisationReceipt : Set where
  constructor contextGeneralisationReceipt
  field
    memory : Memory.MemoryFibre
    sourceContext targetContext : String
    transportCertificate : String
    generalisationIsAutomatic : Bool
    generalisationIsAutomaticIsFalse : generalisationIsAutomatic ≡ false

open ContextGeneralisationReceipt public

record TrustFormationReceipt : Set where
  constructor trustFormationReceipt
  field
    sourceAgent context : String
    prediction outcome : PNF.EventPNF
    priorTrust updatedTrust : Nat
    provenanceReceipt : String

open TrustFormationReceipt public
