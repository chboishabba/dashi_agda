module DASHI.Cognition.PNF.QuantumDecisionInstrumentHierarchyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.NoncommutativeDecisionUpdateQQExact as Order

------------------------------------------------------------------------
-- MODEL-CLASS HIERARCHY FOR ORDER-EFFECT UPDATE SEMANTICS
--
-- Literature calibration:
-- Masanao Ozawa; Andrei Khrennikov,
-- "Modeling combination of question order effect, response replicability
-- effect, and QQ-equality with quantum instruments",
-- DOI 10.1016/j.jmp.2020.102491.
--
-- This hierarchy prevents a projective-model diagnostic such as QQ equality
-- from being silently promoted to every generalized state-update model.
------------------------------------------------------------------------

data GenericUpdateModel : Set where genericUpdateModel : GenericUpdateModel

data QuantumInstrumentModel : Set where quantumInstrumentModel : QuantumInstrumentModel

data ProjectiveModel : Set where projectiveModel : ProjectiveModel

instrumentToGeneric : QuantumInstrumentModel → GenericUpdateModel
instrumentToGeneric quantumInstrumentModel = genericUpdateModel

projectiveToInstrument : ProjectiveModel → QuantumInstrumentModel
projectiveToInstrument projectiveModel = quantumInstrumentModel

projectiveToGeneric : ProjectiveModel → GenericUpdateModel
projectiveToGeneric model = instrumentToGeneric (projectiveToInstrument model)

projectiveWitnessSatisfiesQQ : Order.QQSatisfied Order.projectiveLikeCounts
projectiveWitnessSatisfiesQQ = Order.projectiveLikeSatisfiesQQ

record GeneralizedInstrumentWitness : Set where
  constructor generalizedInstrumentWitness
  field
    instrumentClass : QuantumInstrumentModel
    counts : Order.QQCounts
    qqMayFail : Order.QQSatisfied counts → ⊥

canonicalGeneralizedInstrumentWitness : GeneralizedInstrumentWitness
canonicalGeneralizedInstrumentWitness =
  generalizedInstrumentWitness
    quantumInstrumentModel
    Order.violatingCounts
    Order.qqNotUniversal

generalizedInstrumentDoesNotForceQQ :
  Order.QQSatisfied
    (GeneralizedInstrumentWitness.counts canonicalGeneralizedInstrumentWitness) → ⊥
generalizedInstrumentDoesNotForceQQ =
  GeneralizedInstrumentWitness.qqMayFail canonicalGeneralizedInstrumentWitness

record QuantumDecisionInstrumentHierarchyBoundary : Set where
  constructor quantumDecisionInstrumentHierarchyBoundary
  field
    everyGenericUpdateIsProjective : Bool
    everyInstrumentMustSatisfyQQ : Bool
    projectiveModelsEmbedIntoInstrumentClass : Bool
    instrumentModelsEmbedIntoGenericClass : Bool

canonicalQuantumDecisionInstrumentHierarchyBoundary :
  QuantumDecisionInstrumentHierarchyBoundary
canonicalQuantumDecisionInstrumentHierarchyBoundary =
  quantumDecisionInstrumentHierarchyBoundary false false true true
