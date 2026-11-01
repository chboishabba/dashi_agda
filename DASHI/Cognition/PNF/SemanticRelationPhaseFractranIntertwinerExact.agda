module DASHI.Cognition.PNF.SemanticRelationPhaseFractranIntertwinerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.ConsumerRelationSheetFractranQuotientBidiExact as Sheet
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- Exact interface for the chain
--   semantic relation sheet -> selected phase -> FRACTRAN transport.
--
-- The three carriers remain distinct.  A consumer must provide the two
-- intertwiners that make transpose/sign reversal commute with phase inversion
-- and reciprocal FRACTRAN transport respectively.
------------------------------------------------------------------------

record RelationPhaseCompiler : Set₁ where
  constructor relationPhaseCompiler
  field
    selectPhase : Sheet.RelationSheet3 → Trit.SSPTrit
    transposePhaseLaw :
      (relation : Sheet.RelationSheet3) →
      selectPhase (Sheet.transposeSheet relation)
      ≡ Context.negateTrit (selectPhase relation)

open RelationPhaseCompiler public

record PhaseFractranCompiler : Set₁ where
  constructor phaseFractranCompiler
  field
    compilePhase : Trit.SSPTrit → Context.FractranFraction
    inversePhaseLaw :
      (phase : Trit.SSPTrit) →
      compilePhase (Context.negateTrit phase)
      ≡ Context.reciprocal (compilePhase phase)

open PhaseFractranCompiler public

compileRelation :
  RelationPhaseCompiler →
  PhaseFractranCompiler →
  Sheet.RelationSheet3 →
  Context.FractranFraction
compileRelation relationCompiler fractranCompiler relation =
  compilePhase fractranCompiler (selectPhase relationCompiler relation)

transposeCompilesToReciprocal :
  (relationCompiler : RelationPhaseCompiler) →
  (fractranCompiler : PhaseFractranCompiler) →
  (relation : Sheet.RelationSheet3) →
  compileRelation relationCompiler fractranCompiler (Sheet.transposeSheet relation)
  ≡ Context.reciprocal
      (compileRelation relationCompiler fractranCompiler relation)
transposeCompilesToReciprocal relationCompiler fractranCompiler relation
  rewrite transposePhaseLaw relationCompiler relation
  = inversePhaseLaw fractranCompiler
      (selectPhase relationCompiler relation)

record RelationPhaseFractranBoundary : Set where
  constructor relationPhaseFractranBoundary
  field
    relationSheetIsPhaseCarrier : Bool
    phaseCarrierIsFractranFraction : Bool
    transposeAutomaticallyMeansReciprocal : Bool
    explicitIntertwinersSufficeForCommutation : Bool

canonicalRelationPhaseFractranBoundary : RelationPhaseFractranBoundary
canonicalRelationPhaseFractranBoundary =
  relationPhaseFractranBoundary false false false true
