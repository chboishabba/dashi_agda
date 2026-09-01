module DASHI.Cognition.PNF.SemanticAntisymmetricRelationFractranIntertwinerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.ConsumerRelationSheetFractranQuotientBidiExact as Sheet
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- Concrete repair of the relation -> phase -> FRACTRAN seam.
--
-- Transpose by itself does not imply sign inversion for an arbitrary ternary
-- sheet.  The law is valid on an antisymmetric oriented relation sheet.  This
-- owner selects the literal A->B edge and compiles its phase to one signed SSP
-- prime lane, giving an inhabited reciprocal intertwiner.
------------------------------------------------------------------------

transposeSheet : Sheet.RelationSheet3 → Sheet.RelationSheet3
transposeSheet (Sheet.relationSheet3 relation diagonalA diagonalB diagonalC) =
  Sheet.relationSheet3
    (λ left right → relation right left)
    diagonalA diagonalB diagonalC

transposeSheetInvolutive :
  (relation : Sheet.RelationSheet3) →
  transposeSheet (transposeSheet relation) ≡ relation
transposeSheetInvolutive (Sheet.relationSheet3 relation diagonalA diagonalB diagonalC) = refl

selectABPhase : Sheet.RelationSheet3 → Trit.SSPTrit
selectABPhase relation = Sheet.relation relation Sheet.roleA Sheet.roleB

antisymmetricTransposeInvertsABPhase :
  (relation : Sheet.AntisymmetricSheet) →
  selectABPhase (transposeSheet (Sheet.sheet relation))
  ≡ Context.negateTrit (selectABPhase (Sheet.sheet relation))
antisymmetricTransposeInvertsABPhase relation =
  Sheet.converseNegates relation Sheet.roleB Sheet.roleA

singleLanePhaseFraction : Signed.SSPPrime → Trit.SSPTrit → Context.FractranFraction
singleLanePhaseFraction prime Trit.sspNegOne =
  Context.fractranFraction [] (prime ∷ [])
singleLanePhaseFraction prime Trit.sspZero =
  Context.fractranFraction [] []
singleLanePhaseFraction prime Trit.sspPosOne =
  Context.fractranFraction (prime ∷ []) []

singleLaneNegationIsReciprocal :
  (prime : Signed.SSPPrime) →
  (phase : Trit.SSPTrit) →
  singleLanePhaseFraction prime (Context.negateTrit phase)
  ≡ Context.reciprocal (singleLanePhaseFraction prime phase)
singleLaneNegationIsReciprocal prime Trit.sspNegOne = refl
singleLaneNegationIsReciprocal prime Trit.sspZero = refl
singleLaneNegationIsReciprocal prime Trit.sspPosOne = refl

compileABRelation :
  Signed.SSPPrime → Sheet.RelationSheet3 → Context.FractranFraction
compileABRelation prime relation =
  singleLanePhaseFraction prime (selectABPhase relation)

antisymmetricTransposeCompilesToReciprocal :
  (prime : Signed.SSPPrime) →
  (relation : Sheet.AntisymmetricSheet) →
  compileABRelation prime (transposeSheet (Sheet.sheet relation))
  ≡ Context.reciprocal (compileABRelation prime (Sheet.sheet relation))
antisymmetricTransposeCompilesToReciprocal prime relation
  rewrite antisymmetricTransposeInvertsABPhase relation =
  singleLaneNegationIsReciprocal prime (selectABPhase (Sheet.sheet relation))

record AntisymmetricRelationFractranBoundary : Set where
  constructor antisymmetricRelationFractranBoundary
  field
    arbitraryTransposeImpliesPhaseInverse : Bool
    antisymmetrySuppliesPhaseInverse : Bool
    selectedPhaseCanCompileToOnePrimeLane : Bool
    phaseNegationCompilesToReciprocal : Bool
    reciprocalIsAutomaticallyLawfulSemanticInverse : Bool

canonicalAntisymmetricRelationFractranBoundary :
  AntisymmetricRelationFractranBoundary
canonicalAntisymmetricRelationFractranBoundary =
  antisymmetricRelationFractranBoundary false true true true false
