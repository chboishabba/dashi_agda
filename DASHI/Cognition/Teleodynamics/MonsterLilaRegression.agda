module DASHI.Cognition.Teleodynamics.MonsterLilaRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.MonsterLilaBoundaryExact as M

permutationIsNotPromotedToConwayElement :
  M.conwayGroupElementEstablished M.canonicalMonsterLilaBoundary ≡ false
permutationIsNotPromotedToConwayElement = refl

fineStructureModulationIsNotMonsterRepresentation :
  M.monsterRepresentationEstablished M.canonicalMonsterLilaBoundary ≡ false
fineStructureModulationIsNotMonsterRepresentation = refl

svdMonitorIsNotMoonshineTheorem :
  M.moonshineRealizationEstablished M.canonicalMonsterLilaBoundary ≡ false
svdMonitorIsNotMoonshineTheorem = refl

literalHeuristicOperationsRecorded :
  M.literalComputationalHeuristicsRecorded M.canonicalMonsterLilaBoundary ≡ true
literalHeuristicOperationsRecorded = refl
