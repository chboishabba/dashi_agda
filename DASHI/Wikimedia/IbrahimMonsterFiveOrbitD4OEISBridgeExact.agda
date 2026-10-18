module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4OEISBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4N3BCharacterAcquisitionExact as N3B
import DASHI.Wikimedia.IbrahimMonster42ClassEtaFamilyOEISAcquisitionExact as Eta42

------------------------------------------------------------------------
-- FIVE-ORBIT D4 / OEIS CLASS-42 BRIDGE ACQUISITION
--
-- The theorem-shaped kernel lane already owns the five-orbit permutation
-- character
--
--   (5,5,1,3,3) = 3 A1 + B1 + B2,
--
-- and independently the N(3B) acquisition lane has localized the same-action
-- subgroup/restriction debt.  Fresh OEIS acquisition for A058674 (Monster
-- class 42D) exposes a local coefficient tail 1,3,3 while its eta quotient
-- carries the source-native 14/42 levels.
--
-- This owner retains that 1,3,3 overlap only as a low-authority snowball
-- coordinate.  It is NOT a character comparison: sequence position, class
-- function semantics, subgroup restriction and same-action identity are all
-- still independent obligations.
------------------------------------------------------------------------

n3bBoundary : N3B.FiveOrbitD4N3BAcquisitionBoundary
n3bBoundary = N3B.currentFiveOrbitD4N3BAcquisitionBoundary

eta42Boundary : Eta42.Monster42ClassEtaFamilyBoundary
eta42Boundary = Eta42.currentMonster42ClassEtaFamilyBoundary

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data OEISTailEchoCreatesD4CharacterIdentity : Set where
data OEISTailEchoCreatesN3BRestriction : Set where
data MatchingOneThreeThreeCreatesSameObject : Set where

oeisTailEchoDoesNotCreateD4CharacterIdentity :
  OEISTailEchoCreatesD4CharacterIdentity → ⊥
oeisTailEchoDoesNotCreateD4CharacterIdentity ()

oeisTailEchoDoesNotCreateN3BRestriction :
  OEISTailEchoCreatesN3BRestriction → ⊥
oeisTailEchoDoesNotCreateN3BRestriction ()

matchingOneThreeThreeDoesNotCreateSameObject :
  MatchingOneThreeThreeCreatesSameObject → ⊥
matchingOneThreeThreeDoesNotCreateSameObject ()

------------------------------------------------------------------------
-- Acquisition boundary.
------------------------------------------------------------------------

record FiveOrbitD4OEISBridgeBoundary : Set where
  constructor five-orbit-d4-oeis-bridge-boundary
  field
    kernelD4CharacterPaid : Bool
    kernelD4IrrepDecompositionPaid : Bool
    n3bSameActionFrontierLocated : Bool
    oeis42DSourcePaid : Bool
    oeis42DEta14And42SourcePaid : Bool
    oeis42DTailEchoRetained : Bool
    oeisTailEchoUsedAsSearchPriorityOnly : Bool
    d4SubgroupEmbeddingPaid : Bool
    d4QuotientEqualsN3BCharacter : Bool
    oeisTailEchoCreatesCharacterIdentity : Bool
    oeisTailEchoCreatesMonsterAction : Bool
    nextResidual : String
open FiveOrbitD4OEISBridgeBoundary public

currentFiveOrbitD4OEISBridgeBoundary : FiveOrbitD4OEISBridgeBoundary
currentFiveOrbitD4OEISBridgeBoundary =
  five-orbit-d4-oeis-bridge-boundary
    true true true true true true true
    false false false false
    "Use the exact five-orbit D4 character (5,5,1,3,3)=3*A1+B1+B2 and the existing N(3B) same-action acquisition frontier as the proof-producing route. Retain the A058674 local coefficient tail 1,3,3 and eta levels 14/42 only as OEIS search coordinates: next seek a source-paid D4 subgroup/class-fusion inside the SAME selected 3B normalizer action, then compare the restricted Monster character. Do not infer character identity, subgroup embedding, or Monster class-42 action from the OEIS tail."
