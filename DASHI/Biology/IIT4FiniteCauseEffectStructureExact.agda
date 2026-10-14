module DASHI.Biology.IIT4FiniteCauseEffectStructureExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IIT4FiniteCausalStructureExact as IIT4
import DASHI.Biology.IIT4FiniteDistinctionExact as Distinction
import DASHI.Biology.IIT4FiniteRelationExact as Relation

------------------------------------------------------------------------
-- IIT-4 CAUSE-EFFECT / PHI-STRUCTURE SURFACE
--
-- The finite cause-effect structure is the set of retained distinctions plus
-- their positive relations.  Structure integrated information Phi is the sum
-- of their small-phi terms.  It remains definitionally separate from system
-- integrated information phi_s.
------------------------------------------------------------------------

record FiniteCauseEffectStructure
    (system : IIT4.FiniteCausalSystem)
    (Score : Set) : Set₁ where
  constructor finiteCauseEffectStructure
  field
    distinctions : List (Distinction.FiniteDistinction system Score)
    relations : List (Relation.FiniteRelation system Score)
    sumDistinctionPhi : Score
    sumRelationPhi : Score
    bigPhi : Score
    distinctionSumReceipt : String
    relationSumReceipt : String
    bigPhiSumReceipt : String

open FiniteCauseEffectStructure public

record PhiStructureCalibrationReceipt : Set where
  constructor phiStructureCalibrationReceipt
  field
    sourceLabel : String
    systemPhiRounded : String
    distinctionCount : Nat
    distinctionPhiRounded : List String
    relationCount : Nat
    selectedRelationPhiRounded : String
    bigPhiRounded : String
    calibrationReceipt : String

open PhiStructureCalibrationReceipt public

-- External regression oracle only: current PyPhi worked example reproducing
-- Albantakis et al. (2023), complex aB in state aBC.
workedExampleCalibration : PhiStructureCalibrationReceipt
workedExampleCalibration =
  phiStructureCalibrationReceipt
    "Albantakis et al. 2023 Fig.1/2/4; current PyPhi worked example"
    "0.17"
    3
    ("0.33" ∷ "0.32" ∷ "0.07" ∷ [])
    7
    "about 0.036 (paper display about 0.035 from rounded phi_d)"
    "1.56"
    "scripts/iit4_structure_reference.py records the source-derived regression values"

record IIT4CauseEffectStructureBoundary : Set where
  constructor iit4CauseEffectStructureBoundary
  field
    causeEffectStructureContainsDistinctionsAndRelations : Bool
    bigPhiSumsDistinctionAndRelationPhi : Bool
    systemPhiAndBigPhiAreDefinitionallySame : Bool
    completeStructureCanBeConstructedFromSystemPhiAlone : Bool
    sourceCalibrationIsFreshKernelProof : Bool

open IIT4CauseEffectStructureBoundary public

canonicalIIT4CauseEffectStructureBoundary : IIT4CauseEffectStructureBoundary
canonicalIIT4CauseEffectStructureBoundary =
  iit4CauseEffectStructureBoundary true true false false false

systemPhiIsNotBigPhi :
  systemPhiAndBigPhiAreDefinitionallySame
    canonicalIIT4CauseEffectStructureBoundary ≡ false
systemPhiIsNotBigPhi = refl

systemPhiAloneCannotPopulateStructure :
  completeStructureCanBeConstructedFromSystemPhiAlone
    canonicalIIT4CauseEffectStructureBoundary ≡ false
systemPhiAloneCannotPopulateStructure = refl
