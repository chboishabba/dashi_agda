module DASHI.Analysis.NonArchimedeanMonster3BResidualFactorizationExact where

------------------------------------------------------------------------
-- MONSTER 3B RESIDUAL FACTORIZATION OVER THE SOURCE-17 DYADIC BULK
--
-- Existing arithmetic gives
--
--   (65663,65610,65610)
--     = 65536(1,1,1) + (127,74,74).
--
-- The residual itself factors as
--
--   (127,74,74) = 74(1,1,1) + (53,0,0),
--
-- hence
--
--   275 = 222 + 53.
--
-- This separates a phase-uniform correction from the actual C3 character
-- imbalance.  The source dyadic bulk therefore sits one layer below the
-- familiar 65610-balanced regular bulk.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as M3B
import DASHI.Analysis.NonArchimedeanMonster3BPhaseBulkHypervoxelExact as Bulk

uniform74 : M3B.ThreePhaseMultiplicity
uniform74 = M3B.threePhaseMultiplicity 74 74 74

character53 : M3B.ThreePhaseMultiplicity
character53 = M3B.threePhaseMultiplicity 53 0 0

residualFactorsUniformPlusCharacter :
  Bulk.addPhase uniform74 character53 ≡ Bulk.monster3BResidualFibre
residualFactorsUniformPlusCharacter = refl

uniform74Dimension : Nat
uniform74Dimension = M3B.phaseDimension uniform74

uniform74DimensionIs222 : uniform74Dimension ≡ 222
uniform74DimensionIs222 = refl

character53Dimension : Nat
character53Dimension = M3B.phaseDimension character53

character53DimensionIs53 : character53Dimension ≡ 53
character53DimensionIs53 = refl

residual275FactorsAs222Plus53 :
  uniform74Dimension + character53Dimension ≡ Bulk.monster3BResidualDimension
residual275FactorsAs222Plus53 = refl

------------------------------------------------------------------------
-- Balanced bulk reached after the uniform correction.
------------------------------------------------------------------------

source17PlusUniform74 : M3B.ThreePhaseMultiplicity
source17PlusUniform74 = Bulk.addPhase Bulk.source17ReplicatedBulk uniform74

source17PlusUniform74IsBalanced65610 :
  source17PlusUniform74 ≡
  M3B.threePhaseMultiplicity 65610 65610 65610
source17PlusUniform74IsBalanced65610 = refl

balanced65610Plus53IsMonsterW3B :
  Bulk.addPhase source17PlusUniform74 character53 ≡ M3B.monsterW3B
balanced65610Plus53IsMonsterW3B = refl

record ResidualFactorizationBoundary : Set where
  constructor residual-factorization-boundary
  field
    dyadicBulkExplainsFullMonsterResidual : Bool
    uniformCorrectionIsCharacterDefect : Bool
    characterDefectLivesAfterBalancedCorrection : Bool
    arithmeticFactorizationImpliesInvariantSubmoduleSplit : Bool
    arithmeticFactorizationSuggestsSearchCoordinates : Bool

canonicalResidualFactorizationBoundary : ResidualFactorizationBoundary
canonicalResidualFactorizationBoundary =
  residual-factorization-boundary
    false false true false true

------------------------------------------------------------------------
-- BIDI search consequence:
--
-- If the consumer asks specifically for the 3B character defect, searching
-- the already-balanced 2^16 bulk is insufficient.  The live producer is the
-- residual action/character after the uniform 74-per-phase correction.
------------------------------------------------------------------------

data ResidualProducer : Set where
  dyadicBulkProducer : ResidualProducer
  uniformPhaseCorrectionProducer : ResidualProducer
  characterResidualProducer : ResidualProducer
  actualRepresentationRecognitionProducer : ResidualProducer

characterDefectSearchPath : List ResidualProducer
characterDefectSearchPath =
  dyadicBulkProducer ∷
  uniformPhaseCorrectionProducer ∷
  characterResidualProducer ∷
  actualRepresentationRecognitionProducer ∷
  []
