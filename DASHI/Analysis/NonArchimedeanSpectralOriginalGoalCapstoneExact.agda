module DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact where

------------------------------------------------------------------------
-- ORIGINAL-GOAL CAPSTONE
--
-- Return the tranche to the theorem-bearing finite non-Archimedean spectral
-- dynamics that motivated the audit.  Monster correspondence is useful
-- x-pollination but not a prerequisite here.
--
-- After reusing finite matrix-action faithfulness, the source-exact closure
-- graph is now:
--
--  D_n function-level character action       [OWNED]
--  D_n preserves tau-odd functions           [OWNED]
--      |
--      +-> odd character <-> tau-odd          [LIVE]
--      |
--  order(3)=2^(n-2)                           [OWNED]
--  odd residue cardinality                    [OWNED]
--      |
--      +-> arithmetic orbit chart
--          (j,0)->3^j ; (j,1)->-3^j           [HIGHEST-ALPHA LIVE]
--          -> canonical C1,C2 package         [DOWNSTREAM]
--          -> |W_C|^2=2                       [OWNED CONDITIONAL]
--          -> W1*W2=2                         [OWNED CONDITIONAL]
--          -> phase/sign W_i                  [LIVE]
--
--  concrete twistedDirMatrix                  [OWNED]
--      -> Hadamard twisted-sector split       [OWNED]
--      -> concrete DFT carrier/reindex         [OWNED]
--      -> DFT-conjugated matrix                [OWNED OBJECT]
--      -> twisted coordinates <-> odd chars    [LIVE]
--      -> equality on complete character basis [DOWNSTREAM]
--      -> matrix equality by repo faithfulness [COMPILER / OWNED GENERIC]
--             |               |               |
--             v               v               v
--       spatial spectrum  spatial trace   spatial powers
--
-- Separately, the one-step determinant cover factorization is OWNED, while the
-- theorem named `spectral_tower_one_step` has only `True` as its formal type;
-- literal recursive spectrum-union transport remains a small downstream weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data OriginalGoalLeaf : Set where
  oddCharacterTauOddIff : OriginalGoalLeaf
  arithmeticOddOrbitChart : OriginalGoalLeaf
  twistedCoordinateCharacterIdentification : OriginalGoalLeaf
  completeCharacterBasisActionEquality : OriginalGoalLeaf
  concreteDFTConjugatedEqualsMonomial : OriginalGoalLeaf
  canonicalTwoOddOrbitPackage : OriginalGoalLeaf
  orbitPhaseSign : OriginalGoalLeaf
  literalOneStepSpectrumUnion : OriginalGoalLeaf


data OriginalGoalStatus : Set where
  owned : OriginalGoalStatus
  live : OriginalGoalStatus
  downstream : OriginalGoalStatus
  pruned : OriginalGoalStatus
  compiled : OriginalGoalStatus

leafStatus : OriginalGoalLeaf → OriginalGoalStatus
leafStatus oddCharacterTauOddIff = live
leafStatus arithmeticOddOrbitChart = live
leafStatus twistedCoordinateCharacterIdentification = live
leafStatus completeCharacterBasisActionEquality = downstream
leafStatus concreteDFTConjugatedEqualsMonomial = compiled
leafStatus canonicalTwoOddOrbitPackage = downstream
leafStatus orbitPhaseSign = live
leafStatus literalOneStepSpectrumUnion = downstream

priority : List OriginalGoalLeaf
priority =
  arithmeticOddOrbitChart ∷
  oddCharacterTauOddIff ∷
  twistedCoordinateCharacterIdentification ∷
  completeCharacterBasisActionEquality ∷
  orbitPhaseSign ∷
  literalOneStepSpectrumUnion ∷
  []

record SharedWeldFanout : Set where
  constructor sharedWeldFanout
  field
    sameConcreteMatrixWeldFeedsSpatialSpectrum : Bool
    sameConcreteMatrixWeldFeedsSpatialTrace : Bool
    sameConcreteMatrixWeldFeedsSpatialPower : Bool
    equalityOnBasisCompilesLiteralMatrixEquality : Bool
    threeIndependentMatrixWeldsShouldBeSearched : Bool

canonicalSharedWeldFanout : SharedWeldFanout
canonicalSharedWeldFanout =
  sharedWeldFanout true true true true false

record OriginalGoalBoundary : Set where
  constructor originalGoalBoundary
  field
    functionLevelCharacterActionOwned : Bool
    tauOddPreservationOwned : Bool
    finiteMatrixBasisFaithfulnessOwned : Bool
    monomialPowerCalculusOwned : Bool
    orbitOrderOwned : Bool
    oddCardinalityOwned : Bool
    conditionalOrbitMagnitudeOwned : Bool
    conditionalPairedProductOwned : Bool
    concreteHadamardSplitOwned : Bool
    concreteDFTInfrastructureOwned : Bool
    determinantTowerFactorizationOwned : Bool

    oddCharacterTauOddIffOwned : Bool
    arithmeticOrbitChartOwned : Bool
    twistedCoordinateCharacterIdentificationOwned : Bool
    concreteDFTMonomialEqualityCompiledOnceInputsExist : Bool
    orbitPhaseSignOwned : Bool
    literalSpectrumTowerOwned : Bool

    monsterCorrespondenceRequiredForSpectralClosure : Bool
    finalMagnitudeHypothesisMayCloseItsOwnProducerPath : Bool

canonicalOriginalGoalBoundary : OriginalGoalBoundary
canonicalOriginalGoalBoundary =
  originalGoalBoundary
    true true true true true true true true true true true
    false false false true false false
    false false

monsterIsOptionalForOriginalClosure :
  OriginalGoalBoundary.monsterCorrespondenceRequiredForSpectralClosure
    canonicalOriginalGoalBoundary
  ≡ false
monsterIsOptionalForOriginalClosure = refl

matrixEqualityIsCompilerOutputOnceSemanticInputsExist :
  OriginalGoalBoundary.concreteDFTMonomialEqualityCompiledOnceInputsExist
    canonicalOriginalGoalBoundary
  ≡ true
matrixEqualityIsCompilerOutputOnceSemanticInputsExist = refl

finalMagnitudeCannotSelfDischarge :
  OriginalGoalBoundary.finalMagnitudeHypothesisMayCloseItsOwnProducerPath
    canonicalOriginalGoalBoundary
  ≡ false
finalMagnitudeCannotSelfDischarge = refl
