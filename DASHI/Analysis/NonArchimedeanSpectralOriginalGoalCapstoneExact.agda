module DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact where

------------------------------------------------------------------------
-- ORIGINAL-GOAL CAPSTONE
--
-- Return the tranche to the theorem-bearing finite non-Archimedean spectral
-- dynamics that motivated the audit.  Monster correspondence is useful
-- x-pollination but not a prerequisite here.
--
-- The source-exact closure graph is now:
--
--  D_n character action                    [OWNED]
--      |
--      +-> order(3)=2^(n-2)                [OWNED]
--      +-> odd residue cardinality         [OWNED]
--      |     -> canonical C1,C2 package    [LIVE EXPORT]
--      |          -> |W_C|^2=2             [COMPILER FROM OWNED CONDITIONAL]
--      |          -> W1*W2=2               [COMPILER FROM OWNED CONDITIONAL]
--      |          -> phase/sign W_i        [LIVE]
--      |
--  concrete twistedDirMatrix               [OWNED]
--      -> Hadamard twisted-sector split    [OWNED]
--      -> concrete DFT basis/reindex        [OWNED]
--      -> DFT-conjugated matrix             [OWNED]
--      -> equals explicit monomial operator [HIGHEST-ALPHA LIVE]
--             |                |
--             v                v
--       spatial spectrum   spatial trace
--             |                |
--             +------ fanout --+
--
-- Separately, the one-step determinant cover factorization is OWNED, while the
-- theorem named `spectral_tower_one_step` has only `True` as its formal type;
-- literal recursive spectrum-union transport remains a small downstream weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data OriginalGoalLeaf : Set where
  canonicalTwoOddOrbitPackage : OriginalGoalLeaf
  concreteDFTConjugatedEqualsMonomial : OriginalGoalLeaf
  orbitPhaseSign : OriginalGoalLeaf
  literalOneStepSpectrumUnion : OriginalGoalLeaf


data OriginalGoalStatus : Set where
  owned : OriginalGoalStatus
  live : OriginalGoalStatus
  downstream : OriginalGoalStatus
  pruned : OriginalGoalStatus

leafStatus : OriginalGoalLeaf → OriginalGoalStatus
leafStatus canonicalTwoOddOrbitPackage = live
leafStatus concreteDFTConjugatedEqualsMonomial = live
leafStatus orbitPhaseSign = live
leafStatus literalOneStepSpectrumUnion = downstream

priority : List OriginalGoalLeaf
priority =
  concreteDFTConjugatedEqualsMonomial ∷
  canonicalTwoOddOrbitPackage ∷
  orbitPhaseSign ∷
  literalOneStepSpectrumUnion ∷
  []

record SharedWeldFanout : Set where
  constructor sharedWeldFanout
  field
    sameConcreteMatrixWeldFeedsSpatialSpectrum : Bool
    sameConcreteMatrixWeldFeedsSpatialTrace : Bool
    sameConcreteMatrixWeldFeedsSpatialPower : Bool
    threeIndependentMatrixWeldsShouldBeSearched : Bool

canonicalSharedWeldFanout : SharedWeldFanout
canonicalSharedWeldFanout =
  sharedWeldFanout true true true false

record OriginalGoalBoundary : Set where
  constructor originalGoalBoundary
  field
    characterActionOwned : Bool
    monomialPowerCalculusOwned : Bool
    orbitOrderOwned : Bool
    oddCardinalityOwned : Bool
    conditionalOrbitMagnitudeOwned : Bool
    conditionalPairedProductOwned : Bool
    concreteHadamardSplitOwned : Bool
    concreteDFTInfrastructureOwned : Bool
    determinantTowerFactorizationOwned : Bool

    concreteDFTMonomialEqualityOwned : Bool
    canonicalOrbitPackageOwned : Bool
    orbitPhaseSignOwned : Bool
    literalSpectrumTowerOwned : Bool

    monsterCorrespondenceRequiredForSpectralClosure : Bool
    finalMagnitudeHypothesisMayCloseItsOwnProducerPath : Bool

canonicalOriginalGoalBoundary : OriginalGoalBoundary
canonicalOriginalGoalBoundary =
  originalGoalBoundary
    true true true true true true true true true
    false false false false
    false false

monsterIsOptionalForOriginalClosure :
  OriginalGoalBoundary.monsterCorrespondenceRequiredForSpectralClosure
    canonicalOriginalGoalBoundary
  ≡ false
monsterIsOptionalForOriginalClosure = refl

finalMagnitudeCannotSelfDischarge :
  OriginalGoalBoundary.finalMagnitudeHypothesisMayCloseItsOwnProducerPath
    canonicalOriginalGoalBoundary
  ≡ false
finalMagnitudeCannotSelfDischarge = refl
