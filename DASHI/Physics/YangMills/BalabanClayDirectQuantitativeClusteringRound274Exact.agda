{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayDirectQuantitativeClusteringRound274Exact where

------------------------------------------------------------------------
-- ROUND274 / QUANTITATIVE CLUSTERING MUST NOT HIDE INSIDE T5 METADATA
--
-- `FiniteToContinuumOSClosure` is intentionally generic: it accepts an arbitrary
-- predicate `Clustered : Schwinger -> Set` and an inhabitant `continuumClustered`.
-- The quantitative T5 compiler likewise takes that inhabitant as an INPUT.
-- Therefore the mere existence of a T5 closure record does not prove the
-- physical exponential-clustering theorem needed for the mass gap.
--
-- The spectral consumer already exposes the correct primitive theorem:
--
--   ClusteringUpperBound spectrum
--
-- together with positivity of the candidate gap.  This owner makes that direct
-- route canonical and bypasses the opaque `Clustered` label entirely.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record DirectQuantitativeContinuumClustering
    {Observable Energy Bound : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound) : Set₁ where
  field
    clusteringUpper : Gap.ClusteringUpperBound spectrum
    candidateGapPositive : Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum)

open DirectQuantitativeContinuumClustering public

compileDirectQuantitativeClusteringToTransferGap :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  DirectQuantitativeContinuumClustering spectrum →
  Gap.PositiveTransferGap spectrum
compileDirectQuantitativeClusteringToTransferGap {spectrum = spectrum} payment =
  Gap.positiveTransferGapFromClusteringCutset spectrum
    (clusteringUpper payment)
    (candidateGapPositive payment)

data OpaqueT5ClusteredFieldCreatesQuantitativeClusteringPermission : Set where

opaqueT5ClusteredDoesNotCreateQuantitativeClustering :
  OpaqueT5ClusteredFieldCreatesQuantitativeClusteringPermission → ⊥
opaqueT5ClusteredDoesNotCreateQuantitativeClustering ()

record Round274Boundary : Set where
  constructor round274-boundary
  field
    genericT5ContinuumClusteredFieldPaysMassGapClustering : Bool
    genericT5ContinuumClusteredFieldPaysMassGapClusteringIsFalse :
      genericT5ContinuumClusteredFieldPaysMassGapClustering ≡ false

    quantitativeClusteringUpperIsCanonicalBConsumer : Bool
    quantitativeClusteringUpperIsCanonicalBConsumerIsTrue :
      quantitativeClusteringUpperIsCanonicalBConsumer ≡ true

    t5MayCarryQuantitativeClusteringAfterProof : Bool
    t5MayCarryQuantitativeClusteringAfterProofIsTrue :
      t5MayCarryQuantitativeClusteringAfterProof ≡ true

    heatDoobLangevinRouteMandatory : Bool
    heatDoobLangevinRouteMandatoryIsFalse :
      heatDoobLangevinRouteMandatory ≡ false

    theoremContentClosedHere : Bool
    theoremContentClosedHereIsFalse : theoremContentClosedHere ≡ false

canonicalRound274Boundary : Round274Boundary
canonicalRound274Boundary =
  round274-boundary false refl true refl true refl false refl false refl

round274DirectQuantitativeClusteringCompilerLevel : ProofLevel
round274DirectQuantitativeClusteringCompilerLevel = machineChecked

round274PhysicalQuantitativeClusteringLevel : ProofLevel
round274PhysicalQuantitativeClusteringLevel = conditional
