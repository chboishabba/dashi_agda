module DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Replace the invalid "delete three rows" reading of the raw 780-row
-- constraint by a split exact presentation.  The twelve average coordinates
-- are retained literally.  The 768 gauge-multiplier coordinates are projected
-- to their componentwise-mean-zero representative, i.e. the quotient by the
-- three flat constant directions.  The reopening map remembers the original
-- tagged row presentation.
--
-- Thus every raw multiplier has
--
--     raw --reduce--> reduced --reopen--> raw,
--
-- where reopen(reduce(raw)) is the canonical projector P, P^2=P, and its
-- kernel is exactly "zero average part + constant gauge part".  Conversely a
-- reduced multiplier is fixed pointwise by reduce after reopening.  This is a
-- computational quotient presentation; it is not a claim that the nonlinear
-- physical stabilizer is globally the flat three-dimensional constant sector.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPath4PhysicalFibreMatchExact as Indices
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact as Variance
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean

SelectedMultiplier : Set
SelectedMultiplier = Combined.SelectedConstraintRow4 → ℚ

AverageMultiplier : Set
AverageMultiplier = Average.SelectedBlockAverageRow4 → ℚ

GaugeMultiplier : Set
GaugeMultiplier = FlatFloor.GaugeMultiplier

averagePart : SelectedMultiplier → AverageMultiplier
averagePart multiplier row = multiplier (Combined.averageConstraintRow row)

gaugePart : SelectedMultiplier → GaugeMultiplier
gaugePart multiplier row = multiplier (Combined.gaugeConstraintRow row)

------------------------------------------------------------------------
-- A mean-zero gauge multiplier is a concrete section of the flat constant
-- quotient.  First prove that centering fixes every already-reduced point.
------------------------------------------------------------------------

baseSite : Periodic.Site4
baseSite =
  pair (pair Indices.index0 Indices.index0)
    (pair Indices.index0 Indices.index0)

scalarMeanZeroFromGlobalMeanZero :
  ∀ field → Variance.GlobalMeanZero4 field →
  Mean.scalarMean field ≡ 0ℚ
scalarMeanZeroFromGlobalMeanZero field meanZero =
  trans
    (cong (GlobalAverage.oneTwoFiftySix *_)
      (Bridge.sumSitesMatchesGlobalSiteSum field))
    (trans
      (sym (GlobalAverage.average0123EqualsGlobalMean field baseSite))
      (meanZero baseSite))

reducedCoordinateMeanZero :
  ∀ multiplier → FlatFloor.FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate →
  Variance.GlobalMeanZero4
    (FlatFloor.gaugeMultiplierField multiplier coordinate)
reducedCoordinateMeanZero multiplier reduced Coordinates.coordinateX =
  FlatFloor.coordinateXMeanZero reduced
reducedCoordinateMeanZero multiplier reduced Coordinates.coordinateY =
  FlatFloor.coordinateYMeanZero reduced
reducedCoordinateMeanZero multiplier reduced Coordinates.coordinateZ =
  FlatFloor.coordinateZMeanZero reduced

constantProjectionReducedZero :
  ∀ multiplier → FlatFloor.FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate site →
  Mean.constantProjection multiplier (pair coordinate site) ≡ 0ℚ
constantProjectionReducedZero multiplier reduced coordinate site =
  scalarMeanZeroFromGlobalMeanZero
    (FlatFloor.gaugeMultiplierField multiplier coordinate)
    (reducedCoordinateMeanZero multiplier reduced coordinate)

centeredMultiplierFixesReduced :
  ∀ multiplier → FlatFloor.FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate site →
  Mean.centeredMultiplier multiplier (pair coordinate site)
  ≡ multiplier (pair coordinate site)
centeredMultiplierFixesReduced multiplier reduced coordinate site =
  trans
    (cong
      (multiplier (pair coordinate site) -_)
      (constantProjectionReducedZero multiplier reduced coordinate site))
    (ℚRing.solve-∀ (multiplier (pair coordinate site)))

------------------------------------------------------------------------
-- Reduced tagged multiplier and split maps.
------------------------------------------------------------------------

record SelectedReducedCombinedMultiplier : Set where
  constructor selectedReducedCombinedMultiplier
  field
    averageMultiplier : AverageMultiplier
    gaugeMultiplier : GaugeMultiplier
    gaugeReduced : FlatFloor.FlatGaugeReducedMultiplier gaugeMultiplier

open SelectedReducedCombinedMultiplier public

reduceSelectedMultiplier :
  SelectedMultiplier → SelectedReducedCombinedMultiplier
reduceSelectedMultiplier multiplier =
  selectedReducedCombinedMultiplier
    (averagePart multiplier)
    (Mean.centeredMultiplier (gaugePart multiplier))
    (Mean.centeredMultiplierReduced (gaugePart multiplier))

reopenReducedMultiplier :
  SelectedReducedCombinedMultiplier → SelectedMultiplier
reopenReducedMultiplier selected (Combined.averageConstraintRow row) =
  averageMultiplier selected row
reopenReducedMultiplier selected (Combined.gaugeConstraintRow row) =
  gaugeMultiplier selected row

selectedCombinedReducedProjection : SelectedMultiplier → SelectedMultiplier
selectedCombinedReducedProjection multiplier =
  reopenReducedMultiplier (reduceSelectedMultiplier multiplier)

selectedCombinedReducedProjectionAverageExact :
  ∀ multiplier row →
  selectedCombinedReducedProjection multiplier
    (Combined.averageConstraintRow row)
  ≡ multiplier (Combined.averageConstraintRow row)
selectedCombinedReducedProjectionAverageExact multiplier row = refl

selectedCombinedReducedProjectionGaugeExact :
  ∀ multiplier row →
  selectedCombinedReducedProjection multiplier
    (Combined.gaugeConstraintRow row)
  ≡ Mean.centeredMultiplier (gaugePart multiplier) row
selectedCombinedReducedProjectionGaugeExact multiplier row = refl

------------------------------------------------------------------------
-- q o s = I on the reduced representative, pointwise and proof-relevantly.
------------------------------------------------------------------------

reduceAfterReopenAverageExact :
  ∀ selected row →
  averageMultiplier
    (reduceSelectedMultiplier (reopenReducedMultiplier selected)) row
  ≡ averageMultiplier selected row
reduceAfterReopenAverageExact selected row = refl

reduceAfterReopenGaugeExact :
  ∀ selected coordinate site →
  gaugeMultiplier
    (reduceSelectedMultiplier (reopenReducedMultiplier selected))
    (pair coordinate site)
  ≡ gaugeMultiplier selected (pair coordinate site)
reduceAfterReopenGaugeExact selected coordinate site =
  centeredMultiplierFixesReduced
    (gaugeMultiplier selected) (gaugeReduced selected) coordinate site

reopenReduceProjectionIdempotent :
  ∀ multiplier row →
  selectedCombinedReducedProjection
    (selectedCombinedReducedProjection multiplier) row
  ≡ selectedCombinedReducedProjection multiplier row
reopenReduceProjectionIdempotent multiplier
    (Combined.averageConstraintRow row) = refl
reopenReduceProjectionIdempotent multiplier
    (Combined.gaugeConstraintRow (pair coordinate site)) =
  reduceAfterReopenGaugeExact
    (reduceSelectedMultiplier multiplier) coordinate site

------------------------------------------------------------------------
-- Exact kernel: the projector kills precisely the flat presentation
-- redundancy, not a guessed background stabilizer.
------------------------------------------------------------------------

record SelectedCombinedConstantGaugeRedundancy
    (multiplier : SelectedMultiplier) : Set where
  field
    averagePartZero : ∀ row → averagePart multiplier row ≡ 0ℚ
    gaugeCenteredPartZero : ∀ row →
      Mean.centeredMultiplier (gaugePart multiplier) row ≡ 0ℚ

open SelectedCombinedConstantGaugeRedundancy public

selectedCombinedReducedProjectionKernelForward :
  ∀ multiplier →
  (∀ row → selectedCombinedReducedProjection multiplier row ≡ 0ℚ) →
  SelectedCombinedConstantGaugeRedundancy multiplier
selectedCombinedReducedProjectionKernelForward multiplier projectionZero =
  record
    { averagePartZero = λ row →
        projectionZero (Combined.averageConstraintRow row)
    ; gaugeCenteredPartZero = λ row →
        projectionZero (Combined.gaugeConstraintRow row)
    }

selectedCombinedReducedProjectionKernelBackward :
  ∀ multiplier →
  SelectedCombinedConstantGaugeRedundancy multiplier →
  ∀ row → selectedCombinedReducedProjection multiplier row ≡ 0ℚ
selectedCombinedReducedProjectionKernelBackward multiplier redundancy
    (Combined.averageConstraintRow row) =
  averagePartZero redundancy row
selectedCombinedReducedProjectionKernelBackward multiplier redundancy
    (Combined.gaugeConstraintRow row) =
  gaugeCenteredPartZero redundancy row

centeredZeroImpliesGaugeIsConstantProjection :
  ∀ multiplier →
  (∀ row → Mean.centeredMultiplier (gaugePart multiplier) row ≡ 0ℚ) →
  ∀ coordinate site →
  gaugePart multiplier (pair coordinate site)
  ≡ Mean.constantProjection (gaugePart multiplier) (pair coordinate site)
centeredZeroImpliesGaugeIsConstantProjection multiplier centeredZero coordinate site =
  let
    split = Mean.multiplierSplitsPointwise
      (gaugePart multiplier) coordinate site
  in
  trans split
    (trans
      (cong
        (_+ Mean.constantProjection (gaugePart multiplier)
              (pair coordinate site))
        (centeredZero (pair coordinate site)))
      (ℚRing.solve-∀
        (Mean.constantProjection (gaugePart multiplier)
          (pair coordinate site))))

selectedCombinedMultiplierSplitLevel : ProofLevel
selectedCombinedMultiplierSplitLevel = machineChecked

selectedCombinedReducedProjectionLevel : ProofLevel
selectedCombinedReducedProjectionLevel = machineChecked

selectedCombinedReducedKernelLevel : ProofLevel
selectedCombinedReducedKernelLevel = machineChecked
