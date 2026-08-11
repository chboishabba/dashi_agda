module DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionCongruenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Prove pointwise congruence of the actual selected mean-zero projection and
-- its constant complement without using function extensionality.  This is the
-- congruence bridge needed by the finite padded normal inverse.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionOrthogonalityExact as Projection

scalarMeanRespectsPointwise : ∀ left right →
  (∀ site → left site ≡ right site) →
  Mean.scalarMean left ≡ Mean.scalarMean right
scalarMeanRespectsPointwise left right pointwise =
  cong (GlobalAverage.oneTwoFiftySix *_)
    (Periodic.sumSitesCong left right pointwise)

scalarCenteredRespectsPointwise : ∀ left right →
  (∀ site → left site ≡ right site) →
  ∀ site → Mean.scalarCentered left site ≡ Mean.scalarCentered right site
scalarCenteredRespectsPointwise left right pointwise site =
  cong₂ _-_ (pointwise site) (scalarMeanRespectsPointwise left right pointwise)

scalarConstantRespectsPointwise : ∀ left right →
  (∀ site → left site ≡ right site) →
  ∀ site →
  Mean.scalarConstantProjection left site
  ≡ Mean.scalarConstantProjection right site
scalarConstantRespectsPointwise left right pointwise site =
  scalarMeanRespectsPointwise left right pointwise

selectedProjectionRespectsPointwise : ∀ left right →
  (∀ row → left row ≡ right row) →
  ∀ row →
  Projection.selectedReducedProjection left row
  ≡ Projection.selectedReducedProjection right row
selectedProjectionRespectsPointwise left right pointwise
    (Combined.averageConstraintRow row) =
  pointwise (Combined.averageConstraintRow row)
selectedProjectionRespectsPointwise left right pointwise
    (Combined.gaugeConstraintRow (pair coordinate site)) =
  scalarCenteredRespectsPointwise
    (FlatFloor.gaugeMultiplierField (Split.gaugePart left) coordinate)
    (FlatFloor.gaugeMultiplierField (Split.gaugePart right) coordinate)
    (λ current → pointwise
      (Combined.gaugeConstraintRow (pair coordinate current)))
    site

selectedComplementRespectsPointwise : ∀ left right →
  (∀ row → left row ≡ right row) →
  ∀ row →
  Projection.selectedConstantComplement left row
  ≡ Projection.selectedConstantComplement right row
selectedComplementRespectsPointwise left right pointwise
    (Combined.averageConstraintRow row) =
  Agda.Builtin.Equality.refl
selectedComplementRespectsPointwise left right pointwise
    (Combined.gaugeConstraintRow (pair coordinate site)) =
  scalarConstantRespectsPointwise
    (FlatFloor.gaugeMultiplierField (Split.gaugePart left) coordinate)
    (FlatFloor.gaugeMultiplierField (Split.gaugePart right) coordinate)
    (λ current → pointwise
      (Combined.gaugeConstraintRow (pair coordinate current)))
    site

selectedProjectionPointwiseCongruenceLevel : ProofLevel
selectedProjectionPointwiseCongruenceLevel = machineChecked
