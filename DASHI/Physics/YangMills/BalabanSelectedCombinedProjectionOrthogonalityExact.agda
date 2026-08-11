module DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionOrthogonalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers", RAIRO Analyse Numerique 8 (1974),
-- 129--151. No DOI was assigned to the cited article.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Turn the split multiplier presentation into an actual orthogonal finite
-- projection calculus on the literal 780-row carrier.  The selected projector
-- P keeps all twelve average rows and centers each of the three gauge
-- multiplier fields.  Its complementary part C keeps only the three constant
-- gauge means.  We prove pointwise
--
--       lambda = P lambda + C lambda,
--       P(P lambda) = P lambda,
--       C(P lambda) = 0,
--       P(C lambda) = 0,
--
-- prove P and C are rational-linear, and prove the cross orthogonality
--
--       <P lambda , C mu> = 0
--
-- for arbitrary lambda,mu.  This is the exact split needed to pad the reduced
-- normal equation on the already-existing finite 780-coordinate carrier,
-- without deleting rows or pretending the flat constant sector is the generic
-- nonlinear stabilizer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair; map)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact as AverageRows
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split

RawMultiplier : Set
RawMultiplier = Split.SelectedMultiplier

rawAdd : RawMultiplier → RawMultiplier → RawMultiplier
rawAdd left right row = left row + right row

rawScale : ℚ → RawMultiplier → RawMultiplier
rawScale coefficient multiplier row = coefficient * multiplier row

selectedReducedProjection : RawMultiplier → RawMultiplier
selectedReducedProjection = Split.selectedCombinedReducedProjection

selectedConstantComplement : RawMultiplier → RawMultiplier
selectedConstantComplement multiplier (Combined.averageConstraintRow row) = 0ℚ
selectedConstantComplement multiplier (Combined.gaugeConstraintRow row) =
  Mean.constantProjection (Split.gaugePart multiplier) row

------------------------------------------------------------------------
-- Scalar centering/constant-projection linearity.
------------------------------------------------------------------------

scalarMeanAddExact : ∀ left right →
  Mean.scalarMean (λ site → left site + right site)
  ≡ Mean.scalarMean left + Mean.scalarMean right
scalarMeanAddExact left right =
  trans
    (cong (GlobalAverage.oneTwoFiftySix *_)
      (Periodic.sumSitesAdd left right))
    (ℚRing.solve-∀
      GlobalAverage.oneTwoFiftySix
      (Periodic.sumSites left) (Periodic.sumSites right))

scalarMeanScaleExact : ∀ coefficient scalarField →
  Mean.scalarMean (λ site → coefficient * scalarField site)
  ≡ coefficient * Mean.scalarMean scalarField
scalarMeanScaleExact coefficient scalarField =
  trans
    (cong (GlobalAverage.oneTwoFiftySix *_)
      (Periodic.sumSitesScale coefficient scalarField))
    (ℚRing.solve-∀
      GlobalAverage.oneTwoFiftySix coefficient
      (Periodic.sumSites scalarField))

scalarCenteredAddExact : ∀ left right site →
  Mean.scalarCentered (λ current → left current + right current) site
  ≡ Mean.scalarCentered left site + Mean.scalarCentered right site
scalarCenteredAddExact left right site =
  trans
    (cong
      ((left site + right site) -_)
      (scalarMeanAddExact left right))
    (ℚRing.solve-∀
      (left site) (right site)
      (Mean.scalarMean left) (Mean.scalarMean right))

scalarCenteredScaleExact : ∀ coefficient scalarField site →
  Mean.scalarCentered (λ current → coefficient * scalarField current) site
  ≡ coefficient * Mean.scalarCentered scalarField site
scalarCenteredScaleExact coefficient scalarField site =
  trans
    (cong
      (coefficient * scalarField site -_)
      (scalarMeanScaleExact coefficient scalarField))
    (ℚRing.solve-∀ coefficient (scalarField site) (Mean.scalarMean scalarField))

scalarConstantAddExact : ∀ left right site →
  Mean.scalarConstantProjection (λ current → left current + right current) site
  ≡ Mean.scalarConstantProjection left site
      + Mean.scalarConstantProjection right site
scalarConstantAddExact left right site = scalarMeanAddExact left right

scalarConstantScaleExact : ∀ coefficient scalarField site →
  Mean.scalarConstantProjection
    (λ current → coefficient * scalarField current) site
  ≡ coefficient * Mean.scalarConstantProjection scalarField site
scalarConstantScaleExact coefficient scalarField site =
  scalarMeanScaleExact coefficient scalarField

scalarMeanConstantProjectionExact : ∀ scalarField →
  Mean.scalarMean (Mean.scalarConstantProjection scalarField)
  ≡ Mean.scalarMean scalarField
scalarMeanConstantProjectionExact scalarField =
  trans
    (cong (GlobalAverage.oneTwoFiftySix *_)
      (Mean.siteSumConstantExact (Mean.scalarMean scalarField)))
    (ℚRing.solve-∀
      GlobalAverage.oneTwoFiftySix (Mean.scalarMean scalarField))

scalarCenteredConstantProjectionZero : ∀ scalarField site →
  Mean.scalarCentered (Mean.scalarConstantProjection scalarField) site ≡ 0ℚ
scalarCenteredConstantProjectionZero scalarField site =
  trans
    (cong
      (Mean.scalarMean scalarField -_)
      (scalarMeanConstantProjectionExact scalarField))
    (ℚRing.solve-∀ (Mean.scalarMean scalarField))

------------------------------------------------------------------------
-- Exact P/C decomposition and annihilation laws.
------------------------------------------------------------------------

selectedProjectionComplementReconstruct : ∀ multiplier row →
  multiplier row
  ≡ selectedReducedProjection multiplier row
    + selectedConstantComplement multiplier row
selectedProjectionComplementReconstruct multiplier
    (Combined.averageConstraintRow row) =
  ℚRing.solve-∀ (multiplier (Combined.averageConstraintRow row))
selectedProjectionComplementReconstruct multiplier
    (Combined.gaugeConstraintRow (pair coordinate site)) =
  Mean.multiplierSplitsPointwise
    (Split.gaugePart multiplier) coordinate site

selectedProjectionIdempotent : ∀ multiplier row →
  selectedReducedProjection (selectedReducedProjection multiplier) row
  ≡ selectedReducedProjection multiplier row
selectedProjectionIdempotent = Split.reopenReduceProjectionIdempotent

selectedComplementOfProjectionZero : ∀ multiplier row →
  selectedConstantComplement (selectedReducedProjection multiplier) row ≡ 0ℚ
selectedComplementOfProjectionZero multiplier
    (Combined.averageConstraintRow row) = refl
selectedComplementOfProjectionZero multiplier
    (Combined.gaugeConstraintRow (pair coordinate site)) =
  Split.constantProjectionReducedZero
    (Split.gaugeMultiplier (Split.reduceSelectedMultiplier multiplier))
    (Split.gaugeReduced (Split.reduceSelectedMultiplier multiplier))
    coordinate site

selectedProjectionOfComplementZero : ∀ multiplier row →
  selectedReducedProjection (selectedConstantComplement multiplier) row ≡ 0ℚ
selectedProjectionOfComplementZero multiplier
    (Combined.averageConstraintRow row) = refl
selectedProjectionOfComplementZero multiplier
    (Combined.gaugeConstraintRow (pair coordinate site)) =
  trans
    (Split.selectedCombinedReducedProjectionGaugeExact
      (selectedConstantComplement multiplier) (pair coordinate site))
    (scalarCenteredConstantProjectionZero
      (FlatFloor.gaugeMultiplierField (Split.gaugePart multiplier) coordinate)
      site)

------------------------------------------------------------------------
-- P and C are rational-linear on the raw tagged carrier.
------------------------------------------------------------------------

selectedProjectionAddExact : ∀ left right row →
  selectedReducedProjection (rawAdd left right) row
  ≡ rawAdd (selectedReducedProjection left) (selectedReducedProjection right) row
selectedProjectionAddExact left right (Combined.averageConstraintRow row) = refl
selectedProjectionAddExact left right
    (Combined.gaugeConstraintRow (pair coordinate site)) =
  trans
    (Split.selectedCombinedReducedProjectionGaugeExact
      (rawAdd left right) (pair coordinate site))
    (trans
      (scalarCenteredAddExact
        (FlatFloor.gaugeMultiplierField (Split.gaugePart left) coordinate)
        (FlatFloor.gaugeMultiplierField (Split.gaugePart right) coordinate)
        site)
      (cong₂ _+_
        (sym (Split.selectedCombinedReducedProjectionGaugeExact
          left (pair coordinate site)))
        (sym (Split.selectedCombinedReducedProjectionGaugeExact
          right (pair coordinate site)))))

selectedProjectionScaleExact : ∀ coefficient multiplier row →
  selectedReducedProjection (rawScale coefficient multiplier) row
  ≡ rawScale coefficient (selectedReducedProjection multiplier) row
selectedProjectionScaleExact coefficient multiplier
    (Combined.averageConstraintRow row) = refl
selectedProjectionScaleExact coefficient multiplier
    (Combined.gaugeConstraintRow (pair coordinate site)) =
  trans
    (Split.selectedCombinedReducedProjectionGaugeExact
      (rawScale coefficient multiplier) (pair coordinate site))
    (trans
      (scalarCenteredScaleExact coefficient
        (FlatFloor.gaugeMultiplierField (Split.gaugePart multiplier) coordinate)
        site)
      (cong (coefficient *_)
        (sym (Split.selectedCombinedReducedProjectionGaugeExact
          multiplier (pair coordinate site)))))

selectedComplementAddExact : ∀ left right row →
  selectedConstantComplement (rawAdd left right) row
  ≡ rawAdd (selectedConstantComplement left) (selectedConstantComplement right) row
selectedComplementAddExact left right (Combined.averageConstraintRow row) = refl
selectedComplementAddExact left right
    (Combined.gaugeConstraintRow (pair coordinate site)) =
  scalarConstantAddExact
    (FlatFloor.gaugeMultiplierField (Split.gaugePart left) coordinate)
    (FlatFloor.gaugeMultiplierField (Split.gaugePart right) coordinate)
    site

selectedComplementScaleExact : ∀ coefficient multiplier row →
  selectedConstantComplement (rawScale coefficient multiplier) row
  ≡ rawScale coefficient (selectedConstantComplement multiplier) row
selectedComplementScaleExact coefficient multiplier
    (Combined.averageConstraintRow row) = refl
selectedComplementScaleExact coefficient multiplier
    (Combined.gaugeConstraintRow (pair coordinate site)) =
  scalarConstantScaleExact coefficient
    (FlatFloor.gaugeMultiplierField (Split.gaugePart multiplier) coordinate)
    site

------------------------------------------------------------------------
-- Cross orthogonality: centered gauge fields are orthogonal to arbitrary
-- constant gauge fields, not only to their own mean.
------------------------------------------------------------------------

scalarCenteredConstantCrossOrthogonal : ∀ left right →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site →
      Mean.scalarCentered left site
        * Mean.scalarConstantProjection right site)
  ≡ 0ℚ
scalarCenteredConstantCrossOrthogonal left right =
  let
    meanRight = Mean.scalarMean right

    centeredListSumZero :
      Sums.sumRational (Block.physicalBlockSites Path4.side4)
        (Mean.scalarCentered left)
      ≡ 0ℚ
    centeredListSumZero =
      trans
        (sym (Bridge.sumSitesMatchesGlobalSiteSum (Mean.scalarCentered left)))
        (Mean.scalarCenteredSumZero left)
  in
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4) _ _
      (λ site →
        ℚP.*-comm (Mean.scalarCentered left site) meanRight))
    (trans
      (Sums.sumRationalScale meanRight
        (Block.physicalBlockSites Path4.side4)
        (Mean.scalarCentered left))
      (trans
        (cong (meanRight *_) centeredListSumZero)
        (ℚRing.solve-∀ meanRight)))

selectedGaugeProjectionComplementDotZero : ∀ left right →
  Sums.sumRational (Basis.elements Rows.selectedGaugeRowFiniteSelector)
    (λ gaugeRow →
      selectedReducedProjection left (Combined.gaugeConstraintRow gaugeRow)
      * selectedConstantComplement right (Combined.gaugeConstraintRow gaugeRow))
  ≡ 0ℚ
selectedGaugeProjectionComplementDotZero left right =
  trans
    (Fubini.sumCartesian Coordinates.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      (λ gaugeRow →
        selectedReducedProjection left (Combined.gaugeConstraintRow gaugeRow)
        * selectedConstantComplement right (Combined.gaugeConstraintRow gaugeRow)))
    (trans
      (Sums.sumRationalCong Coordinates.lieCoordinates3 _ (λ _ → 0ℚ)
        (λ coordinate →
          scalarCenteredConstantCrossOrthogonal
            (FlatFloor.gaugeMultiplierField (Split.gaugePart left) coordinate)
            (FlatFloor.gaugeMultiplierField (Split.gaugePart right) coordinate)))
      (Fubini.sumRationalZero Coordinates.lieCoordinates3))

selectedProjectionComplementOrthogonal : ∀ left right →
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
    (selectedReducedProjection left) (selectedConstantComplement right)
  ≡ 0ℚ
selectedProjectionComplementOrthogonal left right =
  trans
    (Fubini.sumRationalAppend
      (map Combined.averageConstraintRow
        (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector))
      (map Combined.gaugeConstraintRow
        (Basis.elements Rows.selectedGaugeRowFiniteSelector))
      (λ row →
        selectedReducedProjection left row * selectedConstantComplement right row))
    (trans
      (cong₂ _+_
        (trans
          (Fubini.sumRationalMap Combined.averageConstraintRow
            (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
            (λ row →
              selectedReducedProjection left row
                * selectedConstantComplement right row))
          (trans
            (Sums.sumRationalCong
              (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
              _ (λ _ → 0ℚ) (λ row → ℚRing.solve []))
            (Fubini.sumRationalZero
              (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector))))
        (trans
          (Fubini.sumRationalMap Combined.gaugeConstraintRow
            (Basis.elements Rows.selectedGaugeRowFiniteSelector)
            (λ row →
              selectedReducedProjection left row
                * selectedConstantComplement right row))
          (selectedGaugeProjectionComplementDotZero left right)))
      (ℚRing.solve []))

selectedComplementProjectionOrthogonal : ∀ left right →
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
    (selectedConstantComplement left) (selectedReducedProjection right)
  ≡ 0ℚ
selectedComplementProjectionOrthogonal left right =
  trans
    (Rect.finiteDotSymmetric Rows.selectedCombinedConstraintRowCarrier
      (selectedConstantComplement left) (selectedReducedProjection right))
    (selectedProjectionComplementOrthogonal right left)

selectedCombinedProjectionLinearLevel : ProofLevel
selectedCombinedProjectionLinearLevel = machineChecked

selectedCombinedProjectionAnnihilationLevel : ProofLevel
selectedCombinedProjectionAnnihilationLevel = machineChecked

selectedCombinedProjectionOrthogonalityLevel : ProofLevel
selectedCombinedProjectionOrthogonalityLevel = machineChecked
