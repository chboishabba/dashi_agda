module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintStencilExact where

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
-- DASHI CONTRIBUTION
--
-- Prove the exact spatial stencil of the literal selected-background gauge
-- row.  A row at x can see only a positive bond based at x or the positive
-- bond of direction mu based at x-mu.  The adjoint transport may mix the three
-- Lie coordinates, but it cannot enlarge this spatial support.  Therefore
-- every matrix entry outside this two-site-per-direction stencil is exactly
-- zero before any norm estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base as ℚ using (0ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanFiniteLinearFunctionalCoordinatesExact as Linear
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix

data GaugeConstraintSpatialSupport :
    FlatGauge.GaugeCoordinate4 → KKT.State → Set where
  currentSiteSupport :
    ∀ {rowCoordinate rowSite columnCoordinate columnAxis columnSite} →
    columnSite ≡ rowSite →
    GaugeConstraintSpatialSupport
      (pair rowCoordinate rowSite)
      (pair columnCoordinate (pair columnAxis columnSite))

  backwardSiteSupport :
    ∀ {rowCoordinate rowSite columnCoordinate columnAxis columnSite} →
    columnSite ≡ Periodic.shiftBackward columnAxis rowSite →
    GaugeConstraintSpatialSupport
      (pair rowCoordinate rowSite)
      (pair columnCoordinate (pair columnAxis columnSite))

basisAtCurrentSiteOutsideZero :
  ∀ {rowCoordinate rowSite columnCoordinate columnAxis columnSite}
    (outside : GaugeConstraintSpatialSupport
      (pair rowCoordinate rowSite)
      (pair columnCoordinate (pair columnAxis columnSite)) → ⊥)
    selectedCoordinate selectedAxis →
  Linear.basisVector KKT.physicalStateCarrier
    (pair columnCoordinate (pair columnAxis columnSite))
    (pair selectedCoordinate (pair selectedAxis rowSite))
  ≡ 0ℚ
basisAtCurrentSiteOutsideZero
    {rowCoordinate} {rowSite} {columnCoordinate} {columnAxis} {columnSite}
    outside selectedCoordinate selectedAxis
  with Calibration.physicalCoordinateDecidableEquality
    (pair selectedCoordinate (pair selectedAxis rowSite))
    (pair columnCoordinate (pair columnAxis columnSite))
... | yes refl =
  ⊥-elim (outside (currentSiteSupport refl))
... | no _ = refl

basisAtBackwardSiteOutsideZero :
  ∀ {rowCoordinate rowSite columnCoordinate columnAxis columnSite}
    (outside : GaugeConstraintSpatialSupport
      (pair rowCoordinate rowSite)
      (pair columnCoordinate (pair columnAxis columnSite)) → ⊥)
    selectedCoordinate selectedAxis →
  Linear.basisVector KKT.physicalStateCarrier
    (pair columnCoordinate (pair columnAxis columnSite))
    (pair selectedCoordinate
      (pair selectedAxis (Periodic.shiftBackward selectedAxis rowSite)))
  ≡ 0ℚ
basisAtBackwardSiteOutsideZero
    {rowCoordinate} {rowSite} {columnCoordinate} {columnAxis} {columnSite}
    outside selectedCoordinate selectedAxis
  with Calibration.physicalCoordinateDecidableEquality
    (pair selectedCoordinate
      (pair selectedAxis (Periodic.shiftBackward selectedAxis rowSite)))
    (pair columnCoordinate (pair columnAxis columnSite))
... | yes refl =
  ⊥-elim (outside (backwardSiteSupport refl))
... | no _ = refl

basisInsertionBackwardOutsideZero :
  ∀ {rowCoordinate rowSite columnCoordinate columnAxis columnSite}
    (outside : GaugeConstraintSpatialSupport
      (pair rowCoordinate rowSite)
      (pair columnCoordinate (pair columnAxis columnSite)) → ⊥)
    selectedAxis →
  GaugeMatrix.decodedInsertion
    (Linear.basisVector KKT.physicalStateCarrier
      (pair columnCoordinate (pair columnAxis columnSite)))
    selectedAxis (Periodic.shiftBackward selectedAxis rowSite)
  ≡ Q.zeroQ
basisInsertionBackwardOutsideZero outside selectedAxis =
  Q.quaternionExt
    refl
    (basisAtBackwardSiteOutsideZero outside
      Coordinates.coordinateX selectedAxis)
    (basisAtBackwardSiteOutsideZero outside
      Coordinates.coordinateY selectedAxis)
    (basisAtBackwardSiteOutsideZero outside
      Coordinates.coordinateZ selectedAxis)

basisTransportBackwardOutsideZero :
  ∀ {rowCoordinate rowSite columnCoordinate columnAxis columnSite}
    (background : Physical.RationalSU2Background4)
    (outside : GaugeConstraintSpatialSupport
      (pair rowCoordinate rowSite)
      (pair columnCoordinate (pair columnAxis columnSite)) → ⊥)
    selectedAxis →
  GaugeMatrix.transportedDecoded background
    (Linear.basisVector KKT.physicalStateCarrier
      (pair columnCoordinate (pair columnAxis columnSite)))
    selectedAxis rowSite
  ≡ Q.zeroQ
basisTransportBackwardOutsideZero
    {rowSite = rowSite} background outside selectedAxis =
  let
    unit = Gauge.backwardTransportUnit background selectedAxis rowSite
  in
  trans
    (cong (Adjoint.adjointTransport unit)
      (basisInsertionBackwardOutsideZero outside selectedAxis))
    (GaugeMatrix.adjointTransportZeroExact unit)

basisBackwardTermOutsideZero :
  ∀ {rowCoordinate rowSite columnCoordinate columnAxis columnSite}
    (background : Physical.RationalSU2Background4)
    (outside : GaugeConstraintSpatialSupport
      (pair rowCoordinate rowSite)
      (pair columnCoordinate (pair columnAxis columnSite)) → ⊥)
    selectedAxis →
  GaugeMatrix.decodedBackwardTerm background
    (Linear.basisVector KKT.physicalStateCarrier
      (pair columnCoordinate (pair columnAxis columnSite)))
    rowCoordinate selectedAxis rowSite
  ≡ 0ℚ
basisBackwardTermOutsideZero
    {rowCoordinate} {rowSite} background outside selectedAxis
  rewrite basisAtCurrentSiteOutsideZero outside
      rowCoordinate selectedAxis
        | basisTransportBackwardOutsideZero
            background outside selectedAxis
        | GaugeMatrix.quaternionCoordinateZeroExact rowCoordinate =
  ℚRing.solve []

selectedBackgroundGaugeConstraintMatrixOutsideStencilZero :
  ∀ background row column →
  (GaugeConstraintSpatialSupport row column → ⊥) →
  GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
    background row column
  ≡ 0ℚ
selectedBackgroundGaugeConstraintMatrixOutsideStencilZero
    background (pair rowCoordinate rowSite)
    (pair columnCoordinate (pair columnAxis columnSite)) outside =
  trans
    (Sums.sumRationalCong Gauge.axes4
      (λ selectedAxis →
        GaugeMatrix.decodedBackwardTerm background
          (Linear.basisVector KKT.physicalStateCarrier
            (pair columnCoordinate (pair columnAxis columnSite)))
          rowCoordinate selectedAxis rowSite)
      (λ _ → 0ℚ)
      (basisBackwardTermOutsideZero background outside))
    (Fubini.sumRationalZero Gauge.axes4)

selectedGaugeConstraintStencilLevel : ProofLevel
selectedGaugeConstraintStencilLevel = machineChecked
