module DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact where

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
-- Split every literal 768-coordinate gauge multiplier into its three global
-- constant components and a componentwise mean-zero remainder.  The split is
-- pointwise exact and orthogonal in the repository's finite L2 norm:
--
--   lambda = lambda_0 + P_const lambda,
--   ||lambda||^2 = ||lambda_0||^2 + ||P_const lambda||^2.
--
-- This supplies the fixed carrier decomposition needed to regularize the
-- background Gram without pretending the flat constant directions remain the
-- true stabilizer at every background.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as FiniteAverage
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact as Variance
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as Global
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Count
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor

GaugeMultiplier : Set
GaugeMultiplier = FlatFloor.GaugeMultiplier

scalarMean : Periodic.ScalarField → ℚ
scalarMean field =
  GlobalAverage.oneTwoFiftySix * Periodic.sumSites field

scalarConstantProjection : Periodic.ScalarField → Periodic.ScalarField
scalarConstantProjection field site = scalarMean field

scalarCentered : Periodic.ScalarField → Periodic.ScalarField
scalarCentered field site = field site - scalarMean field

siteSumConstantExact : ∀ value →
  Periodic.sumSites (λ _ → value) ≡ (+ 256 / 1) * value
siteSumConstantExact value =
  trans
    (Bridge.sumSitesMatchesGlobalSiteSum (λ _ → value))
    (trans
      (FiniteAverage.sumRationalConstant
        (Block.physicalBlockSites Path4.side4) value)
      (trans
        (cong
          (λ count → Sums.natAsRational count * value)
          Count.periodicSide4SiteCount)
        (ℚRing.solve-∀ value)))

scalarCenteredSumZero : ∀ field →
  Periodic.sumSites (scalarCentered field) ≡ 0ℚ
scalarCenteredSumZero field =
  trans
    (Periodic.sumSitesSubtract field (scalarConstantProjection field))
    (trans
      (cong
        (Periodic.sumSites field -_)
        (siteSumConstantExact (scalarMean field)))
      (ℚRing.solve-∀ (Periodic.sumSites field)))

scalarCenteredGlobalMeanZero : ∀ field site →
  Path4.average0123 (scalarCentered field) site ≡ 0ℚ
scalarCenteredGlobalMeanZero field site =
  trans
    (GlobalAverage.average0123EqualsGlobalMean
      (scalarCentered field) site)
    (trans
      (cong
        (GlobalAverage.oneTwoFiftySix *_)
        (scalarCenteredSumZero field))
      (ℚRing.solve []))

constantProjection : GaugeMultiplier → GaugeMultiplier
constantProjection multiplier (pair coordinate site) =
  scalarMean (FlatFloor.gaugeMultiplierField multiplier coordinate)

centeredMultiplier : GaugeMultiplier → GaugeMultiplier
centeredMultiplier multiplier (pair coordinate site) =
  multiplier (pair coordinate site) - constantProjection multiplier (pair coordinate site)

multiplierSplitsPointwise : ∀ multiplier coordinate site →
  multiplier (pair coordinate site)
  ≡ centeredMultiplier multiplier (pair coordinate site)
    + constantProjection multiplier (pair coordinate site)
multiplierSplitsPointwise multiplier coordinate site =
  ℚRing.solve-∀
    (multiplier (pair coordinate site))
    (constantProjection multiplier (pair coordinate site))

centeredFieldExact : ∀ multiplier coordinate site →
  FlatFloor.gaugeMultiplierField (centeredMultiplier multiplier) coordinate site
  ≡ scalarCentered (FlatFloor.gaugeMultiplierField multiplier coordinate) site
centeredFieldExact multiplier coordinate site = refl

constantFieldExact : ∀ multiplier coordinate site →
  FlatFloor.gaugeMultiplierField (constantProjection multiplier) coordinate site
  ≡ scalarConstantProjection
      (FlatFloor.gaugeMultiplierField multiplier coordinate) site
constantFieldExact multiplier coordinate site = refl

centeredMultiplierReduced : ∀ multiplier →
  FlatFloor.FlatGaugeReducedMultiplier (centeredMultiplier multiplier)
centeredMultiplierReduced multiplier = record
  { FlatFloor.FlatGaugeReducedMultiplier.coordinateXMeanZero =
      scalarCenteredGlobalMeanZero
        (FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateX)
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateYMeanZero =
      scalarCenteredGlobalMeanZero
        (FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateY)
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateZMeanZero =
      scalarCenteredGlobalMeanZero
        (FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateZ)
  }

scalarAddNormExpansion : ∀ left right →
  Periodic.fieldNormSq (λ site → left site + right site)
  ≡ Periodic.fieldNormSq left + Periodic.fieldNormSq right
    + (+ 2 / 1) * Periodic.fieldInner left right
scalarAddNormExpansion left right =
  trans
    (Periodic.sumSitesCong _ _ (λ site →
      ℚRing.solve-∀ (left site) (right site)))
    (trans
      (Periodic.sumSitesAdd
        (λ site → left site * left site)
        (λ site →
          right site * right site
          + (+ 2 / 1) * (left site * right site)))
      (trans
        (cong
          (Periodic.fieldNormSq left +_)
          (Periodic.sumSitesAdd
            (λ site → right site * right site)
            (λ site → (+ 2 / 1) * (left site * right site))))
        (trans
          (cong
            (λ cross →
              Periodic.fieldNormSq left
              + (Periodic.fieldNormSq right + cross))
            (Periodic.sumSitesScale (+ 2 / 1)
              (λ site → left site * right site)))
          (ℚRing.solve-∀
            (Periodic.fieldNormSq left)
            (Periodic.fieldNormSq right)
            (Periodic.fieldInner left right)))))

scalarCenteredConstantOrthogonal : ∀ field →
  Periodic.fieldInner
    (scalarCentered field) (scalarConstantProjection field)
  ≡ 0ℚ
scalarCenteredConstantOrthogonal field =
  let
    mean = scalarMean field
  in
  trans
    (Periodic.sumSitesCong _ _ (λ site →
      ℚRing.solve-∀ (scalarCentered field site) mean))
    (trans
      (Periodic.sumSitesScale mean (scalarCentered field))
      (trans
        (cong (mean *_) (scalarCenteredSumZero field))
        (ℚRing.solve-∀ mean)))

scalarMeanPythagoras : ∀ field →
  Periodic.fieldNormSq field
  ≡ Periodic.fieldNormSq (scalarCentered field)
    + Periodic.fieldNormSq (scalarConstantProjection field)
scalarMeanPythagoras field =
  let
    centered = scalarCentered field
    constant = scalarConstantProjection field

    reconstruct : ∀ site →
      field site ≡ centered site + constant site
    reconstruct site = ℚRing.solve-∀ (field site) (scalarMean field)
  in
  trans
    (Periodic.sumSitesCong _ _ (λ site →
      cong₂ _*_
        (reconstruct site)
        (reconstruct site)))
    (trans
      (scalarAddNormExpansion centered constant)
      (trans
        (cong
          (λ inner →
            Periodic.fieldNormSq centered
            + Periodic.fieldNormSq constant
            + (+ 2 / 1) * inner)
          (scalarCenteredConstantOrthogonal field))
        (ℚRing.solve-∀
          (Periodic.fieldNormSq centered)
          (Periodic.fieldNormSq constant))))

multiplierPeriodicNormSq : GaugeMultiplier → ℚ
multiplierPeriodicNormSq multiplier =
  Periodic.fieldNormSq
      (FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateX)
  + Periodic.fieldNormSq
      (FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateY)
  + Periodic.fieldNormSq
      (FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateZ)

multiplierPeriodicNormMatchesFlat : ∀ multiplier →
  multiplierPeriodicNormSq multiplier
  ≡ FlatFloor.gaugeMultiplierNormSq multiplier
multiplierPeriodicNormMatchesFlat multiplier =
  let
    x = FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateX
    y = FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateY
    z = FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateZ
  in
  trans
    (cong₂ _+_
      (cong₂ _+_
        (Global.periodicFieldNormSqMatchesGlobal x)
        (Global.periodicFieldNormSqMatchesGlobal y))
      (Global.periodicFieldNormSqMatchesGlobal z))
    (ℚRing.solve-∀
      (Variance.globalNormSq x)
      (Variance.globalNormSq y)
      (Variance.globalNormSq z))

multiplierMeanPythagoras : ∀ multiplier →
  FlatFloor.gaugeMultiplierNormSq multiplier
  ≡ FlatFloor.gaugeMultiplierNormSq (centeredMultiplier multiplier)
    + FlatFloor.gaugeMultiplierNormSq (constantProjection multiplier)
multiplierMeanPythagoras multiplier =
  let
    x = FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateX
    y = FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateY
    z = FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateZ

    periodicSplit :
      multiplierPeriodicNormSq multiplier
      ≡ multiplierPeriodicNormSq (centeredMultiplier multiplier)
        + multiplierPeriodicNormSq (constantProjection multiplier)
    periodicSplit =
      trans
        (cong₂ _+_
          (cong₂ _+_ (scalarMeanPythagoras x) (scalarMeanPythagoras y))
          (scalarMeanPythagoras z))
        (ℚRing.solve-∀
          (Periodic.fieldNormSq (scalarCentered x))
          (Periodic.fieldNormSq (scalarConstantProjection x))
          (Periodic.fieldNormSq (scalarCentered y))
          (Periodic.fieldNormSq (scalarConstantProjection y))
          (Periodic.fieldNormSq (scalarCentered z))
          (Periodic.fieldNormSq (scalarConstantProjection z)))
  in
  trans
    (sym (multiplierPeriodicNormMatchesFlat multiplier))
    (trans
      periodicSplit
      (cong₂ _+_
        (multiplierPeriodicNormMatchesFlat (centeredMultiplier multiplier))
        (multiplierPeriodicNormMatchesFlat (constantProjection multiplier))))

selectedGaugeMeanDecompositionLevel : ProofLevel
selectedGaugeMeanDecompositionLevel = machineChecked

selectedGaugeMeanZeroRemainderLevel : ProofLevel
selectedGaugeMeanZeroRemainderLevel = machineChecked

selectedGaugeMeanPythagorasLevel : ProofLevel
selectedGaugeMeanPythagorasLevel = machineChecked
