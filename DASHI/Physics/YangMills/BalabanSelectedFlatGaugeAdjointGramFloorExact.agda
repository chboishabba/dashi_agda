module DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact where

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
-- Identify the literal transpose of the selected flat gauge-constraint matrix
-- with the negative periodic gradient on each Lie-coordinate multiplier field.
-- This makes the already-checked periodic Poincare theorem a theorem about the
-- actual finite matrix used by the selected KKT system, rather than about a
-- parallel abstract difference operator.
--
-- On the componentwise-mean-zero multiplier section:
--
--   ||L_0^* lambda||^2
--     = ||grad lambda||^2
--     >= (1/16) ||lambda||^2.
--
-- The proof is exact on the side-four rational carrier.  It still does not say
-- that the flat constant sector is the kernel at every background; that is the
-- separate holonomy/stabilizer seam handled elsewhere.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; -_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (pair; map)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Incidence
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanPath4GlobalPoincareExact as Poincare
import DASHI.Physics.YangMills.BalabanPath4PhysicalComponentPoincareExact as ComponentPoincare
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as WeightedSchur
import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as RowCarrier
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as Reduced

GaugeMultiplier : Set
GaugeMultiplier = RowCarrier.GaugeMultiplier

GaugeRow : Set
GaugeRow = RowCarrier.GaugeRow

gaugeRows : List GaugeRow
gaugeRows = Basis.elements RowCarrier.selectedGaugeRowFiniteSelector

physicalCoordinates : List Coordinates.PhysicalSU2Coordinate4
physicalCoordinates = Coordinates.physicalSU2Coordinates4

multiplierField : GaugeMultiplier → Coordinates.LieCoordinate → Periodic.Site4 → ℚ
multiplierField multiplier coordinate site = multiplier (pair coordinate site)

------------------------------------------------------------------------
-- Literal flat matrix entry = incidence coefficient with identity adjoint.
------------------------------------------------------------------------

identityAdjointEntryExact :
  ∀ row column →
  GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
    Physical.identityBackground row column
  ≡ GaugeMatrix.incidenceCoefficient row column
identityAdjointEntryExact row column =
  GaugeMatrix.selectedGaugeConstraintAtIdentityRecoversIncidence row column

------------------------------------------------------------------------
-- Exact transpose action is the negative periodic gradient.
------------------------------------------------------------------------

actualFlatGaugeAdjoint : GaugeMultiplier → StateCarrier.StateVector
actualFlatGaugeAdjoint multiplier =
  Rect.applyRectangular gaugeRows
    (Rect.transposeRectangular
      (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
        Physical.identityBackground))
    multiplier

coordinateAxisField :
  GaugeMultiplier → Coordinates.LieCoordinate → Periodic.Axis4 → Periodic.Site4 → ℚ
coordinateAxisField multiplier coordinate axis site =
  actualFlatGaugeAdjoint multiplier
    (pair coordinate (pair axis site))

currentIncidenceCoefficient : GaugeRow → GaugeRow → ℚ
currentIncidenceCoefficient (pair rowCoordinate rowSite)
    (pair columnCoordinate columnSite) =
  GaugeMatrix.lieKronecker rowCoordinate columnCoordinate
    * GaugeMatrix.siteKronecker rowSite columnSite

backwardIncidenceCoefficient :
  Periodic.Axis4 → GaugeRow → GaugeRow → ℚ
backwardIncidenceCoefficient axis
    (pair rowCoordinate rowSite)
    (pair columnCoordinate columnSite) =
  GaugeMatrix.lieKronecker rowCoordinate columnCoordinate
    * GaugeMatrix.siteKronecker
        (Periodic.shiftBackward axis rowSite) columnSite

incidenceSplitsCurrentMinusBackward :
  ∀ rowCoordinate rowSite columnCoordinate columnAxis columnSite →
  GaugeMatrix.incidenceCoefficient
      (pair rowCoordinate rowSite)
      (pair columnCoordinate (pair columnAxis columnSite))
  ≡
  currentIncidenceCoefficient
      (pair rowCoordinate rowSite) (pair columnCoordinate columnSite)
  - backwardIncidenceCoefficient columnAxis
      (pair rowCoordinate rowSite) (pair columnCoordinate columnSite)
incidenceSplitsCurrentMinusBackward rowCoordinate rowSite
    columnCoordinate columnAxis columnSite = refl

currentIncidenceSumExact :
  ∀ multiplier coordinate site →
  Sums.sumRational gaugeRows
    (λ row →
      currentIncidenceCoefficient row (pair coordinate site) * multiplier row)
  ≡ multiplier (pair coordinate site)
currentIncidenceSumExact multiplier coordinate site =
  RowCarrier.selectedGaugeRowSelectorExact
    (λ row → multiplier row)
    (pair coordinate site)

backwardIncidenceSumExact :
  ∀ multiplier coordinate axis site →
  Sums.sumRational gaugeRows
    (λ row →
      backwardIncidenceCoefficient axis row (pair coordinate site)
        * multiplier row)
  ≡ multiplier (pair coordinate (Periodic.shiftForward axis site))
backwardIncidenceSumExact multiplier coordinate axis site =
  let target = pair coordinate (Periodic.shiftForward axis site) in
  trans
    (Sums.sumRationalCong gaugeRows _
      (λ row →
        RowCarrier.gaugeKronecker row target * multiplier row)
      (λ { (pair rowCoordinate rowSite) →
        cong (_* multiplier (pair rowCoordinate rowSite))
          (cong (GaugeMatrix.lieKronecker rowCoordinate coordinate *_)
            (GaugeMatrix.siteKroneckerShiftBackwardForwardExact
              rowSite site axis)) }))
    (RowCarrier.selectedGaugeRowSelectorExact
      (λ row → multiplier row) target)

actualFlatGaugeAdjointPointwiseExact :
  ∀ multiplier coordinate axis site →
  actualFlatGaugeAdjoint multiplier
    (pair coordinate (pair axis site))
  ≡ - Periodic.forwardDifference axis
      (multiplierField multiplier coordinate) site
actualFlatGaugeAdjointPointwiseExact multiplier coordinate axis site =
  let
    column = pair coordinate (pair axis site)
    currentTerm = λ row →
      currentIncidenceCoefficient row (pair coordinate site) * multiplier row
    backwardTerm = λ row →
      backwardIncidenceCoefficient axis row (pair coordinate site) * multiplier row

    split :
      actualFlatGaugeAdjoint multiplier column
      ≡ Sums.sumRational gaugeRows
          (λ row → currentTerm row - backwardTerm row)
    split = Sums.sumRationalCong gaugeRows _ _
      (λ row →
        trans
          (cong (_* multiplier row)
            (trans
              (identityAdjointEntryExact row column)
              (caseIncidence row)))
          (ℚRing.solve-∀
            (currentIncidenceCoefficient row (pair coordinate site))
            (backwardIncidenceCoefficient axis row (pair coordinate site))
            (multiplier row)))
      where
        caseIncidence : ∀ row →
          GaugeMatrix.incidenceCoefficient row column
          ≡ currentIncidenceCoefficient row (pair coordinate site)
            - backwardIncidenceCoefficient axis row (pair coordinate site)
        caseIncidence (pair rowCoordinate rowSite) =
          incidenceSplitsCurrentMinusBackward
            rowCoordinate rowSite coordinate axis site

    distribute :
      Sums.sumRational gaugeRows
        (λ row → currentTerm row - backwardTerm row)
      ≡ Sums.sumRational gaugeRows currentTerm
        - Sums.sumRational gaugeRows backwardTerm
    distribute = Fubini.sumRationalSubtract gaugeRows currentTerm backwardTerm

    currentExact = currentIncidenceSumExact multiplier coordinate site
    backwardExact = backwardIncidenceSumExact multiplier coordinate axis site
  in
  trans split
    (trans distribute
      (trans
        (cong₂ _-_ currentExact backwardExact)
        (ℚRing.solve-∀
          (multiplier (pair coordinate site))
          (multiplier
            (pair coordinate (Periodic.shiftForward axis site))))))

------------------------------------------------------------------------
-- Literal transpose norm = periodic gradient energy.
------------------------------------------------------------------------

componentGradientEnergy : GaugeMultiplier → Coordinates.LieCoordinate → ℚ
componentGradientEnergy multiplier coordinate =
  Sums.sumRational
    (Block.physicalBlockSites Path4.side4)
    (λ site → Periodic.siteGradientEnergy
      (multiplierField multiplier coordinate) site)

gaugeMultiplierRowNormSq : GaugeMultiplier → ℚ
gaugeMultiplierRowNormSq multiplier =
  Rect.finiteNormSq RowCarrier.selectedGaugeRowCarrier multiplier

actualFlatGaugeAdjointNormSq : GaugeMultiplier → ℚ
actualFlatGaugeAdjointNormSq multiplier =
  Rect.finiteNormSq StateCarrier.physicalStateCarrier
    (actualFlatGaugeAdjoint multiplier)

componentAxisNormExact :
  ∀ multiplier coordinate axis →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site →
      coordinateAxisField multiplier coordinate axis site
        * coordinateAxisField multiplier coordinate axis site)
  ≡ ComponentPoincare.axisDirectionalEnergy
      (multiplierField multiplier coordinate) axis
componentAxisNormExact multiplier coordinate axis =
  Sums.sumRationalCong
    (Block.physicalBlockSites Path4.side4) _ _
    (λ site →
      let difference = Periodic.forwardDifference axis
        (multiplierField multiplier coordinate) site in
      trans
        (cong₂ _*_
          (actualFlatGaugeAdjointPointwiseExact multiplier coordinate axis site)
          (actualFlatGaugeAdjointPointwiseExact multiplier coordinate axis site))
        (ℚRing.solve-∀ difference))

componentAdjointNormExact :
  ∀ multiplier coordinate →
  Sums.sumRational Incidence.bondCells4
    (λ cell →
      actualFlatGaugeAdjoint multiplier (pair coordinate cell)
        * actualFlatGaugeAdjoint multiplier (pair coordinate cell))
  ≡ componentGradientEnergy multiplier coordinate
componentAdjointNormExact multiplier coordinate =
  trans
    (Fubini.sumCartesian
      Periodic.axes4
      (Block.physicalBlockSites Path4.side4)
      (λ cell →
        actualFlatGaugeAdjoint multiplier (pair coordinate cell)
          * actualFlatGaugeAdjoint multiplier (pair coordinate cell)))
    (trans
      (Sums.sumRationalCong Periodic.axes4 _ _
        (λ axis → componentAxisNormExact multiplier coordinate axis))
      (sym (Periodic.sumAxesSitesEqualsGlobalGradientEnergy
        (multiplierField multiplier coordinate))))

actualFlatGaugeAdjointNormExact : ∀ multiplier →
  actualFlatGaugeAdjointNormSq multiplier
  ≡ Sums.sumRational Coordinates.lieCoordinates3
      (componentGradientEnergy multiplier)
actualFlatGaugeAdjointNormExact multiplier =
  trans
    (Fubini.sumCartesian
      Coordinates.lieCoordinates3 Incidence.bondCells4
      (λ coordinate →
        actualFlatGaugeAdjoint multiplier coordinate
          * actualFlatGaugeAdjoint multiplier coordinate))
    (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
      (λ coordinate → componentAdjointNormExact multiplier coordinate))

------------------------------------------------------------------------
-- Gauge-row norm = sum of component site norms.
------------------------------------------------------------------------

componentMultiplierNormSq : GaugeMultiplier → Coordinates.LieCoordinate → ℚ
componentMultiplierNormSq multiplier coordinate =
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site →
      multiplier (pair coordinate site) * multiplier (pair coordinate site))

gaugeMultiplierRowNormSqExact : ∀ multiplier →
  gaugeMultiplierRowNormSq multiplier
  ≡ Sums.sumRational Coordinates.lieCoordinates3
      (componentMultiplierNormSq multiplier)
gaugeMultiplierRowNormSqExact multiplier =
  Fubini.sumCartesian
    Coordinates.lieCoordinates3
    (Block.physicalBlockSites Path4.side4)
    (λ row → multiplier row * multiplier row)

------------------------------------------------------------------------
-- The existing periodic Poincare floor applies componentwise.
------------------------------------------------------------------------

componentMeanZero : GaugeMultiplier → Coordinates.LieCoordinate → Set
componentMeanZero multiplier coordinate =
  Poincare.GlobalMeanZero4 (multiplierField multiplier coordinate)

record FlatGaugeReducedMultiplier (multiplier : GaugeMultiplier) : Set where
  field
    coordinateXMeanZero : componentMeanZero multiplier Coordinates.coordinateX
    coordinateYMeanZero : componentMeanZero multiplier Coordinates.coordinateY
    coordinateZMeanZero : componentMeanZero multiplier Coordinates.coordinateZ

open FlatGaugeReducedMultiplier public

componentReduced :
  ∀ {multiplier} → FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate → componentMeanZero multiplier coordinate
componentReduced reduced Coordinates.coordinateX = coordinateXMeanZero reduced
componentReduced reduced Coordinates.coordinateY = coordinateYMeanZero reduced
componentReduced reduced Coordinates.coordinateZ = coordinateZMeanZero reduced

componentPoincareFloor :
  ∀ multiplier → FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate →
  LDL.oneSixteenth * componentMultiplierNormSq multiplier coordinate
  ≤ componentGradientEnergy multiplier coordinate
componentPoincareFloor multiplier reduced coordinate =
  ComponentPoincare.physicalComponentOneSixteenthPoincare
    (multiplierField multiplier coordinate)
    (componentReduced reduced coordinate)

actualFlatGaugeGramReducedFloor :
  ∀ multiplier → FlatGaugeReducedMultiplier multiplier →
  LDL.oneSixteenth * gaugeMultiplierRowNormSq multiplier
  ≤ actualFlatGaugeAdjointNormSq multiplier
actualFlatGaugeGramReducedFloor multiplier reduced =
  let
    pointwise : ∀ coordinate →
      LDL.oneSixteenth * componentMultiplierNormSq multiplier coordinate
      ≤ componentGradientEnergy multiplier coordinate
    pointwise = componentPoincareFloor multiplier reduced

    summed = WeightedSchur.sumPointwiseBelow
      Coordinates.lieCoordinates3 _ _ pointwise

    leftExact = Sums.sumRationalScale
      LDL.oneSixteenth
      Coordinates.lieCoordinates3
      (componentMultiplierNormSq multiplier)

    rowExact = gaugeMultiplierRowNormSqExact multiplier
    adjointExact = actualFlatGaugeAdjointNormExact multiplier
  in
  subst
    (λ lower → lower ≤ actualFlatGaugeAdjointNormSq multiplier)
    (sym
      (trans
        (cong (LDL.oneSixteenth *_) rowExact)
        (sym leftExact)))
    (subst
      (λ upper →
        Sums.sumRational Coordinates.lieCoordinates3
          (λ coordinate →
            LDL.oneSixteenth * componentMultiplierNormSq multiplier coordinate)
        ≤ upper)
      (sym adjointExact)
      summed)

------------------------------------------------------------------------
-- Open-reference and periodic quadratic forms are exactly the same quantity.
------------------------------------------------------------------------

selectedFlatGaugeReferenceFloor : ℚ
selectedFlatGaugeReferenceFloor = LDL.oneSixteenth

selectedFlatGaugeReferenceFloorExact : ∀ multiplier →
  FlatGaugeReducedMultiplier multiplier →
  selectedFlatGaugeReferenceFloor * gaugeMultiplierRowNormSq multiplier
  ≤ actualFlatGaugeAdjointNormSq multiplier
selectedFlatGaugeReferenceFloorExact = actualFlatGaugeGramReducedFloor

selectedFlatGaugeReferenceFloorPositive : 0ℚ < selectedFlatGaugeReferenceFloor
selectedFlatGaugeReferenceFloorPositive = LDL.oneSixteenthPositive

------------------------------------------------------------------------
-- The same section is exactly the componentwise mean-zero section already used
-- by BalabanSelectedFlatGaugeReducedFloorExact.
------------------------------------------------------------------------

flatGaugeReducedToOpenComponent :
  ∀ multiplier → FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate →
  Reduced.ComponentMeanZero
    (multiplierField multiplier coordinate)
flatGaugeReducedToOpenComponent multiplier reduced coordinate =
  reducedToOpenReference (componentReduced reduced coordinate)
  where
    reducedToOpenReference : ∀ {scalarField} →
      Poincare.GlobalMeanZero4 scalarField →
      Reduced.ComponentMeanZero scalarField
    reducedToOpenReference meanZero =
      λ base →
        trans
          (GlobalAverage.average0123EqualsGlobalMean _ base)
          (meanZero base)

openComponentToFlatGaugeReduced :
  ∀ multiplier →
  (∀ coordinate →
    Reduced.ComponentMeanZero
      (multiplierField multiplier coordinate)) →
  FlatGaugeReducedMultiplier multiplier
openComponentToFlatGaugeReduced multiplier openReduced = record
  { coordinateXMeanZero = toPeriodic Coordinates.coordinateX
  ; coordinateYMeanZero = toPeriodic Coordinates.coordinateY
  ; coordinateZMeanZero = toPeriodic Coordinates.coordinateZ
  }
  where
    toPeriodic : ∀ coordinate →
      Poincare.GlobalMeanZero4 (multiplierField multiplier coordinate)
    toPeriodic coordinate base =
      trans
        (sym
          (GlobalAverage.average0123EqualsGlobalMean
            (multiplierField multiplier coordinate) base))
        (openReduced coordinate base)

------------------------------------------------------------------------
-- Exact bridge to the open-reference norm used by the background defect theorem.
------------------------------------------------------------------------

componentMultiplierNormSqOpenExact :
  ∀ multiplier coordinate →
  componentMultiplierNormSq multiplier coordinate
  ≡ Reduced.openNormSq (multiplierField multiplier coordinate)
componentMultiplierNormSqOpenExact multiplier coordinate =
  refl

gaugeMultiplierOpenNormSq : GaugeMultiplier → ℚ
gaugeMultiplierOpenNormSq multiplier =
  Reduced.openNormSq (multiplierField multiplier Coordinates.coordinateX)
  + Reduced.openNormSq (multiplierField multiplier Coordinates.coordinateY)
  + Reduced.openNormSq (multiplierField multiplier Coordinates.coordinateZ)

gaugeMultiplierRowNormSqMatchesOpen : ∀ multiplier →
  gaugeMultiplierRowNormSq multiplier ≡ gaugeMultiplierOpenNormSq multiplier
gaugeMultiplierRowNormSqMatchesOpen multiplier =
  trans
    (gaugeMultiplierRowNormSqExact multiplier)
    refl

gaugeMultiplierOpenBelowPeriodic : ∀ multiplier →
  gaugeMultiplierOpenNormSq multiplier ≤ gaugeMultiplierRowNormSq multiplier
gaugeMultiplierOpenBelowPeriodic multiplier =
  let
    openNonnegative : 0ℚ ≤ gaugeMultiplierOpenNormSq multiplier
    openNonnegative = WeightedSchur.sumNonnegative
      Coordinates.lieCoordinates3
      (λ coordinate → componentMultiplierNormSq multiplier coordinate)
      (λ coordinate →
        Rect.finiteNormSqNonnegative
          Reduced.site4FiniteCoordinates
          (multiplierField multiplier coordinate))

    raw :
      gaugeMultiplierOpenNormSq multiplier + 0ℚ
      ≤ gaugeMultiplierOpenNormSq multiplier + gaugeMultiplierRowNormSq multiplier
    raw = ℚP.+-monoʳ-≤ (gaugeMultiplierOpenNormSq multiplier)
      (subst
        (λ value → 0ℚ ≤ value)
        (gaugeMultiplierRowNormSqMatchesOpen multiplier)
        openNonnegative)

    lowerNormalized :
      gaugeMultiplierOpenNormSq multiplier
      ≤ gaugeMultiplierOpenNormSq multiplier + gaugeMultiplierRowNormSq multiplier
    lowerNormalized =
      subst
        (λ lower → lower ≤
          gaugeMultiplierOpenNormSq multiplier + gaugeMultiplierRowNormSq multiplier)
        (ℚP.+-identityʳ (gaugeMultiplierOpenNormSq multiplier))
        raw
  in
  subst
    (λ upper → gaugeMultiplierOpenNormSq multiplier ≤ upper)
    (ℚRing.solve-∀
      (gaugeMultiplierOpenNormSq multiplier)
      (gaugeMultiplierRowNormSq multiplier))
    lowerNormalized

selectedFlatGaugeAdjointLiteralLevel : ProofLevel
selectedFlatGaugeAdjointLiteralLevel = machineChecked

selectedFlatGaugeAdjointReducedFloorLevel : ProofLevel
selectedFlatGaugeAdjointReducedFloorLevel = machineChecked
