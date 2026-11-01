module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact where

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
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Convert the already proved *forward* selected-background gauge derivative
-- estimate into a literal transpose/adjoint estimate on the 768 x 3072
-- physical matrix.  Let
--
--   E_A = L_gauge,A - L_gauge,1.
--
-- The physical quaternion estimate gives, for every state basis column j,
--
--   sum_r E_A(r,j)^2 <= 16 delta.
--
-- Applying the exact finite transpose/Frobenius theorem to all 3072 columns
-- gives
--
--   ||E_A^T lambda||^2 <= 3072 * 16 delta ||lambda||^2.
--
-- At the selected relaxed radius delta = 4 rho^2, rho=1/8192, the coefficient
-- is exactly
--
--   3072 * 16 * 4 * rho^2 = 3/1024.
--
-- This is intentionally an entry-by-entry finite proof.  It does not infer
-- equality of operator norms of E and E^T from singular-value theory.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteRectangularTransposeFrobeniusExact as Transpose
import DASHI.Physics.YangMills.BalabanFiniteLinearFunctionalCoordinatesExact as Linear
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Count
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as GaugeFirst
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact as Pointwise
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as Global
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows

GaugeRow : Set
GaugeRow = FlatGauge.GaugeCoordinate4

GaugeMultiplier : Set
GaugeMultiplier = GaugeRow → ℚ

gaugeRows : List GaugeRow
gaugeRows = Basis.elements Rows.selectedGaugeRowFiniteSelector

------------------------------------------------------------------------
-- Literal defect matrix E_A = L_A - L_1.
------------------------------------------------------------------------

gaugeDefectMatrix :
  Physical.RationalSU2Background4 →
  GaugeRow → KKT.State → ℚ
gaugeDefectMatrix background row column =
  GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row column
  - GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
      Physical.identityBackground row column

gaugeDefectMatrixEntryExact :
  ∀ background coordinate site column →
  gaugeDefectMatrix background (pair coordinate site) column
  ≡ Pointwise.backgroundGaugeDefectCoordinate background
      (Coordinates.decodePhysicalSU2 (Basis.physicalBasis column))
      coordinate site
gaugeDefectMatrixEntryExact background coordinate site column =
  let
    basis = Linear.basisVector KKT.physicalStateCarrier column
    field = Coordinates.decodePhysicalSU2 basis

    backgroundExact :
      GaugeMatrix.gaugeFunctional background (pair coordinate site) basis
      ≡ GaugeFirst.backgroundGaugeFirst background field
          (pair coordinate site)
    backgroundExact =
      GaugeMatrix.gaugeFunctionalIsPhysicalDerivative
        background (pair coordinate site) basis

    identityExact :
      GaugeMatrix.gaugeFunctional Physical.identityBackground
          (pair coordinate site) basis
      ≡ GaugeFirst.flatGaugeFirstFromAxes field (pair coordinate site)
    identityExact =
      trans
        (GaugeMatrix.gaugeFunctionalIsPhysicalDerivative
          Physical.identityBackground (pair coordinate site) basis)
        (GaugeFirst.identityBackgroundGaugeFirstIsFlatAxes
          field coordinate site)
  in
  cong₂ _-_ backgroundExact identityExact

------------------------------------------------------------------------
-- Column square is exactly the previously bounded physical defect energy.
------------------------------------------------------------------------

gaugeDefectColumnNormSq :
  Physical.RationalSU2Background4 → KKT.State → ℚ
gaugeDefectColumnNormSq background column =
  Sums.sumRational gaugeRows
    (λ row →
      gaugeDefectMatrix background row column
      * gaugeDefectMatrix background row column)

coordinateDefectSquare :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Coordinates.LieCoordinate3 → Periodic.Site4 → ℚ
coordinateDefectSquare background field coordinate site =
  let
    defect = Pointwise.backgroundGaugeDefectCoordinate
      background field coordinate site
  in defect * defect

globalDefectEnergySplitCoordinates : ∀ background field →
  Global.globalGaugeDerivativeDefectEnergy background field
  ≡ Periodic.sumSites
      (coordinateDefectSquare background field Coordinates.coordinateX)
    + (Periodic.sumSites
      (coordinateDefectSquare background field Coordinates.coordinateY)
    + Periodic.sumSites
      (coordinateDefectSquare background field Coordinates.coordinateZ))
globalDefectEnergySplitCoordinates background field =
  let
    dx = coordinateDefectSquare background field Coordinates.coordinateX
    dy = coordinateDefectSquare background field Coordinates.coordinateY
    dz = coordinateDefectSquare background field Coordinates.coordinateZ

    pointwiseExact : ∀ site →
      Pointwise.pointwiseGaugeDefectEnergy background field site
      ≡ dx site + (dy site + dz site)
    pointwiseExact site = ℚRing.solve-∀
      (Pointwise.backgroundGaugeDefectCoordinate
        background field Coordinates.coordinateX site)
      (Pointwise.backgroundGaugeDefectCoordinate
        background field Coordinates.coordinateY site)
      (Pointwise.backgroundGaugeDefectCoordinate
        background field Coordinates.coordinateZ site)
  in
  trans
    (Periodic.sumSitesCong _ _ pointwiseExact)
    (trans
      (Periodic.sumSitesAdd dx (λ site → dy site + dz site))
      (cong
        (Periodic.sumSites dx +_)
        (Periodic.sumSitesAdd dy dz)))

gaugeDefectColumnNormSqExact : ∀ background column →
  gaugeDefectColumnNormSq background column
  ≡ Global.globalGaugeDerivativeDefectEnergy background
      (Coordinates.decodePhysicalSU2 (Basis.physicalBasis column))
gaugeDefectColumnNormSqExact background column =
  let
    field = Coordinates.decodePhysicalSU2 (Basis.physicalBasis column)

    afterEntries :
      gaugeDefectColumnNormSq background column
      ≡ Sums.sumRational Coordinates.lieCoordinates3
          (λ coordinate →
            Sums.sumRational (Block.physicalBlockSites Path4.side4)
              (coordinateDefectSquare background field coordinate))
    afterEntries =
      trans
        (Fubini.sumCartesian
          Coordinates.lieCoordinates3
          (Block.physicalBlockSites Path4.side4)
          (λ row →
            gaugeDefectMatrix background row column
            * gaugeDefectMatrix background row column))
        (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
          (λ coordinate →
            Sums.sumRationalCong
              (Block.physicalBlockSites Path4.side4) _ _
              (λ site →
                cong₂ _*_
                  (gaugeDefectMatrixEntryExact
                    background coordinate site column)
                  (gaugeDefectMatrixEntryExact
                    background coordinate site column))))

    siteSums :
      Sums.sumRational Coordinates.lieCoordinates3
        (λ coordinate →
          Sums.sumRational (Block.physicalBlockSites Path4.side4)
            (coordinateDefectSquare background field coordinate))
      ≡ Periodic.sumSites
          (coordinateDefectSquare background field Coordinates.coordinateX)
        + (Periodic.sumSites
          (coordinateDefectSquare background field Coordinates.coordinateY)
        + Periodic.sumSites
          (coordinateDefectSquare background field Coordinates.coordinateZ))
    siteSums =
      trans
        (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
          (λ coordinate →
            sym
              (Bridge.sumSitesMatchesGlobalSiteSum
                (coordinateDefectSquare background field coordinate))))
        (ℚRing.solve-∀
          (Periodic.sumSites
            (coordinateDefectSquare background field Coordinates.coordinateX))
          (Periodic.sumSites
            (coordinateDefectSquare background field Coordinates.coordinateY))
          (Periodic.sumSites
            (coordinateDefectSquare background field Coordinates.coordinateZ)))
  in
  trans afterEntries
    (trans siteSums
      (sym (globalDefectEnergySplitCoordinates background field)))

basisDecodedNormSqOne : ∀ column →
  Coordinates.physicalSU2BondNormSq
    (Coordinates.decodePhysicalSU2 (Basis.physicalBasis column))
  ≡ 1ℚ
basisDecodedNormSqOne column =
  let
    field = Coordinates.decodePhysicalSU2 (Basis.physicalBasis column)

    encodedNormExact :
      Coordinates.physicalSU2CoordinateNormSq
        (Coordinates.encodePhysicalSU2 field)
      ≡ Coordinates.physicalSU2CoordinateNormSq
          (Basis.physicalBasis column)
    encodedNormExact =
      Sums.sumRationalCong Coordinates.physicalSU2Coordinates4 _ _
        (λ coordinate →
          cong₂ _*_
            (Coordinates.encodeAfterDecodePointwise
              (Basis.physicalBasis column) coordinate)
            (Coordinates.encodeAfterDecodePointwise
              (Basis.physicalBasis column) coordinate))
  in
  trans
    (sym (Coordinates.encodePhysicalSU2NormSqExact field))
    (trans encodedNormExact (Basis.physicalBasisNormSqExact column))

sixteenDelta : ℚ → ℚ
sixteenDelta delta = (+ 16 / 1) * delta

gaugeDefectColumnBound :
  ∀ background delta →
  0ℚ ≤ delta →
  Global.UniformInverseLinkDefectSq background delta →
  ∀ column →
  gaugeDefectColumnNormSq background column ≤ sixteenDelta delta
gaugeDefectColumnBound background delta deltaNonnegative radius column =
  let
    field = Coordinates.decodePhysicalSU2 (Basis.physicalBasis column)
    raw = Global.globalGaugeDerivativeDefectUniformBound
      background field delta deltaNonnegative radius

    normalized :
      Global.globalGaugeDerivativeDefectEnergy background field
      ≤ sixteenDelta delta
    normalized =
      subst
        (λ norm →
          Global.globalGaugeDerivativeDefectEnergy background field
          ≤ (+ 16 / 1) * delta * norm)
        (basisDecodedNormSqOne column)
        (subst
          (λ upper →
            Global.globalGaugeDerivativeDefectEnergy background field ≤ upper)
          (ℚRing.solve-∀ delta)
          raw)
  in
  subst
    (λ left → left ≤ sixteenDelta delta)
    (sym (gaugeDefectColumnNormSqExact background column))
    normalized

sixteenDeltaNonnegative : ∀ delta →
  0ℚ ≤ delta → 0ℚ ≤ sixteenDelta delta
sixteenDeltaNonnegative delta deltaNonnegative =
  let
    instance
      sixteenNN : NonNegative (+ 16 / 1)
      sixteenNN = ℚ.nonNegative (ℚP.nonNegative⁻¹ (+ 16 / 1))
      deltaNN : NonNegative delta
      deltaNN = ℚ.nonNegative deltaNonnegative
  in
  ℚP.nonNegative⁻¹ (sixteenDelta delta)

------------------------------------------------------------------------
-- Exact transpose bound.
------------------------------------------------------------------------

gaugeDefectColumnData :
  ∀ background delta →
  0ℚ ≤ delta →
  Global.UniformInverseLinkDefectSq background delta →
  Transpose.RectangularColumnBound
gaugeDefectColumnData background delta deltaNonnegative radius = record
  { Transpose.RectangularColumnBound.rows = gaugeRows
  ; Transpose.RectangularColumnBound.columns = Coordinates.physicalSU2Coordinates4
  ; Transpose.RectangularColumnBound.matrix = gaugeDefectMatrix background
  ; Transpose.RectangularColumnBound.columnBound = sixteenDelta delta
  ; Transpose.RectangularColumnBound.columnBoundNonnegative =
      sixteenDeltaNonnegative delta deltaNonnegative
  ; Transpose.RectangularColumnBound.columnBounded =
      gaugeDefectColumnBound background delta deltaNonnegative radius
  }

gaugeMultiplierRowNormSq : GaugeMultiplier → ℚ
gaugeMultiplierRowNormSq multiplier =
  Sums.sumRational gaugeRows
    (λ row → multiplier row * multiplier row)

gaugeAdjointDefectApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → KKT.StateVector
gaugeAdjointDefectApply background multiplier column =
  Sums.sumRational gaugeRows
    (λ row → gaugeDefectMatrix background row column * multiplier row)

gaugeAdjointDefectNormSq :
  Physical.RationalSU2Background4 → GaugeMultiplier → ℚ
gaugeAdjointDefectNormSq background multiplier =
  Sums.sumRational Coordinates.physicalSU2Coordinates4
    (λ column →
      gaugeAdjointDefectApply background multiplier column
      * gaugeAdjointDefectApply background multiplier column)

natAsRationalPhysicalCoordinateCountExact :
  Sums.natAsRational (length Coordinates.physicalSU2Coordinates4)
  ≡ + 3072 / 1
natAsRationalPhysicalCoordinateCountExact =
  trans
    (cong Sums.natAsRational Count.physicalCoordinateCount)
    (ℚRing.solve [])

gaugeAdjointDefectFrobeniusBound :
  ∀ background delta →
  0ℚ ≤ delta →
  Global.UniformInverseLinkDefectSq background delta →
  ∀ multiplier →
  gaugeAdjointDefectNormSq background multiplier
  ≤ (+ 3072 / 1) * ((+ 16 / 1) * delta)
      * gaugeMultiplierRowNormSq multiplier
gaugeAdjointDefectFrobeniusBound
    background delta deltaNonnegative radius multiplier =
  let
    dataSet = gaugeDefectColumnData
      background delta deltaNonnegative radius
    raw = Transpose.transposeFrobeniusBound dataSet multiplier
  in
  subst
    (λ coefficient →
      gaugeAdjointDefectNormSq background multiplier
      ≤ coefficient * ((+ 16 / 1) * delta)
          * gaugeMultiplierRowNormSq multiplier)
    natAsRationalPhysicalCoordinateCountExact
    raw

------------------------------------------------------------------------
-- Selected relaxed radius: coefficient = 3/1024 exactly.
------------------------------------------------------------------------

selectedAdjointDefectCoefficient : ℚ
selectedAdjointDefectCoefficient = + 3 / 1024

selectedAdjointDefectCoefficientExact :
  (+ 3072 / 1) * ((+ 16 / 1) * Relaxed.fourRhoSquare)
  ≡ selectedAdjointDefectCoefficient
selectedAdjointDefectCoefficientExact = ℚRing.solve []

gaugeAdjointDefectSelectedRadiusBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  gaugeAdjointDefectNormSq background multiplier
  ≤ selectedAdjointDefectCoefficient * gaugeMultiplierRowNormSq multiplier
gaugeAdjointDefectSelectedRadiusBound background radius multiplier =
  subst
    (λ coefficient →
      gaugeAdjointDefectNormSq background multiplier
      ≤ coefficient * gaugeMultiplierRowNormSq multiplier)
    selectedAdjointDefectCoefficientExact
    (gaugeAdjointDefectFrobeniusBound
      background Relaxed.fourRhoSquare
      (ℚP.nonNegative⁻¹ Relaxed.fourRhoSquare)
      radius multiplier)

selectedGaugeAdjointDefectLevel : ProofLevel
selectedGaugeAdjointDefectLevel = machineChecked
