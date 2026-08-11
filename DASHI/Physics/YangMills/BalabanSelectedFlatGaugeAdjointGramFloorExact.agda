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
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Identify the transpose of the *actual selected gauge-constraint matrix* at
-- the identity background.  It is not supplied as a compatible-looking
-- gradient: finite adjointness plus the literal periodic summation-by-parts
-- theorem force it pointwise to be the negative forward gradient.
--
-- On the componentwise mean-zero multiplier sector this gives the concrete
-- Gram lower bound
--
--   (1/16) ||lambda||^2 <= ||L_gauge,0^* lambda||^2
--                         = <lambda,K_gauge,0 lambda>.
--
-- The proof uses the repository's literal 768-row gauge carrier and 3072-state
-- carrier.  The periodic wrap edges are retained and proved nonnegative.  No
-- row deletion, rank-by-dimension argument, abstract Hilbert adjoint, or
-- assumed Poincare constant is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (pair; allCyclicIndices; four)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanFiniteLinearFunctionalCoordinatesExact as Linear
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4GlobalPoincareExact as Poincare
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Cell
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as GaugeFirst
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor

------------------------------------------------------------------------
-- Literal 768-row gauge carrier.
------------------------------------------------------------------------

selectedFlatGaugeRowCarrier :
  Matrix.FiniteRationalCoordinates FlatGauge.GaugeCoordinate4
selectedFlatGaugeRowCarrier = record
  { Matrix.FiniteRationalCoordinates.coordinates =
      Basis.elements Rows.selectedGaugeRowFiniteSelector
  ; Matrix.FiniteRationalCoordinates.delta =
      λ row column →
        Basis.kronecker
          (Basis.decide Rows.selectedGaugeRowFiniteSelector)
          column row
  ; Matrix.FiniteRationalCoordinates.deltaActsAsIdentity =
      λ vector row →
        trans
          (Sums.sumRationalCong
            (Basis.elements Rows.selectedGaugeRowFiniteSelector)
            (λ column →
              Basis.kronecker
                (Basis.decide Rows.selectedGaugeRowFiniteSelector)
                column row
              * vector column)
            (λ column →
              vector column
              * Basis.kronecker
                  (Basis.decide Rows.selectedGaugeRowFiniteSelector)
                  column row)
            (λ column → ℚRing.solve-∀
              (Basis.kronecker
                (Basis.decide Rows.selectedGaugeRowFiniteSelector)
                column row)
              (vector column)))
          (Basis.selectorExact
            Rows.selectedGaugeRowFiniteSelector vector row)
  }

GaugeMultiplier : Set
GaugeMultiplier = FlatGauge.GaugeCoordinate4 → ℚ

identityGaugeConstraintMatrix :
  Rect.RectangularMatrix FlatGauge.GaugeCoordinate4 KKT.State
identityGaugeConstraintMatrix =
  GaugeMatrix.selectedBackgroundGaugeConstraintMatrix Physical.identityBackground

identityGaugeConstraintApply :
  KKT.StateVector → GaugeMultiplier
identityGaugeConstraintApply =
  Rect.applyRectangular KKT.physicalStateCarrier identityGaugeConstraintMatrix

identityGaugeConstraintApplyExact :
  ∀ vector coordinate site →
  identityGaugeConstraintApply vector (pair coordinate site)
  ≡ FlatGauge.flatGaugeFirst
      (Coordinates.decodePhysicalSU2 vector) (pair coordinate site)
identityGaugeConstraintApplyExact vector coordinate site =
  trans
    (GaugeMatrix.selectedBackgroundGaugeConstraintMatrixApplyExact
      Physical.identityBackground vector (pair coordinate site))
    (GaugeFirst.identityBackgroundGaugeFirstIsPeriodicDivergence
      (Coordinates.decodePhysicalSU2 vector) coordinate site)

actualFlatGaugeAdjoint : GaugeMultiplier → KKT.StateVector
actualFlatGaugeAdjoint multiplier =
  Rect.applyRectangular selectedFlatGaugeRowCarrier
    (Rect.transposeRectangular identityGaugeConstraintMatrix)
    multiplier

------------------------------------------------------------------------
-- Literal negative periodic gradient candidate.
------------------------------------------------------------------------

multiplierField :
  GaugeMultiplier → Coordinates.LieCoordinate3 → Periodic.ScalarField
multiplierField multiplier coordinate site =
  multiplier (pair coordinate site)

stateBondField :
  KKT.StateVector → Coordinates.LieCoordinate3 → Periodic.BondField4
stateBondField vector coordinate axis site =
  vector (pair coordinate (pair axis site))

flatNegativeGradientState : GaugeMultiplier → KKT.StateVector
flatNegativeGradientState multiplier
    (pair coordinate (pair axis site)) =
  - Periodic.forwardDifference axis
      (multiplierField multiplier coordinate) site

------------------------------------------------------------------------
-- Scalar periodic summation by parts in the exact orientation required by L*.
------------------------------------------------------------------------

periodicAxisNegativeGradientAdjoint :
  ∀ axis field gauge →
  Periodic.fieldInner field
    (λ site → - Periodic.forwardDifference axis gauge site)
  ≡ Periodic.fieldInner
      (Periodic.backwardDifference axis field) gauge
periodicAxisNegativeGradientAdjoint axis field gauge =
  let
    forward = Periodic.forwardDifference axis gauge
    backward = Periodic.backwardDifference axis field

    moveMinus :
      Periodic.fieldInner field (λ site → - forward site)
      ≡ - Periodic.fieldInner forward field
    moveMinus =
      trans
        (Periodic.sumSitesCong _ _ (λ site →
          ℚRing.solve-∀ (field site) (forward site)))
        (Periodic.sumSitesNeg (λ site → forward site * field site))

    integrationByParts :
      Periodic.fieldInner forward field
      ≡ - Periodic.fieldInner gauge backward
    integrationByParts = Periodic.summationByParts axis gauge field
  in
  trans moveMinus
    (trans
      (cong -_ integrationByParts)
      (trans
        (ℚRing.solve-∀ (Periodic.fieldInner gauge backward))
        (Periodic.fieldInnerSymmetric gauge backward)))

fieldInnerFourSumLeft : ∀ first second third fourth gauge →
  Periodic.fieldInner
    (Periodic.fieldSum4 first second third fourth) gauge
  ≡ Periodic.fieldInner first gauge
    + (Periodic.fieldInner second gauge
    + (Periodic.fieldInner third gauge
    + Periodic.fieldInner fourth gauge))
fieldInnerFourSumLeft first second third fourth gauge =
  trans
    (Periodic.sumSitesCong _ _ (λ site →
      ℚRing.solve-∀
        (first site) (second site) (third site) (fourth site)
        (gauge site)))
    (trans
      (Periodic.sumSitesAdd
        (λ site → first site * gauge site)
        (λ site →
          second site * gauge site
          + (third site * gauge site + fourth site * gauge site)))
      (cong
        (Periodic.fieldInner first gauge +_)
        (trans
          (Periodic.sumSitesAdd
            (λ site → second site * gauge site)
            (λ site → third site * gauge site + fourth site * gauge site))
          (cong
            (Periodic.fieldInner second gauge +_)
            (Periodic.sumSitesAdd
              (λ site → third site * gauge site)
              (λ site → fourth site * gauge site))))))

axisBackwardPairingFold : ∀ field gauge →
  Sums.sumRational GaugeFirst.axes4
    (λ axis →
      Periodic.fieldInner
        (Periodic.backwardDifference axis (field axis)) gauge)
  ≡ Periodic.fieldInner (Periodic.periodicDivergence field) gauge
axisBackwardPairingFold field gauge =
  trans
    (ℚRing.solve-∀
      (Periodic.fieldInner
        (Periodic.backwardDifference Periodic.axis0 (field Periodic.axis0)) gauge)
      (Periodic.fieldInner
        (Periodic.backwardDifference Periodic.axis1 (field Periodic.axis1)) gauge)
      (Periodic.fieldInner
        (Periodic.backwardDifference Periodic.axis2 (field Periodic.axis2)) gauge)
      (Periodic.fieldInner
        (Periodic.backwardDifference Periodic.axis3 (field Periodic.axis3)) gauge))
    (sym
      (fieldInnerFourSumLeft
        (Periodic.backwardDifference Periodic.axis0 (field Periodic.axis0))
        (Periodic.backwardDifference Periodic.axis1 (field Periodic.axis1))
        (Periodic.backwardDifference Periodic.axis2 (field Periodic.axis2))
        (Periodic.backwardDifference Periodic.axis3 (field Periodic.axis3))
        gauge))

------------------------------------------------------------------------
-- Pairing of one Lie component on the literal axis-major bond carrier.
------------------------------------------------------------------------

bondCellCandidatePairingExact :
  ∀ vector multiplier coordinate →
  Sums.sumRational Cell.bondCells4
    (λ cell →
      vector (pair coordinate cell)
      * flatNegativeGradientState multiplier (pair coordinate cell))
  ≡ Periodic.fieldInner
      (Periodic.periodicDivergence (stateBondField vector coordinate))
      (multiplierField multiplier coordinate)
bondCellCandidatePairingExact vector multiplier coordinate =
  let
    stateField = stateBondField vector coordinate
    gauge = multiplierField multiplier coordinate

    asAxes :
      Sums.sumRational Cell.bondCells4
        (λ cell →
          vector (pair coordinate cell)
          * flatNegativeGradientState multiplier (pair coordinate cell))
      ≡ Sums.sumRational GaugeFirst.axes4
          (λ axis →
            Sums.sumRational (Block.physicalBlockSites Path4.side4)
              (λ site →
                stateField axis site
                * (- Periodic.forwardDifference axis gauge site)))
    asAxes =
      Fubini.sumCartesian
        GaugeFirst.axes4
        (Block.physicalBlockSites Path4.side4)
        (λ cell →
          vector (pair coordinate cell)
          * flatNegativeGradientState multiplier (pair coordinate cell))

    asPeriodicInner :
      Sums.sumRational GaugeFirst.axes4
        (λ axis →
          Sums.sumRational (Block.physicalBlockSites Path4.side4)
            (λ site →
              stateField axis site
              * (- Periodic.forwardDifference axis gauge site)))
      ≡ Sums.sumRational GaugeFirst.axes4
          (λ axis →
            Periodic.fieldInner (stateField axis)
              (λ site → - Periodic.forwardDifference axis gauge site))
    asPeriodicInner =
      Sums.sumRationalCong GaugeFirst.axes4 _ _
        (λ axis →
          sym
            (Bridge.sumSitesMatchesGlobalSiteSum
              (λ site →
                stateField axis site
                * (- Periodic.forwardDifference axis gauge site))))

    integrated :
      Sums.sumRational GaugeFirst.axes4
        (λ axis →
          Periodic.fieldInner (stateField axis)
            (λ site → - Periodic.forwardDifference axis gauge site))
      ≡ Sums.sumRational GaugeFirst.axes4
          (λ axis →
            Periodic.fieldInner
              (Periodic.backwardDifference axis (stateField axis)) gauge)
    integrated =
      Sums.sumRationalCong GaugeFirst.axes4 _ _
        (λ axis → periodicAxisNegativeGradientAdjoint axis (stateField axis) gauge)
  in
  trans asAxes
    (trans asPeriodicInner
      (trans integrated (axisBackwardPairingFold stateField gauge)))

stateCandidatePairingExact : ∀ vector multiplier →
  KKT.stateDot vector (flatNegativeGradientState multiplier)
  ≡ Sums.sumRational Coordinates.lieCoordinates3
      (λ coordinate →
        Periodic.fieldInner
          (Periodic.periodicDivergence (stateBondField vector coordinate))
          (multiplierField multiplier coordinate))
stateCandidatePairingExact vector multiplier =
  trans
    (Fubini.sumCartesian
      Coordinates.lieCoordinates3 Cell.bondCells4
      (λ selected →
        vector selected * flatNegativeGradientState multiplier selected))
    (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
      (bondCellCandidatePairingExact vector multiplier))

------------------------------------------------------------------------
-- The physical identity-background gauge matrix has the same pairing.
------------------------------------------------------------------------

rowCoordinatePairingExact : ∀ vector multiplier coordinate →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site →
      FlatGauge.flatGaugeFirst
        (Coordinates.decodePhysicalSU2 vector) (pair coordinate site)
      * multiplier (pair coordinate site))
  ≡ Periodic.fieldInner
      (Periodic.periodicDivergence (stateBondField vector coordinate))
      (multiplierField multiplier coordinate)
rowCoordinatePairingExact vector multiplier coordinate =
  let
    term : Periodic.Site4 → ℚ
    term site =
      Periodic.periodicDivergence (stateBondField vector coordinate) site
      * multiplierField multiplier coordinate site

    pointwise : ∀ site →
      FlatGauge.flatGaugeFirst
        (Coordinates.decodePhysicalSU2 vector) (pair coordinate site)
      * multiplier (pair coordinate site)
      ≡ term site
    pointwise site = refl
  in
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4) _ term pointwise)
    (sym (Bridge.sumSitesMatchesGlobalSiteSum term))

identityGaugeConstraintPairingExact : ∀ vector multiplier →
  Rect.finiteDot selectedFlatGaugeRowCarrier
    (identityGaugeConstraintApply vector) multiplier
  ≡ Sums.sumRational Coordinates.lieCoordinates3
      (λ coordinate →
        Periodic.fieldInner
          (Periodic.periodicDivergence (stateBondField vector coordinate))
          (multiplierField multiplier coordinate))
identityGaugeConstraintPairingExact vector multiplier =
  trans
    (Sums.sumRationalCong
      (Basis.elements Rows.selectedGaugeRowFiniteSelector)
      (λ row → identityGaugeConstraintApply vector row * multiplier row)
      (λ row →
        FlatGauge.flatGaugeFirst
          (Coordinates.decodePhysicalSU2 vector) row * multiplier row)
      (λ { (pair coordinate site) →
        cong (_* multiplier (pair coordinate site))
          (identityGaugeConstraintApplyExact vector coordinate site) }))
    (trans
      (Fubini.sumCartesian
        Coordinates.lieCoordinates3
        (Block.physicalBlockSites Path4.side4)
        (λ row →
          FlatGauge.flatGaugeFirst
            (Coordinates.decodePhysicalSU2 vector) row * multiplier row))
      (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
        (rowCoordinatePairingExact vector multiplier)))

actualFlatGaugeAdjointPairingExact : ∀ vector multiplier →
  KKT.stateDot vector (actualFlatGaugeAdjoint multiplier)
  ≡ KKT.stateDot vector (flatNegativeGradientState multiplier)
actualFlatGaugeAdjointPairingExact vector multiplier =
  let
    rectangularAdjoint =
      Rect.rectangularAdjointExact
        KKT.physicalStateCarrier selectedFlatGaugeRowCarrier
        identityGaugeConstraintMatrix vector multiplier
  in
  trans
    (sym rectangularAdjoint)
    (trans
      (identityGaugeConstraintPairingExact vector multiplier)
      (sym (stateCandidatePairingExact vector multiplier)))

stateDotIsPhysicalCoordinateDot : ∀ left right →
  KKT.stateDot left right ≡ Coordinates.physicalCoordinateDot left right
stateDotIsPhysicalCoordinateDot left right = refl

actualFlatGaugeAdjointPointwiseExact : ∀ multiplier coordinate →
  actualFlatGaugeAdjoint multiplier coordinate
  ≡ flatNegativeGradientState multiplier coordinate
actualFlatGaugeAdjointPointwiseExact multiplier coordinate =
  let
    basis = Basis.physicalBasis coordinate
    pairing = actualFlatGaugeAdjointPairingExact basis multiplier

    actualExtract :
      KKT.stateDot basis (actualFlatGaugeAdjoint multiplier)
      ≡ actualFlatGaugeAdjoint multiplier coordinate
    actualExtract =
      trans
        (stateDotIsPhysicalCoordinateDot basis (actualFlatGaugeAdjoint multiplier))
        (Basis.physicalBasisDotExact coordinate (actualFlatGaugeAdjoint multiplier))

    candidateExtract :
      KKT.stateDot basis (flatNegativeGradientState multiplier)
      ≡ flatNegativeGradientState multiplier coordinate
    candidateExtract =
      trans
        (stateDotIsPhysicalCoordinateDot basis (flatNegativeGradientState multiplier))
        (Basis.physicalBasisDotExact coordinate (flatNegativeGradientState multiplier))
  in
  trans (sym actualExtract) (trans pairing candidateExtract)

------------------------------------------------------------------------
-- Norm identity and the strict flat reduced Gram floor.
------------------------------------------------------------------------

gaugeMultiplierPeriodicGradientEnergy : GaugeMultiplier → ℚ
gaugeMultiplierPeriodicGradientEnergy multiplier =
  Sums.sumRational Coordinates.lieCoordinates3
    (λ coordinate →
      Sums.sumRational GaugeFirst.axes4
        (λ axis →
          Periodic.fieldNormSq
            (Periodic.forwardDifference axis
              (multiplierField multiplier coordinate))))

gaugeMultiplierPeriodicWrapEnergy : GaugeMultiplier → ℚ
gaugeMultiplierPeriodicWrapEnergy multiplier =
  Sums.sumRational Coordinates.lieCoordinates3
    (λ coordinate →
      Sums.sumRational GaugeFirst.axes4
        (λ axis →
          Bridge.axisBoundaryWrapEnergy axis
            (multiplierField multiplier coordinate)))

scalarPeriodicGradientOpenPlusWrap : ∀ field →
  Sums.sumRational GaugeFirst.axes4
    (λ axis →
      Periodic.fieldNormSq (Periodic.forwardDifference axis field))
  ≡ Poincare.globalDirectionalEnergy field
    + Sums.sumRational GaugeFirst.axes4
        (λ axis → Bridge.axisBoundaryWrapEnergy axis field)
scalarPeriodicGradientOpenPlusWrap field =
  trans
    (Sums.sumRationalCong GaugeFirst.axes4 _ _
      (λ axis → Bridge.axisPeriodicDifferenceSplitsOpenAndBoundary axis field))
    (trans
      (Fubini.sumRationalAdd GaugeFirst.axes4
        (λ axis →
          DASHI.Physics.YangMills.BalabanPath4PhysicalComponentPoincareExact.axisDirectionalEnergy
            axis field)
        (λ axis → Bridge.axisBoundaryWrapEnergy axis field))
      (cong
        (_+ Sums.sumRational GaugeFirst.axes4
          (λ axis → Bridge.axisBoundaryWrapEnergy axis field))
        (ℚRing.solve-∀)))

scalarPeriodicWrapNonnegative : ∀ field →
  0ℚ ≤ Sums.sumRational GaugeFirst.axes4
    (λ axis → Bridge.axisBoundaryWrapEnergy axis field)
scalarPeriodicWrapNonnegative field =
  DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact.sumNonnegative
    GaugeFirst.axes4
    (λ axis → Bridge.axisBoundaryWrapEnergy axis field)
    (λ axis → Bridge.axisBoundaryWrapEnergyNonnegative axis field)

gaugeMultiplierPeriodicGradientOpenPlusWrap : ∀ multiplier →
  gaugeMultiplierPeriodicGradientEnergy multiplier
  ≡ FlatFloor.gaugeMultiplierGradientEnergy multiplier
    + gaugeMultiplierPeriodicWrapEnergy multiplier
gaugeMultiplierPeriodicGradientOpenPlusWrap multiplier =
  trans
    (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
      (λ coordinate →
        scalarPeriodicGradientOpenPlusWrap
          (multiplierField multiplier coordinate)))
    (Fubini.sumRationalAdd Coordinates.lieCoordinates3
      (λ coordinate →
        Poincare.globalDirectionalEnergy
          (multiplierField multiplier coordinate))
      (λ coordinate →
        Sums.sumRational GaugeFirst.axes4
          (λ axis → Bridge.axisBoundaryWrapEnergy axis
            (multiplierField multiplier coordinate))))

gaugeMultiplierPeriodicWrapNonnegative : ∀ multiplier →
  0ℚ ≤ gaugeMultiplierPeriodicWrapEnergy multiplier
gaugeMultiplierPeriodicWrapNonnegative multiplier =
  DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact.sumNonnegative
    Coordinates.lieCoordinates3
    (λ coordinate →
      Sums.sumRational GaugeFirst.axes4
        (λ axis → Bridge.axisBoundaryWrapEnergy axis
          (multiplierField multiplier coordinate)))
    (λ coordinate → scalarPeriodicWrapNonnegative
      (multiplierField multiplier coordinate))

gaugeMultiplierOpenBelowPeriodic : ∀ multiplier →
  FlatFloor.gaugeMultiplierGradientEnergy multiplier
  ≤ gaugeMultiplierPeriodicGradientEnergy multiplier
gaugeMultiplierOpenBelowPeriodic multiplier =
  subst
    (λ upper →
      FlatFloor.gaugeMultiplierGradientEnergy multiplier ≤ upper)
    (sym (gaugeMultiplierPeriodicGradientOpenPlusWrap multiplier))
    (ℚP.+-monoʳ-≤
      (FlatFloor.gaugeMultiplierGradientEnergy multiplier)
      (gaugeMultiplierPeriodicWrapNonnegative multiplier))

flatNegativeGradientStateNormExact : ∀ multiplier →
  KKT.stateNormSq (flatNegativeGradientState multiplier)
  ≡ gaugeMultiplierPeriodicGradientEnergy multiplier
flatNegativeGradientStateNormExact multiplier =
  trans
    (Fubini.sumCartesian
      Coordinates.lieCoordinates3 Cell.bondCells4
      (λ selected →
        flatNegativeGradientState multiplier selected
        * flatNegativeGradientState multiplier selected))
    (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
      (λ coordinate →
        trans
          (Fubini.sumCartesian GaugeFirst.axes4
            (Block.physicalBlockSites Path4.side4)
            (λ cell →
              flatNegativeGradientState multiplier (pair coordinate cell)
              * flatNegativeGradientState multiplier (pair coordinate cell)))
          (Sums.sumRationalCong GaugeFirst.axes4 _ _
            (λ axis →
              trans
                (Sums.sumRationalCong
                  (Block.physicalBlockSites Path4.side4) _ _
                  (λ site → ℚRing.solve-∀
                    (Periodic.forwardDifference axis
                      (multiplierField multiplier coordinate) site)))
                (sym
                  (Bridge.sumSitesMatchesGlobalSiteSum
                    (λ site →
                      Periodic.forwardDifference axis
                        (multiplierField multiplier coordinate) site
                      * Periodic.forwardDifference axis
                        (multiplierField multiplier coordinate) site))))))))

actualFlatGaugeAdjointNormExact : ∀ multiplier →
  KKT.stateNormSq (actualFlatGaugeAdjoint multiplier)
  ≡ gaugeMultiplierPeriodicGradientEnergy multiplier
actualFlatGaugeAdjointNormExact multiplier =
  trans
    (Sums.sumRationalCong Coordinates.physicalSU2Coordinates4 _ _
      (λ coordinate →
        cong₂ _*_
          (actualFlatGaugeAdjointPointwiseExact multiplier coordinate)
          (actualFlatGaugeAdjointPointwiseExact multiplier coordinate)))
    (flatNegativeGradientStateNormExact multiplier)

actualFlatGaugeGramQuadratic : GaugeMultiplier → ℚ
actualFlatGaugeGramQuadratic multiplier =
  KKT.stateNormSq (actualFlatGaugeAdjoint multiplier)

actualFlatGaugeGramReducedFloor :
  ∀ multiplier → FlatFloor.FlatGaugeReducedMultiplier multiplier →
  DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate.oneSixteenth
    * FlatFloor.gaugeMultiplierNormSq multiplier
  ≤ actualFlatGaugeGramQuadratic multiplier
actualFlatGaugeGramReducedFloor multiplier reduced =
  ℚP.≤-trans
    (FlatFloor.flatGaugeReducedPoincare multiplier reduced)
    (ℚP.≤-trans
      (gaugeMultiplierOpenBelowPeriodic multiplier)
      (subst
        (λ upper →
          gaugeMultiplierPeriodicGradientEnergy multiplier ≤ upper)
        (sym (actualFlatGaugeAdjointNormExact multiplier))
        ℚP.≤-refl))

selectedFlatGaugeAdjointIdentificationLevel : ProofLevel
selectedFlatGaugeAdjointIdentificationLevel = machineChecked

selectedFlatGaugeReducedGramFloorLevel : ProofLevel
selectedFlatGaugeReducedGramFloorLevel = machineChecked
