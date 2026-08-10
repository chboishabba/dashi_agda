module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeReducedFloorExact where

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
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Master-reconciled physical theorem.  At the identity background the actual
-- 768-row gauge-matrix transpose has the componentwise-mean-zero floor 1/16.
-- The exact selected-radius transpose defect is at most 3/1024.  Combining the
-- two through the finite rational perturbation inequality yields
--
--   (29/1024) ||lambda||^2 <= ||L_A^* lambda||^2
--
-- for every componentwise-mean-zero gauge multiplier whenever A satisfies the
-- literal relaxed inverse-link radius.  No downstream Round-34/41 selected-
-- background wrapper is required: the theorem consumes the physical radius
-- itself, so it can live directly on current master.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact as Variance
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as Global
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Perturb

GaugeMultiplier : Set
GaugeMultiplier = Defect.GaugeMultiplier

gaugeMultiplierRowNormSqExact : ∀ multiplier →
  Defect.gaugeMultiplierRowNormSq multiplier
  ≡ FlatFloor.gaugeMultiplierNormSq multiplier
gaugeMultiplierRowNormSqExact multiplier =
  let
    perCoordinate : ∀ coordinate →
      Sums.sumRational (Block.physicalBlockSites Path4.side4)
        (λ site → multiplier (pair coordinate site) * multiplier (pair coordinate site))
      ≡ Variance.globalNormSq
          (FlatFloor.gaugeMultiplierField multiplier coordinate)
    perCoordinate coordinate =
      trans
        (sym
          (Bridge.sumSitesMatchesGlobalSiteSum
            (λ site →
              multiplier (pair coordinate site) * multiplier (pair coordinate site))))
        (Global.periodicFieldNormSqMatchesGlobal
          (FlatFloor.gaugeMultiplierField multiplier coordinate))
  in
  trans
    (Fubini.sumCartesian
      Coordinates.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      (λ row → multiplier row * multiplier row))
    (trans
      (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _ perCoordinate)
      (ℚRing.solve-∀
        (Variance.globalNormSq
          (FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateX))
        (Variance.globalNormSq
          (FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateY))
        (Variance.globalNormSq
          (FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateZ))))

backgroundGaugeAdjoint :
  Physical.RationalSU2Background4 → GaugeMultiplier → KKT.StateVector
backgroundGaugeAdjoint background multiplier =
  Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
    (Rect.transposeRectangular
      (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background))
    multiplier

sumRationalAddExact : ∀ {A : Set} values (left right : A → ℚ) →
  Sums.sumRational values (λ value → left value + right value)
  ≡ Sums.sumRational values left + Sums.sumRational values right
sumRationalAddExact [] left right = ℚRing.solve []
sumRationalAddExact (value ∷ values) left right
  rewrite sumRationalAddExact values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (Sums.sumRational values left)
    (Sums.sumRational values right)

backgroundGaugeAdjointSplits : ∀ background multiplier coordinate →
  backgroundGaugeAdjoint background multiplier coordinate
  ≡ FlatAdjoint.actualFlatGaugeAdjoint multiplier coordinate
      + Defect.gaugeAdjointDefectApply background multiplier coordinate
backgroundGaugeAdjointSplits background multiplier coordinate =
  let
    rows = Defect.gaugeRows

    pointwise : ∀ row →
      GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
          background row coordinate * multiplier row
      ≡ GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
          Physical.identityBackground row coordinate * multiplier row
        + Defect.gaugeDefectMatrix background row coordinate * multiplier row
    pointwise row = ℚRing.solve-∀
      (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row coordinate)
      (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
        Physical.identityBackground row coordinate)
      (multiplier row)
  in
  trans
    (Sums.sumRationalCong rows _ _ pointwise)
    (sumRationalAddExact rows
      (λ row →
        GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
          Physical.identityBackground row coordinate * multiplier row)
      (λ row →
        Defect.gaugeDefectMatrix background row coordinate * multiplier row))

record ReducedGaugeMultiplier : Set where
  constructor reducedGaugeMultiplier
  field
    multiplier : GaugeMultiplier
    reduced : FlatFloor.FlatGaugeReducedMultiplier multiplier
open ReducedGaugeMultiplier public

reducedGaugeMultiplierNormSq : ReducedGaugeMultiplier → ℚ
reducedGaugeMultiplierNormSq selected =
  FlatFloor.gaugeMultiplierNormSq (multiplier selected)

backgroundGaugeAdjointPerturbationData :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  Perturb.ReducedFloorPerturbationData KKT.physicalStateCarrier
backgroundGaugeAdjointPerturbationData background radius = record
  { Perturb.ReducedFloorPerturbationData.Multiplier = ReducedGaugeMultiplier
  ; Perturb.ReducedFloorPerturbationData.multiplierNormSq = reducedGaugeMultiplierNormSq
  ; Perturb.ReducedFloorPerturbationData.reference =
      λ selected → FlatAdjoint.actualFlatGaugeAdjoint (multiplier selected)
  ; Perturb.ReducedFloorPerturbationData.defect =
      λ selected → Defect.gaugeAdjointDefectApply background (multiplier selected)
  ; Perturb.ReducedFloorPerturbationData.full =
      λ selected → backgroundGaugeAdjoint background (multiplier selected)
  ; Perturb.ReducedFloorPerturbationData.referenceFloor = LDL.oneSixteenth
  ; Perturb.ReducedFloorPerturbationData.defectCoefficient =
      Defect.selectedAdjointDefectCoefficient
  ; Perturb.ReducedFloorPerturbationData.fullSplits =
      λ selected coordinate →
        backgroundGaugeAdjointSplits background (multiplier selected) coordinate
  ; Perturb.ReducedFloorPerturbationData.referenceCoercive =
      λ selected →
        FlatAdjoint.actualFlatGaugeGramReducedFloor
          (multiplier selected) (reduced selected)
  ; Perturb.ReducedFloorPerturbationData.defectUpper =
      λ selected →
        subst
          (λ norm →
            Defect.gaugeAdjointDefectNormSq background (multiplier selected)
            ≤ Defect.selectedAdjointDefectCoefficient * norm)
          (gaugeMultiplierRowNormSqExact (multiplier selected))
          (Defect.gaugeAdjointDefectSelectedRadiusBound
            background radius (multiplier selected))
  }

selectedBackgroundGaugeReducedFloor : ℚ
selectedBackgroundGaugeReducedFloor = + 29 / 1024

selectedBackgroundGaugeReducedFloorExact :
  Perturb.oneHalf * LDL.oneSixteenth
    - Defect.selectedAdjointDefectCoefficient
  ≡ selectedBackgroundGaugeReducedFloor
selectedBackgroundGaugeReducedFloorExact = ℚRing.solve []

selectedBackgroundGaugeAdjointReducedFloor :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ selected →
  selectedBackgroundGaugeReducedFloor * reducedGaugeMultiplierNormSq selected
  ≤ KKT.stateNormSq
      (backgroundGaugeAdjoint background (multiplier selected))
selectedBackgroundGaugeAdjointReducedFloor background radius selected =
  subst
    (λ coefficient →
      coefficient * reducedGaugeMultiplierNormSq selected
      ≤ KKT.stateNormSq (backgroundGaugeAdjoint background (multiplier selected)))
    selectedBackgroundGaugeReducedFloorExact
    (Perturb.perturbedReducedFloor
      (backgroundGaugeAdjointPerturbationData background radius) selected)

selectedBackgroundGaugeReducedFloorLevel : ProofLevel
selectedBackgroundGaugeReducedFloorLevel = machineChecked
