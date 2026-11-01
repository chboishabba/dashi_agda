module DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointPoincareFloorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01240221.
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
-- Finish the flat source-scale gauge sector on the literal L=13 matrix from
-- BalabanPath13FlatGaugeAdjointMatrixExact.  On each 13-site axis fibre the
-- periodic gradient energy is exactly
--
--       open Path13 energy + one nonnegative wrap square.
--
-- Therefore the periodic transpose norm dominates the open-edge energy used
-- by the exact Path13 Poincare certificate.  Summing over four axes and three
-- su(2) coordinates gives, for componentwise global-mean-zero multipliers,
--
--       (1/18) ||lambda||^2 <= ||L_g,0^* lambda||^2.
--
-- Both sides live on the source-faithful carriers: 3*13^4 multiplier rows and
-- 3*4*13^4=342732 physical state columns.  No side-four floor is transported.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanPath13PhysicalFibreMatchExact as Match
import DASHI.Physics.YangMills.BalabanPath13DirectionalEnergyContractionExact as Direction
import DASHI.Physics.YangMills.BalabanPath13FourAxisPhysicalPoincareExact as ScalarPoincare
import DASHI.Physics.YangMills.BalabanPath13SU2FourAxisPhysicalPoincareExact as SU2Poincare
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointMatrixExact as Flat

shiftForwardInsertAxis13 :
  ∀ axis coordinate transverse →
  Flat.shiftForward13 axis (insertAxis axis coordinate transverse)
  ≡ insertAxis axis (Flat.cyclicNext coordinate) transverse
shiftForwardInsertAxis13 zeroᵢ coordinate (pair x1 (pair x2 x3)) = refl
shiftForwardInsertAxis13 (sucᵢ zeroᵢ) coordinate
    (pair x0 (pair x2 x3)) = refl
shiftForwardInsertAxis13 (sucᵢ (sucᵢ zeroᵢ)) coordinate
    (pair x0 (pair x1 x3)) = refl
shiftForwardInsertAxis13 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) coordinate
    (pair x0 (pair x1 x2)) = refl

periodicFibreEnergy13 :
  SiteField Side13.side13 → Axis4 →
  Triple (CyclicIndex Side13.side13) → ℚ
periodicFibreEnergy13 field axis transverse =
  sumRational (allCyclicIndices Side13.side13)
    (λ coordinate →
      sq
        (field (insertAxis axis (Flat.cyclicNext coordinate) transverse)
        - field (insertAxis axis coordinate transverse)))

periodicWrapEnergy13 :
  SiteField Side13.side13 → Axis4 →
  Triple (CyclicIndex Side13.side13) → ℚ
periodicWrapEnergy13 field axis transverse =
  sq
    (field (insertAxis axis Match.index0 transverse)
    - field (insertAxis axis Match.index12 transverse))

periodicFibreEnergyExpansion13 : ∀ field axis transverse →
  periodicFibreEnergy13 field axis transverse
  ≡ sqDiff (field (insertAxis axis Match.index1 transverse))
       (field (insertAxis axis Match.index0 transverse))
   + (sqDiff (field (insertAxis axis Match.index2 transverse))
       (field (insertAxis axis Match.index1 transverse))
   + (sqDiff (field (insertAxis axis Match.index3 transverse))
       (field (insertAxis axis Match.index2 transverse))
   + (sqDiff (field (insertAxis axis Match.index4 transverse))
       (field (insertAxis axis Match.index3 transverse))
   + (sqDiff (field (insertAxis axis Match.index5 transverse))
       (field (insertAxis axis Match.index4 transverse))
   + (sqDiff (field (insertAxis axis Match.index6 transverse))
       (field (insertAxis axis Match.index5 transverse))
   + (sqDiff (field (insertAxis axis Match.index7 transverse))
       (field (insertAxis axis Match.index6 transverse))
   + (sqDiff (field (insertAxis axis Match.index8 transverse))
       (field (insertAxis axis Match.index7 transverse))
   + (sqDiff (field (insertAxis axis Match.index9 transverse))
       (field (insertAxis axis Match.index8 transverse))
   + (sqDiff (field (insertAxis axis Match.index10 transverse))
       (field (insertAxis axis Match.index9 transverse))
   + (sqDiff (field (insertAxis axis Match.index11 transverse))
       (field (insertAxis axis Match.index10 transverse))
   + (sqDiff (field (insertAxis axis Match.index12 transverse))
       (field (insertAxis axis Match.index11 transverse))
   + (sqDiff (field (insertAxis axis Match.index0 transverse))
       (field (insertAxis axis Match.index12 transverse))
   + 0ℚ)))))))))))))
periodicFibreEnergyExpansion13 field axis transverse = refl

openFibreEnergyExpansion13 : ∀ field axis transverse →
  physicalFibreEdgeEnergy field axis transverse
  ≡ sqDiff (field (insertAxis axis Match.index1 transverse))
       (field (insertAxis axis Match.index0 transverse))
   + (sqDiff (field (insertAxis axis Match.index2 transverse))
       (field (insertAxis axis Match.index1 transverse))
   + (sqDiff (field (insertAxis axis Match.index3 transverse))
       (field (insertAxis axis Match.index2 transverse))
   + (sqDiff (field (insertAxis axis Match.index4 transverse))
       (field (insertAxis axis Match.index3 transverse))
   + (sqDiff (field (insertAxis axis Match.index5 transverse))
       (field (insertAxis axis Match.index4 transverse))
   + (sqDiff (field (insertAxis axis Match.index6 transverse))
       (field (insertAxis axis Match.index5 transverse))
   + (sqDiff (field (insertAxis axis Match.index7 transverse))
       (field (insertAxis axis Match.index6 transverse))
   + (sqDiff (field (insertAxis axis Match.index8 transverse))
       (field (insertAxis axis Match.index7 transverse))
   + (sqDiff (field (insertAxis axis Match.index9 transverse))
       (field (insertAxis axis Match.index8 transverse))
   + (sqDiff (field (insertAxis axis Match.index10 transverse))
       (field (insertAxis axis Match.index9 transverse))
   + (sqDiff (field (insertAxis axis Match.index11 transverse))
       (field (insertAxis axis Match.index10 transverse))
   + (sqDiff (field (insertAxis axis Match.index12 transverse))
       (field (insertAxis axis Match.index11 transverse))
   + 0ℚ))))))))))))
openFibreEnergyExpansion13 field axis transverse = refl

periodicFibreSplitsOpenWrap13 : ∀ field axis transverse →
  periodicFibreEnergy13 field axis transverse
  ≡ physicalFibreEdgeEnergy field axis transverse
    + periodicWrapEnergy13 field axis transverse
periodicFibreSplitsOpenWrap13 field axis transverse
  rewrite periodicFibreEnergyExpansion13 field axis transverse
        | openFibreEnergyExpansion13 field axis transverse =
  ℚRing.solve-∀
    (field (insertAxis axis Match.index0 transverse))
    (field (insertAxis axis Match.index1 transverse))
    (field (insertAxis axis Match.index2 transverse))
    (field (insertAxis axis Match.index3 transverse))
    (field (insertAxis axis Match.index4 transverse))
    (field (insertAxis axis Match.index5 transverse))
    (field (insertAxis axis Match.index6 transverse))
    (field (insertAxis axis Match.index7 transverse))
    (field (insertAxis axis Match.index8 transverse))
    (field (insertAxis axis Match.index9 transverse))
    (field (insertAxis axis Match.index10 transverse))
    (field (insertAxis axis Match.index11 transverse))
    (field (insertAxis axis Match.index12 transverse))

axisPeriodicFibreEnergy13 : Axis4 → SiteField Side13.side13 → ℚ
axisPeriodicFibreEnergy13 axis field =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (periodicFibreEnergy13 field axis)

axisWrapEnergy13 : Axis4 → SiteField Side13.side13 → ℚ
axisWrapEnergy13 axis field =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (periodicWrapEnergy13 field axis)

axisPeriodicSplitsOpenWrap13 : ∀ axis field →
  axisPeriodicFibreEnergy13 axis field
  ≡ Direction.axisDirectionalEnergy axis field + axisWrapEnergy13 axis field
axisPeriodicSplitsOpenWrap13 axis field =
  trans
    (sumRationalCong
      (physicalTransverseCoordinates Side13.side13) _ _
      (periodicFibreSplitsOpenWrap13 field axis))
    (sumRationalAdd
      (physicalTransverseCoordinates Side13.side13)
      (physicalFibreEdgeEnergy field axis)
      (periodicWrapEnergy13 field axis))

axisWrapEnergyNonnegative13 : ∀ axis field →
  0ℚ ≤ axisWrapEnergy13 axis field
axisWrapEnergyNonnegative13 axis field =
  Schur.sumNonnegative
    (physicalTransverseCoordinates Side13.side13)
    (periodicWrapEnergy13 field axis)
    (λ transverse → FiniteL2.squareNonnegative
      (field (insertAxis axis Match.index0 transverse)
      - field (insertAxis axis Match.index12 transverse)))

axisPeriodicDominatesOpen13 : ∀ axis field →
  Direction.axisDirectionalEnergy axis field
  ≤ axisPeriodicFibreEnergy13 axis field
axisPeriodicDominatesOpen13 axis field =
  subst
    (λ upper → Direction.axisDirectionalEnergy axis field ≤ upper)
    (sym (axisPeriodicSplitsOpenWrap13 axis field))
    (subst
      (λ lower → lower ≤
        Direction.axisDirectionalEnergy axis field + axisWrapEnergy13 axis field)
      (ℚRing.solve-∀ (Direction.axisDirectionalEnergy axis field))
      (ℚP.+-mono-≤ ℚP.≤-refl (axisWrapEnergyNonnegative13 axis field)))

axisSitePeriodicEnergy13 : Axis4 → SiteField Side13.side13 → ℚ
axisSitePeriodicEnergy13 axis field =
  globalSiteSum
    (λ site → sq (Flat.forwardDifference13 axis field site))

axisSitePeriodicMatchesFibre13 : ∀ axis field →
  axisSitePeriodicEnergy13 axis field ≡ axisPeriodicFibreEnergy13 axis field
axisSitePeriodicMatchesFibre13 axis field =
  trans
    (sym
      (axisPartitionSumMatchesGlobal axis
        (λ site → sq (Flat.forwardDifference13 axis field site))))
    (sumRationalCong
      (physicalTransverseCoordinates Side13.side13) _ _
      (λ transverse →
        sumRationalCong (allCyclicIndices Side13.side13) _ _
          (λ coordinate →
            cong sq
              (trans
                (cong
                  (λ target → field target - field (insertAxis axis coordinate transverse))
                  (shiftForwardInsertAxis13 axis coordinate transverse))
                refl))))

componentPeriodicEnergyAsAxes13 :
  ∀ multiplier coordinate →
  Flat.periodicComponentGradientEnergy13 multiplier coordinate
  ≡ sumRational (allCyclicIndices four)
      (λ axis → axisPeriodicFibreEnergy13 axis
        (Flat.multiplierField13 multiplier coordinate))
componentPeriodicEnergyAsAxes13 multiplier coordinate =
  trans
    (sumCartesian
      (allCyclicIndices four)
      (physicalBlockSites Side13.side13)
      (λ cell →
        sq
          (Flat.forwardDifference13
            (first cell)
            (Flat.multiplierField13 multiplier coordinate)
            (second cell))))
    (sumRationalCong (allCyclicIndices four) _ _
      (λ axis → axisSitePeriodicMatchesFibre13 axis
        (Flat.multiplierField13 multiplier coordinate)))

sumAxesOpenEnergyExact13 : ∀ field →
  sumRational (allCyclicIndices four)
    (λ axis → Direction.axisDirectionalEnergy axis field)
  ≡ ScalarPoincare.globalDirectionalEnergy field
sumAxesOpenEnergyExact13 field = ℚRing.solve-∀
  (Direction.axisDirectionalEnergy zeroᵢ field)
  (Direction.axisDirectionalEnergy (sucᵢ zeroᵢ) field)
  (Direction.axisDirectionalEnergy (sucᵢ (sucᵢ zeroᵢ)) field)
  (Direction.axisDirectionalEnergy (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field)

componentPeriodicDominatesOpen13 : ∀ multiplier coordinate →
  ScalarPoincare.globalDirectionalEnergy
      (Flat.multiplierField13 multiplier coordinate)
  ≤ Flat.periodicComponentGradientEnergy13 multiplier coordinate
componentPeriodicDominatesOpen13 multiplier coordinate =
  let
    field = Flat.multiplierField13 multiplier coordinate
    summed = Schur.sumPointwiseBelow
      (allCyclicIndices four)
      (λ axis → Direction.axisDirectionalEnergy axis field)
      (λ axis → axisPeriodicFibreEnergy13 axis field)
      (λ axis → axisPeriodicDominatesOpen13 axis field)
  in
  subst
    (λ lower → lower ≤ Flat.periodicComponentGradientEnergy13 multiplier coordinate)
    (sym (sumAxesOpenEnergyExact13 field))
    (subst
      (λ upper →
        sumRational (allCyclicIndices four)
          (λ axis → Direction.axisDirectionalEnergy axis field)
        ≤ upper)
      (sym (componentPeriodicEnergyAsAxes13 multiplier coordinate))
      summed)

openSU2DirectionalEnergy13 : Flat.GaugeMultiplier13 → ℚ
openSU2DirectionalEnergy13 multiplier =
  sumRational Physical.lieCoordinates3
    (λ coordinate →
      ScalarPoincare.globalDirectionalEnergy
        (Flat.multiplierField13 multiplier coordinate))

periodicSU2DominatesOpen13 : ∀ multiplier →
  openSU2DirectionalEnergy13 multiplier
  ≤ Flat.periodicGaugeGradientEnergy13 multiplier
periodicSU2DominatesOpen13 multiplier =
  Schur.sumPointwiseBelow
    Physical.lieCoordinates3
    (λ coordinate →
      ScalarPoincare.globalDirectionalEnergy
        (Flat.multiplierField13 multiplier coordinate))
    (λ coordinate → Flat.periodicComponentGradientEnergy13 multiplier coordinate)
    (componentPeriodicDominatesOpen13 multiplier)

------------------------------------------------------------------------
-- Gauge multiplier norm and the final 1/18 flat floor.
------------------------------------------------------------------------

gaugeMultiplierNormSq13 : Flat.GaugeMultiplier13 → ℚ
gaugeMultiplierNormSq13 multiplier =
  sumRational Flat.gaugeRows13 (λ row → sq (multiplier row))

multiplierAsSU2SiteField13 :
  Flat.GaugeMultiplier13 → SU2Poincare.PhysicalSU2SiteField13
multiplierAsSU2SiteField13 multiplier coordinate site =
  multiplier (pair coordinate site)

gaugeMultiplierNormMatchesSU2SiteNorm13 : ∀ multiplier →
  gaugeMultiplierNormSq13 multiplier
  ≡ SU2Poincare.su2SiteNormSq (multiplierAsSU2SiteField13 multiplier)
gaugeMultiplierNormMatchesSU2SiteNorm13 multiplier =
  sumCartesian
    Physical.lieCoordinates3
    (physicalBlockSites Side13.side13)
    (λ row → sq (multiplier row))

openEnergyMatchesSU2Directional13 : ∀ multiplier →
  openSU2DirectionalEnergy13 multiplier
  ≡ SU2Poincare.su2DirectionalEnergy
      (multiplierAsSU2SiteField13 multiplier)
openEnergyMatchesSU2Directional13 multiplier = refl

record FlatGaugeReducedMultiplier13
    (multiplier : Flat.GaugeMultiplier13) : Set where
  field
    componentwiseMeanZero :
      SU2Poincare.SU2GlobalMeanZero (multiplierAsSU2SiteField13 multiplier)

open FlatGaugeReducedMultiplier13 public

flatGaugeAdjointPoincareFloor13 :
  ∀ multiplier → FlatGaugeReducedMultiplier13 multiplier →
  LDL.oneEighteenth * gaugeMultiplierNormSq13 multiplier
  ≤ Flat.flatGaugeAdjointNormSq13 multiplier
flatGaugeAdjointPoincareFloor13 multiplier reduced =
  let
    poincare = SU2Poincare.path13SU2FourAxisPhysicalPoincare
      (multiplierAsSU2SiteField13 multiplier)
      (componentwiseMeanZero reduced)

    openBelowPeriodic = periodicSU2DominatesOpen13 multiplier
  in
  subst
    (λ lower → lower ≤ Flat.flatGaugeAdjointNormSq13 multiplier)
    (cong (LDL.oneEighteenth *_)
      (sym (gaugeMultiplierNormMatchesSU2SiteNorm13 multiplier)))
    (ℚP.≤-trans
      (subst
        (λ upper →
          LDL.oneEighteenth
            * SU2Poincare.su2SiteNormSq
                (multiplierAsSU2SiteField13 multiplier)
          ≤ upper)
        (sym (openEnergyMatchesSU2Directional13 multiplier))
        poincare)
      (subst
        (λ upper → openSU2DirectionalEnergy13 multiplier ≤ upper)
        (sym (Flat.flatGaugeAdjointNormExact13 multiplier))
        openBelowPeriodic))

path13PeriodicOpenGaugeBridgeLevel : ProofLevel
path13PeriodicOpenGaugeBridgeLevel = machineChecked

path13FlatGaugeAdjointPoincareFloorLevel : ProofLevel
path13FlatGaugeAdjointPoincareFloorLevel = machineChecked
