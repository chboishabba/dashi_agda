module DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact where

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
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Migrate the selected-background gauge-adjoint perturbation to the literal
-- source scale without paying the 342732 state dimension.  For each L=13
-- link, the background-minus-flat transpose is the 3 x 3 adjoint-rotation
-- defect acting on the multiplier at the forward endpoint.  The generic exact
-- quaternion theorem gives, for every basis column,
--
--     component(defect)^2 <= 4 delta,
--
-- while a three-term scalar Cauchy estimate gives 12 delta per output Lie
-- coordinate.  Summing three output coordinates and four bond directions and
-- reindexing the 13-cycle exactly yields
--
--     ||D_A^* gamma||^2 <= 144 delta ||gamma||^2.
--
-- At Bałaban/DASHI's selected radius delta=4 rho^2, rho=1/8192,
--
--     144 delta = 9 / 1048576.
--
-- This is over twenty times sharper than the old side-four Frobenius
-- coefficient 3/1024 and, crucially, is independent of volume.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _/_; NonNegative)
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
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Quaternion
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointNormSquaredExact as AdjointNorm
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPath13PhysicalFibreMatchExact as Match
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointMatrixExact as Flat
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointPoincareFloorExact as FlatFloor

record RationalSU2Background13 : Set where
  field
    link : Axis4 → PhysicalBlockL Side13.side13 → Q.RationalQuaternion
    unitNorm : ∀ axis site → Norm.normSq (link axis site) ≡ 1ℚ
open RationalSU2Background13 public

inverseLink13 : RationalSU2Background13 → Axis4 →
  PhysicalBlockL Side13.side13 → Q.RationalQuaternion
inverseLink13 background axis site =
  Quaternion.quaternionConjugate (link background axis site)

inverseLinkNormSqExact13 : ∀ background axis site →
  Norm.normSq (inverseLink13 background axis site) ≡ 1ℚ
inverseLinkNormSqExact13 background axis site =
  trans
    (AdjointNorm.physicalConjugateNormSqExact (link background axis site))
    (unitNorm background axis site)

record SelectedInverseLinkRadius13 (background : RationalSU2Background13) : Set where
  field
    inverseLinkDefectBound : ∀ axis site →
      Norm.normSq
        (Telescope._-q_ (inverseLink13 background axis site) Q.oneQ)
      ≤ Relaxed.fourRhoSquare
open SelectedInverseLinkRadius13 public

basisQuaternion : Physical.LieCoordinate3 → Q.RationalQuaternion
basisQuaternion Physical.coordinateX = Q.quat 0ℚ 1ℚ 0ℚ 0ℚ
basisQuaternion Physical.coordinateY = Q.quat 0ℚ 0ℚ 1ℚ 0ℚ
basisQuaternion Physical.coordinateZ = Q.quat 0ℚ 0ℚ 0ℚ 1ℚ

basisQuaternionNormSqOne : ∀ coordinate →
  Norm.normSq (basisQuaternion coordinate) ≡ 1ℚ
basisQuaternionNormSqOne Physical.coordinateX = refl
basisQuaternionNormSqOne Physical.coordinateY = refl
basisQuaternionNormSqOne Physical.coordinateZ = refl

quaternionCoordinate : Physical.LieCoordinate3 → Q.RationalQuaternion → ℚ
quaternionCoordinate Physical.coordinateX value = Q.q1 value
quaternionCoordinate Physical.coordinateY value = Q.q2 value
quaternionCoordinate Physical.coordinateZ value = Q.q3 value

coordinateSquareBelowNormSq : ∀ coordinate value →
  sq (quaternionCoordinate coordinate value) ≤ Norm.normSq value
coordinateSquareBelowNormSq Physical.coordinateX (Q.quat q0 q1 q2 q3) =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst (λ candidate → 0ℚ ≤ candidate)
      (ℚRing.solve-∀ q0 q1 q2 q3)
      (FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.squareNonnegative q0)
          (FiniteL2.squareNonnegative q2))
        (FiniteL2.squareNonnegative q3)))
coordinateSquareBelowNormSq Physical.coordinateY (Q.quat q0 q1 q2 q3) =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst (λ candidate → 0ℚ ≤ candidate)
      (ℚRing.solve-∀ q0 q1 q2 q3)
      (FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.squareNonnegative q0)
          (FiniteL2.squareNonnegative q1))
        (FiniteL2.squareNonnegative q3)))
coordinateSquareBelowNormSq Physical.coordinateZ (Q.quat q0 q1 q2 q3) =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst (λ candidate → 0ℚ ≤ candidate)
      (ℚRing.solve-∀ q0 q1 q2 q3)
      (FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.squareNonnegative q0)
          (FiniteL2.squareNonnegative q1))
        (FiniteL2.squareNonnegative q2)))

adjointDefect13 : RationalSU2Background13 → Axis4 →
  PhysicalBlockL Side13.side13 → Physical.LieCoordinate3 → Q.RationalQuaternion
adjointDefect13 background axis site inputCoordinate =
  Adjoint.adjointDefect
    (inverseLink13 background axis site)
    (basisQuaternion inputCoordinate)

adjointDefectCoordinate13 : RationalSU2Background13 →
  Physical.LieCoordinate3 → Physical.LieCoordinate3 → Axis4 →
  PhysicalBlockL Side13.side13 → ℚ
adjointDefectCoordinate13 background outputCoordinate inputCoordinate axis site =
  quaternionCoordinate outputCoordinate
    (adjointDefect13 background axis site inputCoordinate)

adjointDefectNormSqBound13 :
  ∀ background → SelectedInverseLinkRadius13 background →
  ∀ axis site inputCoordinate →
  Norm.normSq (adjointDefect13 background axis site inputCoordinate)
  ≤ (+ 4 / 1) * Relaxed.fourRhoSquare
adjointDefectNormSqBound13 background radius axis site inputCoordinate =
  let
    raw = AdjointNorm.unitAdjointDefectNormSqBound
      (inverseLink13 background axis site)
      (basisQuaternion inputCoordinate)
      (inverseLinkNormSqExact13 background axis site)
    radiusScaled = Norm.scaleNonnegative
      (+ 4 / 1) (ℚP.nonNegative⁻¹ (+ 4 / 1))
      (inverseLinkDefectBound radius axis site)
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        (+ 4 / 1)
          * Norm.normSq
              (Telescope._-q_ (inverseLink13 background axis site) Q.oneQ)
          * Norm.normSq (basisQuaternion inputCoordinate)
        ≤ upper)
      (ℚRing.solve-∀ Relaxed.fourRhoSquare)
      (subst
        (λ left → left ≤ (+ 4 / 1) * Relaxed.fourRhoSquare)
        (trans
          (cong
            ((+ 4 / 1)
              * Norm.normSq
                  (Telescope._-q_ (inverseLink13 background axis site) Q.oneQ) *_)
            (basisQuaternionNormSqOne inputCoordinate))
          (ℚRing.solve-∀
            (Norm.normSq
              (Telescope._-q_ (inverseLink13 background axis site) Q.oneQ))))
        radiusScaled))

adjointDefectCoordinateSquareBound13 :
  ∀ background → SelectedInverseLinkRadius13 background →
  ∀ outputCoordinate inputCoordinate axis site →
  sq (adjointDefectCoordinate13
      background outputCoordinate inputCoordinate axis site)
  ≤ (+ 4 / 1) * Relaxed.fourRhoSquare
adjointDefectCoordinateSquareBound13
    background radius outputCoordinate inputCoordinate axis site =
  ℚP.≤-trans
    (coordinateSquareBelowNormSq outputCoordinate
      (adjointDefect13 background axis site inputCoordinate))
    (adjointDefectNormSqBound13 background radius axis site inputCoordinate)

StateVector13 : Set
StateVector13 = Physical.PhysicalSU2Coordinate Side13.side13 → ℚ

gaugeAdjointDefect13 : RationalSU2Background13 →
  Flat.GaugeMultiplier13 → StateVector13
gaugeAdjointDefect13 background multiplier
    (pair inputCoordinate (pair axis site)) =
  - (adjointDefectCoordinate13 background Physical.coordinateX
        inputCoordinate axis site
      * multiplier (pair Physical.coordinateX (Flat.shiftForward13 axis site))
    + (adjointDefectCoordinate13 background Physical.coordinateY
        inputCoordinate axis site
      * multiplier (pair Physical.coordinateY (Flat.shiftForward13 axis site))
    + adjointDefectCoordinate13 background Physical.coordinateZ
        inputCoordinate axis site
      * multiplier (pair Physical.coordinateZ (Flat.shiftForward13 axis site))))

threeTermSquareBound : ∀ a b c →
  sq (a + (b + c)) ≤ (+ 3 / 1) * (sq a + sq b + sq c)
threeTermSquareBound a b c =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst (λ candidate → 0ℚ ≤ candidate)
      (ℚRing.solve-∀ a b c)
      (FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.squareNonnegative (a - b))
          (FiniteL2.squareNonnegative (a - c)))
        (FiniteL2.squareNonnegative (b - c))))

outputStateDefectSquareBound13 :
  ∀ background → SelectedInverseLinkRadius13 background →
  ∀ multiplier inputCoordinate axis site →
  sq (gaugeAdjointDefect13 background multiplier
      (pair inputCoordinate (pair axis site)))
  ≤ (+ 12 / 1) * Relaxed.fourRhoSquare
      * (sq (multiplier
          (pair Physical.coordinateX (Flat.shiftForward13 axis site)))
        + sq (multiplier
          (pair Physical.coordinateY (Flat.shiftForward13 axis site)))
        + sq (multiplier
          (pair Physical.coordinateZ (Flat.shiftForward13 axis site))))
outputStateDefectSquareBound13
    background radius multiplier inputCoordinate axis site =
  let
    gx = multiplier (pair Physical.coordinateX (Flat.shiftForward13 axis site))
    gy = multiplier (pair Physical.coordinateY (Flat.shiftForward13 axis site))
    gz = multiplier (pair Physical.coordinateZ (Flat.shiftForward13 axis site))
    cx = adjointDefectCoordinate13 background Physical.coordinateX
      inputCoordinate axis site
    cy = adjointDefectCoordinate13 background Physical.coordinateY
      inputCoordinate axis site
    cz = adjointDefectCoordinate13 background Physical.coordinateZ
      inputCoordinate axis site
    squareSum = threeTermSquareBound (cx * gx) (cy * gy) (cz * gz)
    xBound : sq (cx * gx)
      ≤ ((+ 4 / 1) * Relaxed.fourRhoSquare) * sq gx
    xBound =
      subst (λ left → left ≤ ((+ 4 / 1) * Relaxed.fourRhoSquare) * sq gx)
        (ℚRing.solve-∀ cx gx)
        (let instance gxNN : NonNegative (sq gx)
              gxNN = ℚ.nonNegative (FiniteL2.squareNonnegative gx)
         in ℚP.*-monoʳ-≤-nonNeg (sq gx)
           (adjointDefectCoordinateSquareBound13
             background radius Physical.coordinateX inputCoordinate axis site))
    yBound : sq (cy * gy)
      ≤ ((+ 4 / 1) * Relaxed.fourRhoSquare) * sq gy
    yBound =
      subst (λ left → left ≤ ((+ 4 / 1) * Relaxed.fourRhoSquare) * sq gy)
        (ℚRing.solve-∀ cy gy)
        (let instance gyNN : NonNegative (sq gy)
              gyNN = ℚ.nonNegative (FiniteL2.squareNonnegative gy)
         in ℚP.*-monoʳ-≤-nonNeg (sq gy)
           (adjointDefectCoordinateSquareBound13
             background radius Physical.coordinateY inputCoordinate axis site))
    zBound : sq (cz * gz)
      ≤ ((+ 4 / 1) * Relaxed.fourRhoSquare) * sq gz
    zBound =
      subst (λ left → left ≤ ((+ 4 / 1) * Relaxed.fourRhoSquare) * sq gz)
        (ℚRing.solve-∀ cz gz)
        (let instance gzNN : NonNegative (sq gz)
              gzNN = ℚ.nonNegative (FiniteL2.squareNonnegative gz)
         in ℚP.*-monoʳ-≤-nonNeg (sq gz)
           (adjointDefectCoordinateSquareBound13
             background radius Physical.coordinateZ inputCoordinate axis site))
    components = ℚP.+-mono-≤ (ℚP.+-mono-≤ xBound yBound) zBound
    scaledComponents = Norm.scaleNonnegative
      (+ 3 / 1) (ℚP.nonNegative⁻¹ (+ 3 / 1)) components
  in
  ℚP.≤-trans
    (subst
      (λ lower → lower
        ≤ (+ 3 / 1) * (sq (cx * gx) + sq (cy * gy) + sq (cz * gz)))
      (ℚRing.solve-∀ cx cy cz gx gy gz) squareSum)
    (subst
      (λ upper →
        (+ 3 / 1) * (sq (cx * gx) + sq (cy * gy) + sq (cz * gz)) ≤ upper)
      (ℚRing.solve-∀ Relaxed.fourRhoSquare (sq gx) (sq gy) (sq gz))
      scaledComponents)

shiftedSquareFibreSum13 : ∀ field axis transverse →
  sumRational (allCyclicIndices Side13.side13)
    (λ coordinate → sq (field
      (insertAxis axis (Flat.cyclicNext coordinate) transverse)))
  ≡ sumRational (allCyclicIndices Side13.side13)
    (λ coordinate → sq (field (insertAxis axis coordinate transverse)))
shiftedSquareFibreSum13 field axis transverse =
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

shiftedSquareGlobalSum13 : ∀ field axis →
  globalSiteSum (λ site → sq (field (Flat.shiftForward13 axis site)))
  ≡ globalSiteSum (λ site → sq (field site))
shiftedSquareGlobalSum13 field axis =
  trans
    (sym (axisPartitionSumMatchesGlobal axis
      (λ site → sq (field (Flat.shiftForward13 axis site)))))
    (trans
      (sumRationalCong
        (physicalTransverseCoordinates Side13.side13) _ _
        (λ transverse →
          trans
            (sumRationalCong
              (allCyclicIndices Side13.side13) _ _
              (λ coordinate → cong sq (cong field
                (shiftForwardInsertAxis13 axis coordinate transverse))))
            (shiftedSquareFibreSum13 field axis transverse)))
      (axisPartitionSumMatchesGlobal axis (λ site → sq (field site))))
  where
  shiftForwardInsertAxis13 :
    ∀ currentAxis coordinate transverse →
    Flat.shiftForward13 currentAxis (insertAxis currentAxis coordinate transverse)
    ≡ insertAxis currentAxis (Flat.cyclicNext coordinate) transverse
  shiftForwardInsertAxis13 zeroᵢ coordinate (pair x1 (pair x2 x3)) = refl
  shiftForwardInsertAxis13 (sucᵢ zeroᵢ) coordinate (pair x0 (pair x2 x3)) = refl
  shiftForwardInsertAxis13 (sucᵢ (sucᵢ zeroᵢ)) coordinate
      (pair x0 (pair x1 x3)) = refl
  shiftForwardInsertAxis13 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) coordinate
      (pair x0 (pair x1 x2)) = refl

multiplierCoordinateNormSq13 : Flat.GaugeMultiplier13 → Physical.LieCoordinate3 → ℚ
multiplierCoordinateNormSq13 multiplier coordinate =
  globalSiteSum (λ site → sq (multiplier (pair coordinate site)))

shiftedMultiplierThreeNormSum13 : ∀ multiplier axis →
  globalSiteSum
    (λ site →
      sq (multiplier (pair Physical.coordinateX (Flat.shiftForward13 axis site)))
      + sq (multiplier (pair Physical.coordinateY (Flat.shiftForward13 axis site)))
      + sq (multiplier (pair Physical.coordinateZ (Flat.shiftForward13 axis site))))
  ≡ FlatFloor.gaugeMultiplierNormSq13 multiplier
shiftedMultiplierThreeNormSum13 multiplier axis =
  trans
    (sumThreeExact
      (physicalBlockSites Side13.side13)
      (λ site → sq (multiplier (pair Physical.coordinateX (Flat.shiftForward13 axis site))))
      (λ site → sq (multiplier (pair Physical.coordinateY (Flat.shiftForward13 axis site))))
      (λ site → sq (multiplier (pair Physical.coordinateZ (Flat.shiftForward13 axis site)))))
    (trans
      (cong3
        (shiftedSquareGlobalSum13
          (λ site → multiplier (pair Physical.coordinateX site)) axis)
        (shiftedSquareGlobalSum13
          (λ site → multiplier (pair Physical.coordinateY site)) axis)
        (shiftedSquareGlobalSum13
          (λ site → multiplier (pair Physical.coordinateZ site)) axis))
      (sym (flatNormSplit multiplier)))
  where
  sumThreeExact : ∀ {A : Set} (values : Agda.Builtin.List.List A)
      (x y z : A → ℚ) →
    sumRational values (λ value → x value + y value + z value)
    ≡ sumRational values x + sumRational values y + sumRational values z
  sumThreeExact Agda.Builtin.List.[] x y z = ℚRing.solve []
  sumThreeExact (Agda.Builtin.List._∷_ value values) x y z
    rewrite sumThreeExact values x y z =
    ℚRing.solve-∀ (x value) (y value) (z value)
      (sumRational values x) (sumRational values y) (sumRational values z)
  cong3 : ∀ {a b c a' b' c' : ℚ} →
    a ≡ a' → b ≡ b' → c ≡ c' → a + b + c ≡ a' + b' + c'
  cong3 refl refl refl = refl
  flatNormSplit : ∀ currentMultiplier →
    FlatFloor.gaugeMultiplierNormSq13 currentMultiplier
    ≡ multiplierCoordinateNormSq13 currentMultiplier Physical.coordinateX
      + multiplierCoordinateNormSq13 currentMultiplier Physical.coordinateY
      + multiplierCoordinateNormSq13 currentMultiplier Physical.coordinateZ
  flatNormSplit currentMultiplier =
    trans
      (sumCartesian Physical.lieCoordinates3
        (physicalBlockSites Side13.side13)
        (λ row → sq (currentMultiplier row)))
      (ℚRing.solve-∀
        (multiplierCoordinateNormSq13 currentMultiplier Physical.coordinateX)
        (multiplierCoordinateNormSq13 currentMultiplier Physical.coordinateY)
        (multiplierCoordinateNormSq13 currentMultiplier Physical.coordinateZ))

gaugeAdjointDefectNormSq13 : RationalSU2Background13 → Flat.GaugeMultiplier13 → ℚ
gaugeAdjointDefectNormSq13 background multiplier =
  Physical.physicalSU2CoordinateNormSq (gaugeAdjointDefect13 background multiplier)

selectedAdjointDefectCoefficient13 : ℚ
selectedAdjointDefectCoefficient13 = + 9 / 1048576

selectedAdjointDefectCoefficient13Exact :
  (+ 144 / 1) * Relaxed.fourRhoSquare ≡ selectedAdjointDefectCoefficient13
selectedAdjointDefectCoefficient13Exact = ℚRing.solve []

selectedGaugeAdjointDefectBound13 :
  ∀ background → SelectedInverseLinkRadius13 background → ∀ multiplier →
  gaugeAdjointDefectNormSq13 background multiplier
  ≤ selectedAdjointDefectCoefficient13
      * FlatFloor.gaugeMultiplierNormSq13 multiplier
selectedGaugeAdjointDefectBound13 background radius multiplier =
  let
    siteThree site axis =
      sq (multiplier (pair Physical.coordinateX (Flat.shiftForward13 axis site)))
      + sq (multiplier (pair Physical.coordinateY (Flat.shiftForward13 axis site)))
      + sq (multiplier (pair Physical.coordinateZ (Flat.shiftForward13 axis site)))
    perOutput : ∀ inputCoordinate axis site →
      sq (gaugeAdjointDefect13 background multiplier
        (pair inputCoordinate (pair axis site)))
      ≤ (+ 12 / 1) * Relaxed.fourRhoSquare * siteThree site axis
    perOutput = outputStateDefectSquareBound13 background radius multiplier
    sumInputCoordinates : ∀ axis site →
      sumRational Physical.lieCoordinates3
        (λ inputCoordinate → sq (gaugeAdjointDefect13 background multiplier
          (pair inputCoordinate (pair axis site))))
      ≤ (+ 36 / 1) * Relaxed.fourRhoSquare * siteThree site axis
    sumInputCoordinates axis site =
      subst
        (λ upper →
          sumRational Physical.lieCoordinates3
            (λ inputCoordinate → sq (gaugeAdjointDefect13 background multiplier
              (pair inputCoordinate (pair axis site)))) ≤ upper)
        (ℚRing.solve-∀ Relaxed.fourRhoSquare (siteThree site axis))
        (Schur.sumPointwiseBelow Physical.lieCoordinates3 _ _
          (λ inputCoordinate → perOutput inputCoordinate axis site))
    summedAll =
      Schur.sumPointwiseBelow
        (Physical.physicalBondCells Side13.side13)
        (λ { (pair axis site) →
          sumRational Physical.lieCoordinates3
            (λ inputCoordinate → sq (gaugeAdjointDefect13 background multiplier
              (pair inputCoordinate (pair axis site)))) })
        (λ { (pair axis site) →
          (+ 36 / 1) * Relaxed.fourRhoSquare * siteThree site axis })
        (λ { (pair axis site) → sumInputCoordinates axis site })
    factorSites :
      sumRational (Physical.physicalBondCells Side13.side13)
        (λ { (pair axis site) →
          (+ 36 / 1) * Relaxed.fourRhoSquare * siteThree site axis })
      ≡ (+ 144 / 1) * Relaxed.fourRhoSquare
          * FlatFloor.gaugeMultiplierNormSq13 multiplier
    factorSites =
      trans
        (sumCartesian (allCyclicIndices four)
          (physicalBlockSites Side13.side13)
          (λ cell → (+ 36 / 1) * Relaxed.fourRhoSquare
            * siteThree (second cell) (first cell)))
        (trans
          (sumRationalCong (allCyclicIndices four) _ _
            (λ axis →
              trans
                (sumRationalScale ((+ 36 / 1) * Relaxed.fourRhoSquare)
                  (physicalBlockSites Side13.side13)
                  (λ site → siteThree site axis))
                (cong (((+ 36 / 1) * Relaxed.fourRhoSquare) *_)
                  (shiftedMultiplierThreeNormSum13 multiplier axis))))
          (ℚRing.solve-∀ Relaxed.fourRhoSquare
            (FlatFloor.gaugeMultiplierNormSq13 multiplier))))
  in
  subst
    (λ upper → gaugeAdjointDefectNormSq13 background multiplier ≤ upper)
    (trans factorSites
      (cong (_* FlatFloor.gaugeMultiplierNormSq13 multiplier)
        selectedAdjointDefectCoefficient13Exact))
    (subst
      (λ lower → lower
        ≤ sumRational (Physical.physicalBondCells Side13.side13)
            (λ { (pair axis site) →
              (+ 36 / 1) * Relaxed.fourRhoSquare * siteThree site axis }))
      (sumCartesian Physical.lieCoordinates3
        (Physical.physicalBondCells Side13.side13)
        (λ coordinate → sq (gaugeAdjointDefect13 background multiplier coordinate)))
      summedAll)

path13BackgroundGaugeAdjointDefectLevel : ProofLevel
path13BackgroundGaugeAdjointDefectLevel = machineChecked
path13SelectedGaugeAdjointDefectLevel : ProofLevel
path13SelectedGaugeAdjointDefectLevel = machineChecked
