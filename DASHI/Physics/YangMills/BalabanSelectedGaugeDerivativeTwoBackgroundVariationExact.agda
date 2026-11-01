module DASHI.Physics.YangMills.BalabanSelectedGaugeDerivativeTwoBackgroundVariationExact where

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
-- Close the gauge sector of the nonlinear Gate-I derivative-variation budget
-- between TWO selected backgrounds, rather than comparing only with the flat
-- reference.  For the literal physical covariant-gauge derivative,
--
--   V_{U,A}(h) = D F_U[h] - D F_A[h],
--
-- the exact flat-plus-defect identity makes V_{U,A} the difference of the two
-- already-controlled background defects.  The scalar identity
--
--   (x-y)^2 <= 2 x^2 + 2 y^2
--
-- is proved from (x+y)^2 >= 0 and then summed over the three Lie coordinates
-- and all 4^4 sites.  If both backgrounds satisfy the repository's selected
-- relaxed link radius delta = 4 rho^2, rho = 1/8192, then
--
--   ||D F_U-D F_A||^2 <= (1/262144) ||h||^2.
--
-- This is far below the full nonlinear IFT target 29/2048.  Consequently the
-- nonlinear block-average derivative may consume the exact remaining squared
-- budget 3711/262144.  No completeness, square root, singular-value theorem,
-- or abstract operator norm is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact as Pointwise
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as Global
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact as Signed
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

------------------------------------------------------------------------
-- Literal two-background gauge derivative difference.
------------------------------------------------------------------------

gaugeDerivativeTwoBackgroundCoordinate :
  Physical.RationalSU2Background4 →
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Coordinates.LieCoordinate3 → Periodic.Site4 → ℚ
gaugeDerivativeTwoBackgroundCoordinate left right bondField coordinate site =
  Gauge.backgroundGaugeFirst left bondField (pair coordinate site)
  - Gauge.backgroundGaugeFirst right bondField (pair coordinate site)

gaugeDerivativeTwoBackgroundIsDefectDifference :
  ∀ left right bondField coordinate site →
  gaugeDerivativeTwoBackgroundCoordinate left right bondField coordinate site
  ≡ Pointwise.backgroundGaugeDefectCoordinate left bondField coordinate site
    - Pointwise.backgroundGaugeDefectCoordinate right bondField coordinate site
gaugeDerivativeTwoBackgroundIsDefectDifference
    left right bondField coordinate site =
  let
    leftExact = Signed.backgroundFirstIsFlatPlusDefect
      left bondField coordinate site
    rightExact = Signed.backgroundFirstIsFlatPlusDefect
      right bondField coordinate site
    flat = Gauge.flatGaugeFirstFromAxes bondField (pair coordinate site)
    leftDefect = Pointwise.backgroundGaugeDefectCoordinate
      left bondField coordinate site
    rightDefect = Pointwise.backgroundGaugeDefectCoordinate
      right bondField coordinate site
  in
  trans
    (cong₂ _-_ leftExact rightExact)
    (ℚRing.solve-∀ flat leftDefect rightDefect)

squareDifferenceBelowTwoSquares : ∀ left right →
  (left - right) * (left - right)
  ≤ (+ 2 / 1) * (left * left) + (+ 2 / 1) * (right * right)
squareDifferenceBelowTwoSquares left right =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ left right)
      (FiniteL2.squareNonnegative (left + right)))

pointwiseTwoBackgroundVariationEnergy :
  Physical.RationalSU2Background4 →
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Periodic.Site4 → ℚ
pointwiseTwoBackgroundVariationEnergy left right bondField site =
  let
    dx = gaugeDerivativeTwoBackgroundCoordinate
      left right bondField Coordinates.coordinateX site
    dy = gaugeDerivativeTwoBackgroundCoordinate
      left right bondField Coordinates.coordinateY site
    dz = gaugeDerivativeTwoBackgroundCoordinate
      left right bondField Coordinates.coordinateZ site
  in
  dx * dx + dy * dy + dz * dz

pointwiseTwoBackgroundVariationUpper :
  ∀ left right bondField site →
  pointwiseTwoBackgroundVariationEnergy left right bondField site
  ≤ (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy left bondField site
    + (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy right bondField site
pointwiseTwoBackgroundVariationUpper left right bondField site =
  let
    lx = Pointwise.backgroundGaugeDefectCoordinate
      left bondField Coordinates.coordinateX site
    ly = Pointwise.backgroundGaugeDefectCoordinate
      left bondField Coordinates.coordinateY site
    lz = Pointwise.backgroundGaugeDefectCoordinate
      left bondField Coordinates.coordinateZ site
    rx = Pointwise.backgroundGaugeDefectCoordinate
      right bondField Coordinates.coordinateX site
    ry = Pointwise.backgroundGaugeDefectCoordinate
      right bondField Coordinates.coordinateY site
    rz = Pointwise.backgroundGaugeDefectCoordinate
      right bondField Coordinates.coordinateZ site

    bx = squareDifferenceBelowTwoSquares lx rx
    by = squareDifferenceBelowTwoSquares ly ry
    bz = squareDifferenceBelowTwoSquares lz rz
    combined = ℚP.+-mono-≤ bx (ℚP.+-mono-≤ by bz)
  in
  subst
    (λ lower →
      lower
      ≤ (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy left bondField site
        + (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy right bondField site)
    (sym
      (trans
        (cong₂ _+_
          (cong₂ _*_
            (gaugeDerivativeTwoBackgroundIsDefectDifference
              left right bondField Coordinates.coordinateX site)
            (gaugeDerivativeTwoBackgroundIsDefectDifference
              left right bondField Coordinates.coordinateX site))
          (cong₂ _+_
            (cong₂ _*_
              (gaugeDerivativeTwoBackgroundIsDefectDifference
                left right bondField Coordinates.coordinateY site)
              (gaugeDerivativeTwoBackgroundIsDefectDifference
                left right bondField Coordinates.coordinateY site))
            (cong₂ _*_
              (gaugeDerivativeTwoBackgroundIsDefectDifference
                left right bondField Coordinates.coordinateZ site)
              (gaugeDerivativeTwoBackgroundIsDefectDifference
                left right bondField Coordinates.coordinateZ site))))
        (ℚRing.solve-∀ lx ly lz rx ry rz)))
    (subst
      (λ upper →
        (lx - rx) * (lx - rx)
          + ((ly - ry) * (ly - ry) + (lz - rz) * (lz - rz))
        ≤ upper)
      (ℚRing.solve-∀ lx ly lz rx ry rz)
      combined)

------------------------------------------------------------------------
-- Global exact selected-radius coefficient.
------------------------------------------------------------------------

gaugeDerivativeTwoBackgroundVariationEnergy :
  Physical.RationalSU2Background4 →
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → ℚ
gaugeDerivativeTwoBackgroundVariationEnergy left right bondField =
  Periodic.sumSites (pointwiseTwoBackgroundVariationEnergy left right bondField)

gaugeDerivativeTwoBackgroundVariationBelowDefects :
  ∀ left right bondField →
  gaugeDerivativeTwoBackgroundVariationEnergy left right bondField
  ≤ (+ 2 / 1) * Global.globalGaugeDerivativeDefectEnergy left bondField
    + (+ 2 / 1) * Global.globalGaugeDerivativeDefectEnergy right bondField
gaugeDerivativeTwoBackgroundVariationBelowDefects left right bondField =
  let
    raw = Global.sumSitesMonotone _ _
      (pointwiseTwoBackgroundVariationUpper left right bondField)

    summed :
      Periodic.sumSites
        (λ site →
          (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy left bondField site
          + (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy right bondField site)
      ≡ (+ 2 / 1) * Global.globalGaugeDerivativeDefectEnergy left bondField
        + (+ 2 / 1) * Global.globalGaugeDerivativeDefectEnergy right bondField
    summed =
      trans
        (Periodic.sumSitesAdd
          (λ site → (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy left bondField site)
          (λ site → (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy right bondField site))
        (cong₂ _+_
          (Periodic.sumSitesScale (+ 2 / 1)
            (Pointwise.pointwiseGaugeDefectEnergy left bondField))
          (Periodic.sumSitesScale (+ 2 / 1)
            (Pointwise.pointwiseGaugeDefectEnergy right bondField)))
  in
  subst
    (λ upper →
      gaugeDerivativeTwoBackgroundVariationEnergy left right bondField ≤ upper)
    summed raw

gaugeDerivativeTwoBackgroundSquaredCoefficient : ℚ
gaugeDerivativeTwoBackgroundSquaredCoefficient = + 1 / 262144

blockAverageDerivativeRemainingSquaredBudget : ℚ
blockAverageDerivativeRemainingSquaredBudget = + 3711 / 262144

fullDerivativeVariationSquaredBudget : ℚ
fullDerivativeVariationSquaredBudget = + 29 / 2048

gaugePlusBlockBudgetExact :
  gaugeDerivativeTwoBackgroundSquaredCoefficient
    + blockAverageDerivativeRemainingSquaredBudget
  ≡ fullDerivativeVariationSquaredBudget
gaugePlusBlockBudgetExact = ℚRing.solve []

selectedGaugeDerivativeTwoBackgroundVariationUpper :
  ∀ left right bondField →
  Relaxed.RelaxedInverseLinkRadius left →
  Relaxed.RelaxedInverseLinkRadius right →
  gaugeDerivativeTwoBackgroundVariationEnergy left right bondField
  ≤ gaugeDerivativeTwoBackgroundSquaredCoefficient
      * Coordinates.physicalSU2BondNormSq bondField
selectedGaugeDerivativeTwoBackgroundVariationUpper
    left right bondField leftRadius rightRadius =
  let
    norm = Coordinates.physicalSU2BondNormSq bondField
    leftDefect = Global.globalGaugeDerivativeDefectUniformBound
      left bondField Relaxed.fourRhoSquare
      (ℚP.nonNegative⁻¹ Relaxed.fourRhoSquare) leftRadius
    rightDefect = Global.globalGaugeDerivativeDefectUniformBound
      right bondField Relaxed.fourRhoSquare
      (ℚP.nonNegative⁻¹ Relaxed.fourRhoSquare) rightRadius

    scaledLeft = Norm.scaleNonnegative (+ 2 / 1)
      (ℚP.nonNegative⁻¹ (+ 2 / 1)) leftDefect
    scaledRight = Norm.scaleNonnegative (+ 2 / 1)
      (ℚP.nonNegative⁻¹ (+ 2 / 1)) rightDefect

    defectSumUpper = ℚP.+-mono-≤ scaledLeft scaledRight
    first = gaugeDerivativeTwoBackgroundVariationBelowDefects
      left right bondField
    combined = ℚP.≤-trans first defectSumUpper

    coefficientExact :
      (+ 2 / 1) * ((+ 16 / 1) * Relaxed.fourRhoSquare * norm)
      + (+ 2 / 1) * ((+ 16 / 1) * Relaxed.fourRhoSquare * norm)
      ≡ gaugeDerivativeTwoBackgroundSquaredCoefficient * norm
    coefficientExact = ℚRing.solve-∀ norm
  in
  subst
    (λ upper →
      gaugeDerivativeTwoBackgroundVariationEnergy left right bondField ≤ upper)
    coefficientExact combined

selectedGaugeDerivativeTwoBackgroundSameObjectLevel : ProofLevel
selectedGaugeDerivativeTwoBackgroundSameObjectLevel = machineChecked

selectedGaugeDerivativeTwoBackgroundVariationLevel : ProofLevel
selectedGaugeDerivativeTwoBackgroundVariationLevel = machineChecked

selectedBlockAverageDerivativeRemainingBudgetLevel : ProofLevel
selectedBlockAverageDerivativeRemainingBudgetLevel = machineChecked
