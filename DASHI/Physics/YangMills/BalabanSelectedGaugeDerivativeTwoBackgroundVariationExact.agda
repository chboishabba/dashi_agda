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
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; trans)

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
gaugeDerivativeTwoBackgroundCoordinate left right field coordinate site =
  Gauge.backgroundGaugeFirst left field (pair coordinate site)
  - Gauge.backgroundGaugeFirst right field (pair coordinate site)

gaugeDerivativeTwoBackgroundIsDefectDifference :
  ∀ left right field coordinate site →
  gaugeDerivativeTwoBackgroundCoordinate left right field coordinate site
  ≡ Pointwise.backgroundGaugeDefectCoordinate left field coordinate site
    - Pointwise.backgroundGaugeDefectCoordinate right field coordinate site
gaugeDerivativeTwoBackgroundIsDefectDifference
    left right field coordinate site =
  let
    leftExact = Signed.backgroundFirstIsFlatPlusDefect
      left field coordinate site
    rightExact = Signed.backgroundFirstIsFlatPlusDefect
      right field coordinate site
    flat = Gauge.flatGaugeFirstFromAxes field (pair coordinate site)
    leftDefect = Pointwise.backgroundGaugeDefectCoordinate
      left field coordinate site
    rightDefect = Pointwise.backgroundGaugeDefectCoordinate
      right field coordinate site
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
pointwiseTwoBackgroundVariationEnergy left right field site =
  let
    dx = gaugeDerivativeTwoBackgroundCoordinate
      left right field Coordinates.coordinateX site
    dy = gaugeDerivativeTwoBackgroundCoordinate
      left right field Coordinates.coordinateY site
    dz = gaugeDerivativeTwoBackgroundCoordinate
      left right field Coordinates.coordinateZ site
  in
  dx * dx + dy * dy + dz * dz

pointwiseTwoBackgroundVariationUpper :
  ∀ left right field site →
  pointwiseTwoBackgroundVariationEnergy left right field site
  ≤ (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy left field site
    + (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy right field site
pointwiseTwoBackgroundVariationUpper left right field site =
  let
    lx = Pointwise.backgroundGaugeDefectCoordinate
      left field Coordinates.coordinateX site
    ly = Pointwise.backgroundGaugeDefectCoordinate
      left field Coordinates.coordinateY site
    lz = Pointwise.backgroundGaugeDefectCoordinate
      left field Coordinates.coordinateZ site
    rx = Pointwise.backgroundGaugeDefectCoordinate
      right field Coordinates.coordinateX site
    ry = Pointwise.backgroundGaugeDefectCoordinate
      right field Coordinates.coordinateY site
    rz = Pointwise.backgroundGaugeDefectCoordinate
      right field Coordinates.coordinateZ site

    bx = squareDifferenceBelowTwoSquares lx rx
    by = squareDifferenceBelowTwoSquares ly ry
    bz = squareDifferenceBelowTwoSquares lz rz
    combined = ℚP.+-mono-≤ bx (ℚP.+-mono-≤ by bz)
  in
  subst
    (λ lower →
      lower
      ≤ (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy left field site
        + (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy right field site)
    (sym
      (trans
        (cong₂ _+_
          (cong₂ _*_
            (gaugeDerivativeTwoBackgroundIsDefectDifference
              left right field Coordinates.coordinateX site)
            (gaugeDerivativeTwoBackgroundIsDefectDifference
              left right field Coordinates.coordinateX site))
          (cong₂ _+_
            (cong₂ _*_
              (gaugeDerivativeTwoBackgroundIsDefectDifference
                left right field Coordinates.coordinateY site)
              (gaugeDerivativeTwoBackgroundIsDefectDifference
                left right field Coordinates.coordinateY site))
            (cong₂ _*_
              (gaugeDerivativeTwoBackgroundIsDefectDifference
                left right field Coordinates.coordinateZ site)
              (gaugeDerivativeTwoBackgroundIsDefectDifference
                left right field Coordinates.coordinateZ site))))
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
gaugeDerivativeTwoBackgroundVariationEnergy left right field =
  Periodic.sumSites (pointwiseTwoBackgroundVariationEnergy left right field)

gaugeDerivativeTwoBackgroundVariationBelowDefects :
  ∀ left right field →
  gaugeDerivativeTwoBackgroundVariationEnergy left right field
  ≤ (+ 2 / 1) * Global.globalGaugeDerivativeDefectEnergy left field
    + (+ 2 / 1) * Global.globalGaugeDerivativeDefectEnergy right field
gaugeDerivativeTwoBackgroundVariationBelowDefects left right field =
  let
    raw = Global.sumSitesMonotone _ _
      (pointwiseTwoBackgroundVariationUpper left right field)

    summed :
      Periodic.sumSites
        (λ site →
          (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy left field site
          + (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy right field site)
      ≡ (+ 2 / 1) * Global.globalGaugeDerivativeDefectEnergy left field
        + (+ 2 / 1) * Global.globalGaugeDerivativeDefectEnergy right field
    summed =
      trans
        (Periodic.sumSitesAdd
          (λ site → (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy left field site)
          (λ site → (+ 2 / 1) * Pointwise.pointwiseGaugeDefectEnergy right field site))
        (cong₂ _+_
          (Periodic.sumSitesScale (+ 2 / 1)
            (Pointwise.pointwiseGaugeDefectEnergy left field))
          (Periodic.sumSitesScale (+ 2 / 1)
            (Pointwise.pointwiseGaugeDefectEnergy right field)))
  in
  subst
    (λ upper →
      gaugeDerivativeTwoBackgroundVariationEnergy left right field ≤ upper)
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
  ∀ left right field →
  Relaxed.RelaxedInverseLinkRadius left →
  Relaxed.RelaxedInverseLinkRadius right →
  gaugeDerivativeTwoBackgroundVariationEnergy left right field
  ≤ gaugeDerivativeTwoBackgroundSquaredCoefficient
      * Coordinates.physicalSU2BondNormSq field
selectedGaugeDerivativeTwoBackgroundVariationUpper
    left right field leftRadius rightRadius =
  let
    norm = Coordinates.physicalSU2BondNormSq field
    leftDefect = Global.globalGaugeDerivativeDefectUniformBound
      left field Relaxed.fourRhoSquare
      (ℚP.nonNegative⁻¹ Relaxed.fourRhoSquare) leftRadius
    rightDefect = Global.globalGaugeDerivativeDefectUniformBound
      right field Relaxed.fourRhoSquare
      (ℚP.nonNegative⁻¹ Relaxed.fourRhoSquare) rightRadius

    scaledLeft = Norm.scaleNonnegative (+ 2 / 1)
      (ℚP.nonNegative⁻¹ (+ 2 / 1)) leftDefect
    scaledRight = Norm.scaleNonnegative (+ 2 / 1)
      (ℚP.nonNegative⁻¹ (+ 2 / 1)) rightDefect

    defectSumUpper = ℚP.+-mono-≤ scaledLeft scaledRight
    first = gaugeDerivativeTwoBackgroundVariationBelowDefects
      left right field
    combined = ℚP.≤-trans first defectSumUpper

    coefficientExact :
      (+ 2 / 1) * ((+ 16 / 1) * Relaxed.fourRhoSquare * norm)
      + (+ 2 / 1) * ((+ 16 / 1) * Relaxed.fourRhoSquare * norm)
      ≡ gaugeDerivativeTwoBackgroundSquaredCoefficient * norm
    coefficientExact = ℚRing.solve-∀ norm
  in
  subst
    (λ upper →
      gaugeDerivativeTwoBackgroundVariationEnergy left right field ≤ upper)
    coefficientExact combined

selectedGaugeDerivativeTwoBackgroundSameObjectLevel : ProofLevel
selectedGaugeDerivativeTwoBackgroundSameObjectLevel = machineChecked

selectedGaugeDerivativeTwoBackgroundVariationLevel : ProofLevel
selectedGaugeDerivativeTwoBackgroundVariationLevel = machineChecked

selectedBlockAverageDerivativeRemainingBudgetLevel : ProofLevel
selectedBlockAverageDerivativeRemainingBudgetLevel = machineChecked
