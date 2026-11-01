module DASHI.Physics.YangMills.BalabanP33AugmentedYangMillsHessianStructureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jan Swoboda,
-- "Morse Homology for the Yang--Mills Gradient Flow",
-- Journal de Mathematiques Pures et Appliquees 98 (2012), 160--210.
-- DOI: 10.1016/j.matpur.2012.02.001.
--
-- Swoboda's continuum Hessian is
--
--   H_A = d_A^* d_A + *[*F_A wedge .]
--
-- and the gauge-fixed Fredholm analysis uses the corresponding augmented
-- gauge sector.  This is a structural precedent only: it does not supply the
-- lattice Wilson constants or the CMP109 block-constraint estimates.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact algebraic facts needed to treat
--
--   H_aug = H_Wilson + H_gauge + H_constraint
--
-- as one literal augmented Hessian:
--
--   * sums of symmetric bilinear forms are symmetric;
--   * the diagonal is the printed three-term sum;
--   * nonnegative gauge and constraint squares preserve every Wilson lower
--     bound;
--   * a signed Wilson remainder estimate combines with the two positive
--     sectors without changing its constant.
--
-- These are small but load-bearing facts: they prevent a continuum structural
-- citation from being mistaken for the missing physical lattice estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong₂; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

BilinearForm : Set → Set
BilinearForm Carrier = Carrier → Carrier → ℚ

Symmetric : ∀ {Carrier} → BilinearForm Carrier → Set
Symmetric form = ∀ left right → form left right ≡ form right left

addForm :
  ∀ {Carrier} →
  BilinearForm Carrier → BilinearForm Carrier → BilinearForm Carrier
addForm left right x y = left x y + right x y

augmentedHessian :
  ∀ {Carrier} →
  BilinearForm Carrier → BilinearForm Carrier → BilinearForm Carrier →
  BilinearForm Carrier
augmentedHessian wilson gauge constraint x y =
  wilson x y + (gauge x y + constraint x y)

addFormSymmetric :
  ∀ {Carrier}
    (left right : BilinearForm Carrier) →
  Symmetric left →
  Symmetric right →
  Symmetric (addForm left right)
addFormSymmetric left right leftSymmetric rightSymmetric x y =
  cong₂ _+_
    (leftSymmetric x y)
    (rightSymmetric x y)

augmentedHessianSymmetric :
  ∀ {Carrier}
    (wilson gauge constraint : BilinearForm Carrier) →
  Symmetric wilson →
  Symmetric gauge →
  Symmetric constraint →
  Symmetric (augmentedHessian wilson gauge constraint)
augmentedHessianSymmetric
    wilson gauge constraint
    wilsonSymmetric gaugeSymmetric constraintSymmetric
    x y =
  cong₂ _+_
    (wilsonSymmetric x y)
    (cong₂ _+_
      (gaugeSymmetric x y)
      (constraintSymmetric x y))

augmentedDiagonalExact :
  ∀ {Carrier}
    (wilson gauge constraint : BilinearForm Carrier)
    (field : Carrier) →
  augmentedHessian wilson gauge constraint field field
  ≡ wilson field field
    + (gauge field field + constraint field field)
augmentedDiagonalExact wilson gauge constraint field = refl

positiveSectorsPreserveLowerBound :
  ∀ wilsonValue gaugeValue constraintValue lower →
  lower ≤ wilsonValue →
  0ℚ ≤ gaugeValue →
  0ℚ ≤ constraintValue →
  lower ≤ wilsonValue + (gaugeValue + constraintValue)
positiveSectorsPreserveLowerBound
    wilsonValue gaugeValue constraintValue lower
    wilsonLower gaugeNonnegative constraintNonnegative =
  let
    instance
      gaugeNN : NonNegative gaugeValue
      gaugeNN = ℚ.nonNegative gaugeNonnegative
      constraintNN : NonNegative constraintValue
      constraintNN = ℚ.nonNegative constraintNonnegative

    wilsonToGauge : wilsonValue ≤ wilsonValue + gaugeValue
    wilsonToGauge = ℚP.p≤p+q wilsonValue gaugeValue

    addConstraint :
      wilsonValue + gaugeValue
      ≤ (wilsonValue + gaugeValue) + constraintValue
    addConstraint =
      ℚP.p≤p+q (wilsonValue + gaugeValue) constraintValue

    reassociate :
      (wilsonValue + gaugeValue) + constraintValue
      ≡ wilsonValue + (gaugeValue + constraintValue)
    reassociate = ℚRing.solve []

    gaugeToAugmented :
      wilsonValue + gaugeValue
      ≤ wilsonValue + (gaugeValue + constraintValue)
    gaugeToAugmented =
      subst
        (λ upper → wilsonValue + gaugeValue ≤ upper)
        reassociate
        addConstraint
  in
  ℚP.≤-trans
    wilsonLower
    (ℚP.≤-trans wilsonToGauge gaugeToAugmented)

augmentedCoercivityFromWilson :
  ∀ {Carrier}
    (wilson gauge constraint : BilinearForm Carrier)
    (coerciveFloor : ℚ) →
  (∀ field → coerciveFloor ≤ wilson field field) →
  (∀ field → 0ℚ ≤ gauge field field) →
  (∀ field → 0ℚ ≤ constraint field field) →
  ∀ field →
  coerciveFloor
  ≤ augmentedHessian wilson gauge constraint field field
augmentedCoercivityFromWilson
    wilson gauge constraint coerciveFloor
    wilsonLower gaugeNonnegative constraintNonnegative field =
  positiveSectorsPreserveLowerBound
    (wilson field field)
    (gauge field field)
    (constraint field field)
    coerciveFloor
    (wilsonLower field)
    (gaugeNonnegative field)
    (constraintNonnegative field)

signedWilsonRemainderWithPositiveSectors :
  ∀ reference remainder gaugeValue constraintValue lower →
  lower ≤ reference + remainder →
  0ℚ ≤ gaugeValue →
  0ℚ ≤ constraintValue →
  lower
  ≤ (reference + remainder) + (gaugeValue + constraintValue)
signedWilsonRemainderWithPositiveSectors
    reference remainder gaugeValue constraintValue lower
    wilsonLower gaugeNonnegative constraintNonnegative =
  positiveSectorsPreserveLowerBound
    (reference + remainder) gaugeValue constraintValue lower
    wilsonLower gaugeNonnegative constraintNonnegative

augmentedYangMillsHessianSymmetryLevel : ProofLevel
augmentedYangMillsHessianSymmetryLevel = machineChecked

augmentedYangMillsPositiveSectorLevel : ProofLevel
augmentedYangMillsPositiveSectorLevel = machineChecked

swobodaContinuumStructureOnlyLevel : ProofLevel
swobodaContinuumStructureOnlyLevel = standardImported
