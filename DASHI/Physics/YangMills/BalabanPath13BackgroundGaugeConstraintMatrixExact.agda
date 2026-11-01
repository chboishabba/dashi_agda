module DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeConstraintMatrixExact where

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
-- Construct the literal L=13 covariant backward-divergence derivative matrix
-- on the same 342732 state carrier as the Path13 coercivity theorem.  For row
-- (b,y) and column (a,mu,x), the physical entry is
--
--   delta_ab delta_xy
--     - [Ad_{U_mu(x)^-1}]_{b a} delta_{x+mu,y}.
--
-- Its flat part is the exact incidence matrix already used by the Path13
-- Poincare proof; its remainder is the local adjoint-rotation defect.  Finite
-- delta selection then proves that the matrix transpose is exactly
--
--   L_g,0^* gamma + D_A^* gamma.
--
-- Thus the selected source-scale gauge floor is attached to one explicit
-- physical derivative matrix rather than to an independently invented defect
-- vector.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)
open import Relation.Nullary using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
open import DASHI.Physics.YangMills.BalabanFiniteEnumerationDistinctExact
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalSU2RationalMatrixCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointMatrixExact as Flat
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

siteDecidableEquality13 : DecidableEquality (PhysicalBlockL Side13.side13)
siteDecidableEquality13 = periodicTorus4DecidableEquality Side13.side13

siteDelta13 :
  PhysicalBlockL Side13.side13 → PhysicalBlockL Side13.side13 → ℚ
siteDelta13 = Coordinates.kroneckerDelta siteDecidableEquality13

lieDelta13 : Physical.LieCoordinate3 → Physical.LieCoordinate3 → ℚ
lieDelta13 = Coordinates.kroneckerDelta Coordinates.lieCoordinateDecidableEquality

siteSelectorExact13 : ∀ target field →
  sumRational (physicalBlockSites Side13.side13)
    (λ site → siteDelta13 target site * field site)
  ≡ field target
siteSelectorExact13 target field =
  Coordinates.deltaSumIdentity
    siteDecidableEquality13
    (Coordinates.siteElementsDuplicateFree Side13.side13)
    target
    (complete (periodicTorus4Finite Side13.side13) target)
    field

gaugeRowDeltaProduct13 :
  ∀ input output site rowSite →
  Flat.gaugeRowDelta13 (pair input site) (pair output rowSite)
  ≡ lieDelta13 input output * siteDelta13 site rowSite
gaugeRowDeltaProduct13 Physical.coordinateX Physical.coordinateX site rowSite
  with siteDecidableEquality13 site rowSite
... | yes _ = refl
... | no _ = refl
gaugeRowDeltaProduct13 Physical.coordinateX Physical.coordinateY site rowSite = refl
gaugeRowDeltaProduct13 Physical.coordinateX Physical.coordinateZ site rowSite = refl
gaugeRowDeltaProduct13 Physical.coordinateY Physical.coordinateX site rowSite = refl
gaugeRowDeltaProduct13 Physical.coordinateY Physical.coordinateY site rowSite
  with siteDecidableEquality13 site rowSite
... | yes _ = refl
... | no _ = refl
gaugeRowDeltaProduct13 Physical.coordinateY Physical.coordinateZ site rowSite = refl
gaugeRowDeltaProduct13 Physical.coordinateZ Physical.coordinateX site rowSite = refl
gaugeRowDeltaProduct13 Physical.coordinateZ Physical.coordinateY site rowSite = refl
gaugeRowDeltaProduct13 Physical.coordinateZ Physical.coordinateZ site rowSite
  with siteDecidableEquality13 site rowSite
... | yes _ = refl
... | no _ = refl

flatEntryAsPhysicalIncidence13 :
  ∀ output rowSite input axis site →
  Flat.flatGaugeConstraintMatrix13
    (pair output rowSite) (pair input (pair axis site))
  ≡ lieDelta13 input output * siteDelta13 site rowSite
    - lieDelta13 input output
      * siteDelta13 (Flat.shiftForward13 axis site) rowSite
flatEntryAsPhysicalIncidence13 output rowSite input axis site =
  cong₂ _-_
    (gaugeRowDeltaProduct13 input output site rowSite)
    (gaugeRowDeltaProduct13 input output
      (Flat.shiftForward13 axis site) rowSite)

transportCoefficient13 :
  Background.RationalSU2Background13 →
  Physical.LieCoordinate3 → Physical.LieCoordinate3 →
  Axis4 → PhysicalBlockL Side13.side13 → ℚ
transportCoefficient13 background output input axis site =
  Background.quaternionCoordinate output
    (Adjoint.adjointTransport
      (Background.inverseLink13 background axis site)
      (Background.basisQuaternion input))

basisCoordinateDelta13 : ∀ output input →
  Background.quaternionCoordinate output (Background.basisQuaternion input)
  ≡ lieDelta13 input output
basisCoordinateDelta13 Physical.coordinateX Physical.coordinateX = refl
basisCoordinateDelta13 Physical.coordinateX Physical.coordinateY = refl
basisCoordinateDelta13 Physical.coordinateX Physical.coordinateZ = refl
basisCoordinateDelta13 Physical.coordinateY Physical.coordinateX = refl
basisCoordinateDelta13 Physical.coordinateY Physical.coordinateY = refl
basisCoordinateDelta13 Physical.coordinateY Physical.coordinateZ = refl
basisCoordinateDelta13 Physical.coordinateZ Physical.coordinateX = refl
basisCoordinateDelta13 Physical.coordinateZ Physical.coordinateY = refl
basisCoordinateDelta13 Physical.coordinateZ Physical.coordinateZ = refl

transportMinusIdentityIsDefect13 :
  ∀ background output input axis site →
  transportCoefficient13 background output input axis site
    - lieDelta13 input output
  ≡ Background.adjointDefectCoordinate13
      background output input axis site
transportMinusIdentityIsDefect13 background output input axis site =
  trans
    (cong
      (λ basisCoordinate →
        transportCoefficient13 background output input axis site
        - basisCoordinate)
      (symmetry (basisCoordinateDelta13 output input)))
    (coordinateDifference output
      (Background.inverseLink13 background axis site)
      (Background.basisQuaternion input))
  where
  symmetry : ∀ {A : Set} {left right : A} → left ≡ right → right ≡ left
  symmetry refl = refl

  coordinateDifference : ∀ coordinate unit basis →
    Background.quaternionCoordinate coordinate
      (Adjoint.adjointTransport unit basis)
      - Background.quaternionCoordinate coordinate basis
    ≡ Background.quaternionCoordinate coordinate
      (Adjoint.adjointDefect unit basis)
  coordinateDifference Physical.coordinateX
      (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3) =
    ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3
  coordinateDifference Physical.coordinateY
      (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3) =
    ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3
  coordinateDifference Physical.coordinateZ
      (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3) =
    ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3

defectMatrixEntry13 :
  Background.RationalSU2Background13 → Flat.GaugeRow13 → Flat.State13 → ℚ
defectMatrixEntry13 background
    (pair output rowSite) (pair input (pair axis site)) =
  - Background.adjointDefectCoordinate13 background output input axis site
    * siteDelta13 (Flat.shiftForward13 axis site) rowSite

backgroundGaugeConstraintMatrix13 :
  Background.RationalSU2Background13 → Flat.GaugeRow13 → Flat.State13 → ℚ
backgroundGaugeConstraintMatrix13 background row column =
  Flat.flatGaugeConstraintMatrix13 row column
  + defectMatrixEntry13 background row column

backgroundGaugeMatrixPhysicalEntry13 :
  ∀ background output rowSite input axis site →
  backgroundGaugeConstraintMatrix13 background
    (pair output rowSite) (pair input (pair axis site))
  ≡ lieDelta13 input output * siteDelta13 site rowSite
    - transportCoefficient13 background output input axis site
      * siteDelta13 (Flat.shiftForward13 axis site) rowSite
backgroundGaugeMatrixPhysicalEntry13 background output rowSite input axis site =
  trans
    (cong
      (_+ defectMatrixEntry13 background
        (pair output rowSite) (pair input (pair axis site)))
      (flatEntryAsPhysicalIncidence13 output rowSite input axis site))
    (subst
      (λ difference →
        (lieDelta13 input output * siteDelta13 site rowSite
          - lieDelta13 input output
            * siteDelta13 (Flat.shiftForward13 axis site) rowSite)
        + (- Background.adjointDefectCoordinate13 background output input axis site
            * siteDelta13 (Flat.shiftForward13 axis site) rowSite)
        ≡ lieDelta13 input output * siteDelta13 site rowSite
          - (lieDelta13 input output + difference)
            * siteDelta13 (Flat.shiftForward13 axis site) rowSite)
      (symmetry (transportMinusIdentityIsDefect13
        background output input axis site))
      (ℚRing.solve-∀
        (lieDelta13 input output)
        (siteDelta13 site rowSite)
        (siteDelta13 (Flat.shiftForward13 axis site) rowSite)
        (Background.adjointDefectCoordinate13 background output input axis site)))
  where
  symmetry : ∀ {A : Set} {left right : A} → left ≡ right → right ≡ left
  symmetry refl = refl

defectAdjointApply13 :
  Background.RationalSU2Background13 → Flat.GaugeMultiplier13 → Flat.StateVector13
defectAdjointApply13 background multiplier column =
  sumRational Flat.gaugeRows13
    (λ row → defectMatrixEntry13 background row column * multiplier row)

siteSelectedDefectSum13 :
  ∀ background multiplier input axis site →
  defectAdjointApply13 background multiplier
    (pair input (pair axis site))
  ≡ Background.gaugeAdjointDefect13 background multiplier
      (pair input (pair axis site))
siteSelectedDefectSum13 background multiplier input axis site =
  trans
    (sumCartesian
      Physical.lieCoordinates3
      (physicalBlockSites Side13.side13)
      (λ { (pair output rowSite) →
        defectMatrixEntry13 background (pair output rowSite)
          (pair input (pair axis site))
        * multiplier (pair output rowSite) }))
    (trans
      (sumRationalCong Physical.lieCoordinates3 _ _
        (λ output →
          trans
            (sumRationalCong
              (physicalBlockSites Side13.side13) _ _
              (λ rowSite →
                ℚRing.solve-∀
                  (Background.adjointDefectCoordinate13
                    background output input axis site)
                  (siteDelta13 (Flat.shiftForward13 axis site) rowSite)
                  (multiplier (pair output rowSite))))
            (trans
              (cong
                (λ selected →
                  - Background.adjointDefectCoordinate13
                      background output input axis site * selected)
                (siteSelectorExact13
                  (Flat.shiftForward13 axis site)
                  (λ rowSite → multiplier (pair output rowSite))))
              refl)))
      (threeCoordinateDefectExact background multiplier input axis site)))
  where
  threeCoordinateDefectExact :
    ∀ currentBackground currentMultiplier currentInput currentAxis currentSite →
    sumRational Physical.lieCoordinates3
      (λ output →
        - Background.adjointDefectCoordinate13 currentBackground
            output currentInput currentAxis currentSite
          * currentMultiplier
            (pair output (Flat.shiftForward13 currentAxis currentSite)))
    ≡ Background.gaugeAdjointDefect13 currentBackground currentMultiplier
      (pair currentInput (pair currentAxis currentSite))
  threeCoordinateDefectExact currentBackground currentMultiplier currentInput currentAxis currentSite =
    ℚRing.solve-∀
      (Background.adjointDefectCoordinate13 currentBackground Physical.coordinateX
        currentInput currentAxis currentSite)
      (Background.adjointDefectCoordinate13 currentBackground Physical.coordinateY
        currentInput currentAxis currentSite)
      (Background.adjointDefectCoordinate13 currentBackground Physical.coordinateZ
        currentInput currentAxis currentSite)
      (currentMultiplier
        (pair Physical.coordinateX (Flat.shiftForward13 currentAxis currentSite)))
      (currentMultiplier
        (pair Physical.coordinateY (Flat.shiftForward13 currentAxis currentSite)))
      (currentMultiplier
        (pair Physical.coordinateZ (Flat.shiftForward13 currentAxis currentSite)))

backgroundGaugeAdjointApply13 :
  Background.RationalSU2Background13 → Flat.GaugeMultiplier13 → Flat.StateVector13
backgroundGaugeAdjointApply13 background multiplier column =
  sumRational Flat.gaugeRows13
    (λ row → backgroundGaugeConstraintMatrix13 background row column * multiplier row)

backgroundGaugeAdjointSameObject13 :
  ∀ background multiplier column →
  backgroundGaugeAdjointApply13 background multiplier column
  ≡ Flat.flatGaugeAdjoint13 multiplier column
    + Background.gaugeAdjointDefect13 background multiplier column
backgroundGaugeAdjointSameObject13 background multiplier
    (pair input (pair axis site)) =
  trans
    (sumRationalCong Flat.gaugeRows13 _ _
      (λ row → ℚRing.solve-∀
        (Flat.flatGaugeConstraintMatrix13 row (pair input (pair axis site)))
        (defectMatrixEntry13 background row (pair input (pair axis site)))
        (multiplier row)))
    (trans
      (sumRationalAdd Flat.gaugeRows13
        (λ row →
          Flat.flatGaugeConstraintMatrix13 row (pair input (pair axis site))
          * multiplier row)
        (λ row →
          defectMatrixEntry13 background row (pair input (pair axis site))
          * multiplier row))
      (cong₂ _+_ refl
        (siteSelectedDefectSum13 background multiplier input axis site)))

path13BackgroundGaugeConstraintMatrixLevel : ProofLevel
path13BackgroundGaugeConstraintMatrixLevel = machineChecked

path13BackgroundGaugePhysicalEntryLevel : ProofLevel
path13BackgroundGaugePhysicalEntryLevel = machineChecked

path13BackgroundGaugeAdjointSameObjectLevel : ProofLevel
path13BackgroundGaugeAdjointSameObjectLevel = machineChecked
