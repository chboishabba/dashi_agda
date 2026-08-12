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
-- Supply the missing same-object matrix theorem for the L=13 background gauge
-- derivative.  On a column (a,mu,x), the covariant backward-divergence row at
-- y receives the current incidence term at y=x and the transported predecessor
-- term at y=x+mu.  Thus the literal matrix entry is
--
--   delta_(a,x),(b,y)
--     - [Ad_{U_mu(x)^-1}]_{b a} delta_(x+mu),y.
--
-- At the identity background this is exactly the source-scale flat incidence
-- matrix.  Its transpose on a multiplier gamma is exactly
--
--   L_g,0^* gamma + D_A^* gamma,
--
-- where D_A^* is the local adjoint defect proved and bounded in
-- BalabanPath13BackgroundGaugeAdjointDefectExact.  Hence the selected L=13
-- floor is attached to the derivative of one explicit matrix, not merely to an
-- independently bounded vector formula.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

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

siteDecidableEquality13 : DecidableEquality (PhysicalBlockL Side13.side13)
siteDecidableEquality13 = periodicTorus4DecidableEquality Side13.side13

siteDelta13 :
  PhysicalBlockL Side13.side13 → PhysicalBlockL Side13.side13 → ℚ
siteDelta13 = Coordinates.kroneckerDelta siteDecidableEquality13

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

lieDelta13 : Physical.LieCoordinate3 → Physical.LieCoordinate3 → ℚ
lieDelta13 =
  Coordinates.kroneckerDelta Coordinates.lieCoordinateDecidableEquality

transportCoefficient13 :
  Background.RationalSU2Background13 →
  Physical.LieCoordinate3 → Physical.LieCoordinate3 →
  Axis4 → PhysicalBlockL Side13.side13 → ℚ
transportCoefficient13 background outputCoordinate inputCoordinate axis site =
  Background.quaternionCoordinate outputCoordinate
    (Adjoint.adjointTransport
      (Background.inverseLink13 background axis site)
      (Background.basisQuaternion inputCoordinate))

identityTransportCoefficient13 :
  ∀ outputCoordinate inputCoordinate →
  Background.quaternionCoordinate outputCoordinate
    (Adjoint.adjointTransport
      BackgroundIdentityUnit (Background.basisQuaternion inputCoordinate))
  ≡ lieDelta13 inputCoordinate outputCoordinate
identityTransportCoefficient13 Physical.coordinateX Physical.coordinateX =
  ℚRing.solve []
identityTransportCoefficient13 Physical.coordinateX Physical.coordinateY =
  ℚRing.solve []
identityTransportCoefficient13 Physical.coordinateX Physical.coordinateZ =
  ℚRing.solve []
identityTransportCoefficient13 Physical.coordinateY Physical.coordinateX =
  ℚRing.solve []
identityTransportCoefficient13 Physical.coordinateY Physical.coordinateY =
  ℚRing.solve []
identityTransportCoefficient13 Physical.coordinateY Physical.coordinateZ =
  ℚRing.solve []
identityTransportCoefficient13 Physical.coordinateZ Physical.coordinateX =
  ℚRing.solve []
identityTransportCoefficient13 Physical.coordinateZ Physical.coordinateY =
  ℚRing.solve []
identityTransportCoefficient13 Physical.coordinateZ Physical.coordinateZ =
  ℚRing.solve []

BackgroundIdentityUnit : Background.Q.RationalQuaternion
BackgroundIdentityUnit = Background.Q.oneQ

identityBackground13 : Background.RationalSU2Background13
identityBackground13 = record
  { Background.RationalSU2Background13.link = λ axis site → BackgroundIdentityUnit
  ; Background.RationalSU2Background13.unitNorm = λ axis site → refl
  }

backgroundGaugeConstraintMatrix13 :
  Background.RationalSU2Background13 → Flat.GaugeRow13 → Flat.State13 → ℚ
backgroundGaugeConstraintMatrix13 background
    (pair outputCoordinate rowSite)
    (pair inputCoordinate (pair axis columnSite)) =
  lieDelta13 inputCoordinate outputCoordinate
    * siteDelta13 columnSite rowSite
  - transportCoefficient13 background outputCoordinate inputCoordinate axis columnSite
    * siteDelta13 (Flat.shiftForward13 axis columnSite) rowSite

identityTransportAtLink13 :
  ∀ outputCoordinate inputCoordinate axis site →
  transportCoefficient13 identityBackground13
    outputCoordinate inputCoordinate axis site
  ≡ lieDelta13 inputCoordinate outputCoordinate
identityTransportAtLink13 outputCoordinate inputCoordinate axis site =
  identityTransportCoefficient13 outputCoordinate inputCoordinate

identityBackgroundGaugeMatrixIsFlat13 :
  ∀ row column →
  backgroundGaugeConstraintMatrix13 identityBackground13 row column
  ≡ Flat.flatGaugeConstraintMatrix13 row column
identityBackgroundGaugeMatrixIsFlat13
    (pair outputCoordinate rowSite)
    (pair inputCoordinate (pair axis columnSite))
  rewrite identityTransportAtLink13
    outputCoordinate inputCoordinate axis columnSite =
  deltaProductExact inputCoordinate outputCoordinate rowSite axis columnSite
  where
  deltaProductExact :
    ∀ input output row currentAxis currentSite →
    lieDelta13 input output * siteDelta13 currentSite row
      - lieDelta13 input output
          * siteDelta13 (Flat.shiftForward13 currentAxis currentSite) row
    ≡ Flat.gaugeRowDelta13 (pair input currentSite) (pair output row)
      - Flat.gaugeRowDelta13
          (pair input (Flat.shiftForward13 currentAxis currentSite))
          (pair output row)
  deltaProductExact Physical.coordinateX Physical.coordinateX row currentAxis currentSite
    with siteDecidableEquality13 currentSite row
       | siteDecidableEquality13 (Flat.shiftForward13 currentAxis currentSite) row
  ... | yes _ | yes _ = refl
  ... | yes _ | no _ = refl
  ... | no _ | yes _ = refl
  ... | no _ | no _ = refl
  deltaProductExact Physical.coordinateX Physical.coordinateY row currentAxis currentSite = refl
  deltaProductExact Physical.coordinateX Physical.coordinateZ row currentAxis currentSite = refl
  deltaProductExact Physical.coordinateY Physical.coordinateX row currentAxis currentSite = refl
  deltaProductExact Physical.coordinateY Physical.coordinateY row currentAxis currentSite
    with siteDecidableEquality13 currentSite row
       | siteDecidableEquality13 (Flat.shiftForward13 currentAxis currentSite) row
  ... | yes _ | yes _ = refl
  ... | yes _ | no _ = refl
  ... | no _ | yes _ = refl
  ... | no _ | no _ = refl
  deltaProductExact Physical.coordinateY Physical.coordinateZ row currentAxis currentSite = refl
  deltaProductExact Physical.coordinateZ Physical.coordinateX row currentAxis currentSite = refl
  deltaProductExact Physical.coordinateZ Physical.coordinateY row currentAxis currentSite = refl
  deltaProductExact Physical.coordinateZ Physical.coordinateZ row currentAxis currentSite
    with siteDecidableEquality13 currentSite row
       | siteDecidableEquality13 (Flat.shiftForward13 currentAxis currentSite) row
  ... | yes _ | yes _ = refl
  ... | yes _ | no _ = refl
  ... | no _ | yes _ = refl
  ... | no _ | no _ = refl

backgroundMinusFlatEntry13 :
  ∀ background outputCoordinate rowSite inputCoordinate axis columnSite →
  backgroundGaugeConstraintMatrix13 background
      (pair outputCoordinate rowSite)
      (pair inputCoordinate (pair axis columnSite))
    - Flat.flatGaugeConstraintMatrix13
      (pair outputCoordinate rowSite)
      (pair inputCoordinate (pair axis columnSite))
  ≡ - Background.adjointDefectCoordinate13 background
      outputCoordinate inputCoordinate axis columnSite
      * siteDelta13 (Flat.shiftForward13 axis columnSite) rowSite
backgroundMinusFlatEntry13
    background outputCoordinate rowSite inputCoordinate axis columnSite =
  let
    unit = Background.inverseLink13 background axis columnSite
    basis = Background.basisQuaternion inputCoordinate

    coefficientDifference :
      transportCoefficient13 background outputCoordinate inputCoordinate axis columnSite
        - lieDelta13 inputCoordinate outputCoordinate
      ≡ Background.adjointDefectCoordinate13 background
          outputCoordinate inputCoordinate axis columnSite
    coefficientDifference =
      trans
        (cong
          (λ identityCoefficient →
            transportCoefficient13 background outputCoordinate inputCoordinate axis columnSite
            - identityCoefficient)
          (sym (identityTransportCoefficient13 outputCoordinate inputCoordinate)))
        (coordinateAdjointDifference outputCoordinate unit basis)
  in
  trans
    (cong
      (λ flatEntry →
        backgroundGaugeConstraintMatrix13 background
          (pair outputCoordinate rowSite)
          (pair inputCoordinate (pair axis columnSite))
        - flatEntry)
      (sym (identityBackgroundGaugeMatrixIsFlat13
        (pair outputCoordinate rowSite)
        (pair inputCoordinate (pair axis columnSite)))))
    (subst
      (λ difference →
        (lieDelta13 inputCoordinate outputCoordinate
            * siteDelta13 columnSite rowSite
          - transportCoefficient13 background outputCoordinate inputCoordinate axis columnSite
            * siteDelta13 (Flat.shiftForward13 axis columnSite) rowSite)
        - (lieDelta13 inputCoordinate outputCoordinate
            * siteDelta13 columnSite rowSite
          - lieDelta13 inputCoordinate outputCoordinate
            * siteDelta13 (Flat.shiftForward13 axis columnSite) rowSite)
        ≡ - difference
          * siteDelta13 (Flat.shiftForward13 axis columnSite) rowSite)
      (sym coefficientDifference)
      (ℚRing.solve-∀
        (lieDelta13 inputCoordinate outputCoordinate)
        (siteDelta13 columnSite rowSite)
        (siteDelta13 (Flat.shiftForward13 axis columnSite) rowSite)
        (transportCoefficient13 background outputCoordinate inputCoordinate axis columnSite)))
  where
  coordinateAdjointDifference :
    ∀ coordinate unit basis →
    Background.quaternionCoordinate coordinate
      (Adjoint.adjointTransport unit basis)
      - Background.quaternionCoordinate coordinate basis
    ≡ Background.quaternionCoordinate coordinate
      (Adjoint.adjointDefect unit basis)
  coordinateAdjointDifference Physical.coordinateX
      (Background.Q.quat u0 u1 u2 u3)
      (Background.Q.quat x0 x1 x2 x3) =
    ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3
  coordinateAdjointDifference Physical.coordinateY
      (Background.Q.quat u0 u1 u2 u3)
      (Background.Q.quat x0 x1 x2 x3) =
    ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3
  coordinateAdjointDifference Physical.coordinateZ
      (Background.Q.quat u0 u1 u2 u3)
      (Background.Q.quat x0 x1 x2 x3) =
    ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3

backgroundGaugeAdjointApply13 :
  Background.RationalSU2Background13 → Flat.GaugeMultiplier13 → Flat.StateVector13
backgroundGaugeAdjointApply13 background multiplier column =
  sumRational Flat.gaugeRows13
    (λ row → backgroundGaugeConstraintMatrix13 background row column * multiplier row)

transportedEndpointSelector13 :
  ∀ background multiplier outputCoordinate inputCoordinate axis site →
  sumRational Flat.gaugeRows13
    (λ { (pair currentCoordinate currentSite) →
      transportCoefficient13 background currentCoordinate inputCoordinate axis site
      * siteDelta13 (Flat.shiftForward13 axis site) currentSite
      * multiplier (pair currentCoordinate currentSite) })
  ≡ sumRational Physical.lieCoordinates3
    (λ currentCoordinate →
      transportCoefficient13 background currentCoordinate inputCoordinate axis site
      * multiplier (pair currentCoordinate (Flat.shiftForward13 axis site)))
transportedEndpointSelector13
    background multiplier outputCoordinate inputCoordinate axis site =
  trans
    (sumCartesian
      Physical.lieCoordinates3
      (physicalBlockSites Side13.side13)
      (λ row →
        transportCoefficient13 background (first row) inputCoordinate axis site
        * siteDelta13 (Flat.shiftForward13 axis site) (second row)
        * multiplier row))
    (sumRationalCong Physical.lieCoordinates3 _ _
      (λ currentCoordinate →
        trans
          (sumRationalCong
            (physicalBlockSites Side13.side13) _ _
            (λ currentSite →
              ℚRing.solve-∀
                (transportCoefficient13 background currentCoordinate inputCoordinate axis site)
                (siteDelta13 (Flat.shiftForward13 axis site) currentSite)
                (multiplier (pair currentCoordinate currentSite))))
          (trans
            (cong
              (transportCoefficient13 background currentCoordinate inputCoordinate axis site *_)
              (siteSelectorExact13
                (Flat.shiftForward13 axis site)
                (λ currentSite → multiplier (pair currentCoordinate currentSite))))
            refl)))

backgroundGaugeAdjointPointwise13 :
  ∀ background multiplier inputCoordinate axis site →
  backgroundGaugeAdjointApply13 background multiplier
    (pair inputCoordinate (pair axis site))
  ≡ Flat.flatGaugeAdjoint13 multiplier
      (pair inputCoordinate (pair axis site))
    + Background.gaugeAdjointDefect13 background multiplier
      (pair inputCoordinate (pair axis site))
backgroundGaugeAdjointPointwise13 background multiplier inputCoordinate axis site =
  let
    column = pair inputCoordinate (pair axis site)
    currentTarget = pair inputCoordinate site

    split :
      backgroundGaugeAdjointApply13 background multiplier column
      ≡ sumRational Flat.gaugeRows13
          (λ row →
            Flat.flatGaugeConstraintMatrix13 row column * multiplier row)
        + sumRational Flat.gaugeRows13
          (λ row →
            (backgroundGaugeConstraintMatrix13 background row column
              - Flat.flatGaugeConstraintMatrix13 row column) * multiplier row)
    split =
      trans
        (sumRationalCong Flat.gaugeRows13 _ _
          (λ row → ℚRing.solve-∀
            (backgroundGaugeConstraintMatrix13 background row column)
            (Flat.flatGaugeConstraintMatrix13 row column)
            (multiplier row)))
        (sumRationalAdd Flat.gaugeRows13
          (λ row → Flat.flatGaugeConstraintMatrix13 row column * multiplier row)
          (λ row →
            (backgroundGaugeConstraintMatrix13 background row column
              - Flat.flatGaugeConstraintMatrix13 row column) * multiplier row))

    flatExact :
      sumRational Flat.gaugeRows13
        (λ row → Flat.flatGaugeConstraintMatrix13 row column * multiplier row)
      ≡ Flat.flatGaugeAdjoint13 multiplier column
    flatExact = refl

    defectExact :
      sumRational Flat.gaugeRows13
        (λ row →
          (backgroundGaugeConstraintMatrix13 background row column
            - Flat.flatGaugeConstraintMatrix13 row column) * multiplier row)
      ≡ Background.gaugeAdjointDefect13 background multiplier column
    defectExact =
      trans
        (sumRationalCong Flat.gaugeRows13 _ _
          (λ { (pair outputCoordinate rowSite) →
            trans
              (cong (_* multiplier (pair outputCoordinate rowSite))
                (backgroundMinusFlatEntry13 background outputCoordinate rowSite
                  inputCoordinate axis site))
              (ℚRing.solve-∀
                (Background.adjointDefectCoordinate13 background
                  outputCoordinate inputCoordinate axis site)
                (siteDelta13 (Flat.shiftForward13 axis site) rowSite)
                (multiplier (pair outputCoordinate rowSite)))) }))
        (trans
          (cong -_
            (transportedEndpointSelector13
              background multiplier Physical.coordinateX inputCoordinate axis site))
          (defectCoordinateSumExact background multiplier inputCoordinate axis site))
  in
  trans split (cong₂ _+_ flatExact defectExact)
  where
  defectCoordinateSumExact :
    ∀ currentBackground currentMultiplier currentInput currentAxis currentSite →
    - sumRational Physical.lieCoordinates3
      (λ currentCoordinate →
        Background.adjointDefectCoordinate13 currentBackground
          currentCoordinate currentInput currentAxis currentSite
        * currentMultiplier
          (pair currentCoordinate (Flat.shiftForward13 currentAxis currentSite)))
    ≡ Background.gaugeAdjointDefect13 currentBackground currentMultiplier
      (pair currentInput (pair currentAxis currentSite))
  defectCoordinateSumExact currentBackground currentMultiplier currentInput currentAxis currentSite =
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

backgroundGaugeAdjointSameObject13 :
  ∀ background multiplier column →
  backgroundGaugeAdjointApply13 background multiplier column
  ≡ Flat.flatGaugeAdjoint13 multiplier column
    + Background.gaugeAdjointDefect13 background multiplier column
backgroundGaugeAdjointSameObject13 background multiplier
    (pair inputCoordinate (pair axis site)) =
  backgroundGaugeAdjointPointwise13
    background multiplier inputCoordinate axis site

path13BackgroundGaugeConstraintMatrixLevel : ProofLevel
path13BackgroundGaugeConstraintMatrixLevel = machineChecked

path13BackgroundGaugeAdjointSameObjectLevel : ProofLevel
path13BackgroundGaugeAdjointSameObjectLevel = machineChecked
