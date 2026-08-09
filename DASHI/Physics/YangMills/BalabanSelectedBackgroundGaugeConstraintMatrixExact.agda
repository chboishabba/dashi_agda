module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact where

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
-- Turn the already literal covariant backward-divergence derivative into its
-- actual finite rectangular KKT row matrix.  The matrix is not independently
-- supplied: its (r,c) entry is the physical derivative evaluated on the
-- literal coordinate basis vector e_c.  Exact quaternion algebra proves the
-- derivative is linear, and the finite coordinate-expansion theorem proves
--
--   (L_gauge(A) v)(r)
--     = D F_A[decode(v)](r).
--
-- This closes the gauge-fixing component of the requested physical L_A.
-- The block-average component and the combined pseudoinverse remain separate
-- producer obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanFiniteLinearFunctionalCoordinatesExact as Linear

scaleQuaternion : ℚ → Q.RationalQuaternion → Q.RationalQuaternion
scaleQuaternion coefficient (Q.quat a0 a1 a2 a3) =
  Q.quat
    (coefficient * a0) (coefficient * a1)
    (coefficient * a2) (coefficient * a3)

adjointTransportZeroExact : ∀ unit →
  Adjoint.adjointTransport unit Q.zeroQ ≡ Q.zeroQ
adjointTransportZeroExact (Q.quat u0 u1 u2 u3) =
  Q.quaternionExt
    (ℚRing.solve-∀ u0 u1 u2 u3)
    (ℚRing.solve-∀ u0 u1 u2 u3)
    (ℚRing.solve-∀ u0 u1 u2 u3)
    (ℚRing.solve-∀ u0 u1 u2 u3)

adjointTransportAddExact : ∀ unit left right →
  Adjoint.adjointTransport unit (left Q.+q right)
  ≡ Adjoint.adjointTransport unit left
      Q.+q Adjoint.adjointTransport unit right
adjointTransportAddExact
    (Q.quat u0 u1 u2 u3)
    (Q.quat x0 x1 x2 x3)
    (Q.quat y0 y1 y2 y3) =
  Q.quaternionExt
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3 y0 y1 y2 y3)
    (ℚRing.solve-∀ u0 u1 u2 u3 x0 x1 x2 x3 y0 y1 y2 y3)

adjointTransportScaleExact : ∀ coefficient unit value →
  Adjoint.adjointTransport unit (scaleQuaternion coefficient value)
  ≡ scaleQuaternion coefficient (Adjoint.adjointTransport unit value)
adjointTransportScaleExact coefficient
    (Q.quat u0 u1 u2 u3) (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ coefficient u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ coefficient u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ coefficient u0 u1 u2 u3 x0 x1 x2 x3)
    (ℚRing.solve-∀ coefficient u0 u1 u2 u3 x0 x1 x2 x3)

quaternionCoordinateZeroExact : ∀ coordinate →
  Gauge.quaternionCoordinate coordinate Q.zeroQ ≡ 0ℚ
quaternionCoordinateZeroExact Coordinates.coordinateX = refl
quaternionCoordinateZeroExact Coordinates.coordinateY = refl
quaternionCoordinateZeroExact Coordinates.coordinateZ = refl

quaternionCoordinateAddExact : ∀ coordinate left right →
  Gauge.quaternionCoordinate coordinate (left Q.+q right)
  ≡ Gauge.quaternionCoordinate coordinate left
      + Gauge.quaternionCoordinate coordinate right
quaternionCoordinateAddExact Coordinates.coordinateX
    (Q.quat x0 x1 x2 x3) (Q.quat y0 y1 y2 y3) =
  ℚRing.solve-∀ x1 y1
quaternionCoordinateAddExact Coordinates.coordinateY
    (Q.quat x0 x1 x2 x3) (Q.quat y0 y1 y2 y3) =
  ℚRing.solve-∀ x2 y2
quaternionCoordinateAddExact Coordinates.coordinateZ
    (Q.quat x0 x1 x2 x3) (Q.quat y0 y1 y2 y3) =
  ℚRing.solve-∀ x3 y3

quaternionCoordinateScaleExact : ∀ coordinate coefficient value →
  Gauge.quaternionCoordinate coordinate (scaleQuaternion coefficient value)
  ≡ coefficient * Gauge.quaternionCoordinate coordinate value
quaternionCoordinateScaleExact Coordinates.coordinateX coefficient
    (Q.quat x0 x1 x2 x3) = ℚRing.solve-∀ coefficient x1
quaternionCoordinateScaleExact Coordinates.coordinateY coefficient
    (Q.quat x0 x1 x2 x3) = ℚRing.solve-∀ coefficient x2
quaternionCoordinateScaleExact Coordinates.coordinateZ coefficient
    (Q.quat x0 x1 x2 x3) = ℚRing.solve-∀ coefficient x3

decodedInsertion :
  KKT.StateVector →
  Gauge.Periodic.Axis4 → Gauge.Periodic.Site4 →
  Q.RationalQuaternion
decodedInsertion vector axis site =
  Gauge.insertionQuaternion
    (Coordinates.decodePhysicalSU2 vector) axis site

decodedInsertionZeroExact : ∀ axis site →
  decodedInsertion Linear.zeroVector axis site ≡ Q.zeroQ
decodedInsertionZeroExact axis site = refl

decodedInsertionAddExact : ∀ left right axis site →
  decodedInsertion (Linear.addVector left right) axis site
  ≡ decodedInsertion left axis site Q.+q decodedInsertion right axis site
decodedInsertionAddExact left right axis site =
  Q.quaternionExt
    (ℚRing.solve [])
    (ℚRing.solve-∀
      (left (pair Coordinates.coordinateX (pair axis site)))
      (right (pair Coordinates.coordinateX (pair axis site))))
    (ℚRing.solve-∀
      (left (pair Coordinates.coordinateY (pair axis site)))
      (right (pair Coordinates.coordinateY (pair axis site))))
    (ℚRing.solve-∀
      (left (pair Coordinates.coordinateZ (pair axis site)))
      (right (pair Coordinates.coordinateZ (pair axis site))))

decodedInsertionScaleExact : ∀ coefficient vector axis site →
  decodedInsertion (Linear.scaleVector coefficient vector) axis site
  ≡ scaleQuaternion coefficient (decodedInsertion vector axis site)
decodedInsertionScaleExact coefficient vector axis site =
  Q.quaternionExt
    (ℚRing.solve [])
    (ℚRing.solve-∀ coefficient
      (vector (pair Coordinates.coordinateX (pair axis site))))
    (ℚRing.solve-∀ coefficient
      (vector (pair Coordinates.coordinateY (pair axis site))))
    (ℚRing.solve-∀ coefficient
      (vector (pair Coordinates.coordinateZ (pair axis site))))

decodedInsertionPointwiseCong : ∀ left right →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ axis site →
  decodedInsertion left axis site ≡ decodedInsertion right axis site
decodedInsertionPointwiseCong left right equal axis site =
  Q.quaternionExt
    refl
    (equal (pair Coordinates.coordinateX (pair axis site)))
    (equal (pair Coordinates.coordinateY (pair axis site)))
    (equal (pair Coordinates.coordinateZ (pair axis site)))

transportedDecoded :
  Physical.RationalSU2Background4 → KKT.StateVector →
  Gauge.Periodic.Axis4 → Gauge.Periodic.Site4 →
  Q.RationalQuaternion
transportedDecoded background vector axis site =
  Adjoint.adjointTransport
    (Gauge.backwardTransportUnit background axis site)
    (decodedInsertion vector axis (Gauge.Periodic.shiftBackward axis site))

transportedDecodedZeroExact : ∀ background axis site →
  transportedDecoded background Linear.zeroVector axis site ≡ Q.zeroQ
transportedDecodedZeroExact background axis site =
  trans
    (cong
      (Adjoint.adjointTransport
        (Gauge.backwardTransportUnit background axis site))
      (decodedInsertionZeroExact axis
        (Gauge.Periodic.shiftBackward axis site)))
    (adjointTransportZeroExact
      (Gauge.backwardTransportUnit background axis site))

transportedDecodedAddExact : ∀ background left right axis site →
  transportedDecoded background (Linear.addVector left right) axis site
  ≡ transportedDecoded background left axis site
      Q.+q transportedDecoded background right axis site
transportedDecodedAddExact background left right axis site =
  let
    previous = Gauge.Periodic.shiftBackward axis site
    unit = Gauge.backwardTransportUnit background axis site
  in
  trans
    (cong (Adjoint.adjointTransport unit)
      (decodedInsertionAddExact left right axis previous))
    (adjointTransportAddExact unit
      (decodedInsertion left axis previous)
      (decodedInsertion right axis previous))

transportedDecodedScaleExact : ∀ background coefficient vector axis site →
  transportedDecoded background
    (Linear.scaleVector coefficient vector) axis site
  ≡ scaleQuaternion coefficient
      (transportedDecoded background vector axis site)
transportedDecodedScaleExact background coefficient vector axis site =
  let
    previous = Gauge.Periodic.shiftBackward axis site
    unit = Gauge.backwardTransportUnit background axis site
  in
  trans
    (cong (Adjoint.adjointTransport unit)
      (decodedInsertionScaleExact coefficient vector axis previous))
    (adjointTransportScaleExact coefficient unit
      (decodedInsertion vector axis previous))

transportedDecodedPointwiseCong : ∀ background left right →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ axis site →
  transportedDecoded background left axis site
  ≡ transportedDecoded background right axis site
transportedDecodedPointwiseCong background left right equal axis site =
  cong
    (Adjoint.adjointTransport
      (Gauge.backwardTransportUnit background axis site))
    (decodedInsertionPointwiseCong left right equal axis
      (Gauge.Periodic.shiftBackward axis site))

decodedBackwardTerm :
  Physical.RationalSU2Background4 → KKT.StateVector →
  Coordinates.LieCoordinate3 →
  Gauge.Periodic.Axis4 → Gauge.Periodic.Site4 → ℚ
decodedBackwardTerm background vector coordinate axis site =
  vector (pair coordinate (pair axis site))
  - Gauge.quaternionCoordinate coordinate
      (transportedDecoded background vector axis site)

decodedBackwardZeroExact : ∀ background coordinate axis site →
  decodedBackwardTerm background Linear.zeroVector coordinate axis site
  ≡ 0ℚ
decodedBackwardZeroExact background coordinate axis site
  rewrite transportedDecodedZeroExact background axis site
        | quaternionCoordinateZeroExact coordinate =
  ℚRing.solve []

decodedBackwardAddExact : ∀ background left right coordinate axis site →
  decodedBackwardTerm background
    (Linear.addVector left right) coordinate axis site
  ≡ decodedBackwardTerm background left coordinate axis site
      + decodedBackwardTerm background right coordinate axis site
decodedBackwardAddExact background left right coordinate axis site
  rewrite transportedDecodedAddExact background left right axis site
        | quaternionCoordinateAddExact coordinate
            (transportedDecoded background left axis site)
            (transportedDecoded background right axis site) =
  ℚRing.solve-∀
    (left (pair coordinate (pair axis site)))
    (right (pair coordinate (pair axis site)))
    (Gauge.quaternionCoordinate coordinate
      (transportedDecoded background left axis site))
    (Gauge.quaternionCoordinate coordinate
      (transportedDecoded background right axis site))

decodedBackwardScaleExact :
  ∀ background coefficient vector coordinate axis site →
  decodedBackwardTerm background
    (Linear.scaleVector coefficient vector) coordinate axis site
  ≡ coefficient * decodedBackwardTerm
      background vector coordinate axis site
decodedBackwardScaleExact
    background coefficient vector coordinate axis site
  rewrite transportedDecodedScaleExact
      background coefficient vector axis site
        | quaternionCoordinateScaleExact coordinate coefficient
            (transportedDecoded background vector axis site) =
  ℚRing.solve-∀ coefficient
    (vector (pair coordinate (pair axis site)))
    (Gauge.quaternionCoordinate coordinate
      (transportedDecoded background vector axis site))

decodedBackwardPointwiseCong : ∀ background left right →
  (∀ selected → left selected ≡ right selected) →
  ∀ coordinate axis site →
  decodedBackwardTerm background left coordinate axis site
  ≡ decodedBackwardTerm background right coordinate axis site
decodedBackwardPointwiseCong
    background left right equal coordinate axis site =
  cong₂ _-_
    (equal (pair coordinate (pair axis site)))
    (cong (Gauge.quaternionCoordinate coordinate)
      (transportedDecodedPointwiseCong
        background left right equal axis site))

sumRationalAddExact : ∀ {A : Set} values (left right : A → ℚ) →
  Sums.sumRational values (λ value → left value + right value)
  ≡ Sums.sumRational values left + Sums.sumRational values right
sumRationalAddExact [] left right = ℚRing.solve []
sumRationalAddExact (value Agda.Builtin.List.∷ values) left right
  rewrite sumRationalAddExact values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (Sums.sumRational values left) (Sums.sumRational values right)

gaugeFunctional :
  Physical.RationalSU2Background4 → FlatGauge.GaugeCoordinate4 →
  KKT.StateVector → ℚ
gaugeFunctional background (pair coordinate site) vector =
  Sums.sumRational Gauge.axes4
    (λ axis →
      decodedBackwardTerm background vector coordinate axis site)

gaugeFunctionalIsPhysicalDerivative : ∀ background row vector →
  gaugeFunctional background row vector
  ≡ Gauge.backgroundGaugeFirst background
      (Coordinates.decodePhysicalSU2 vector) row
gaugeFunctionalIsPhysicalDerivative background (pair coordinate site) vector =
  Sums.sumRationalCong
    Gauge.axes4
    (λ axis → decodedBackwardTerm background vector coordinate axis site)
    (λ axis → Gauge.backgroundBackwardTerm background
      (Coordinates.decodePhysicalSU2 vector) coordinate axis site)
    (λ axis → refl)

gaugeFunctionalZeroExact : ∀ background row →
  gaugeFunctional background row Linear.zeroVector ≡ 0ℚ
gaugeFunctionalZeroExact background (pair coordinate site) =
  trans
    (Sums.sumRationalCong Gauge.axes4
      (λ axis → decodedBackwardTerm
        background Linear.zeroVector coordinate axis site)
      (λ _ → 0ℚ)
      (λ axis → decodedBackwardZeroExact
        background coordinate axis site))
    (Fubini.sumRationalZero Gauge.axes4)

gaugeFunctionalAddExact : ∀ background row left right →
  gaugeFunctional background row (Linear.addVector left right)
  ≡ gaugeFunctional background row left
      + gaugeFunctional background row right
gaugeFunctionalAddExact background (pair coordinate site) left right =
  trans
    (Sums.sumRationalCong Gauge.axes4
      (λ axis → decodedBackwardTerm background
        (Linear.addVector left right) coordinate axis site)
      (λ axis →
        decodedBackwardTerm background left coordinate axis site
        + decodedBackwardTerm background right coordinate axis site)
      (λ axis → decodedBackwardAddExact
        background left right coordinate axis site))
    (sumRationalAddExact Gauge.axes4
      (λ axis → decodedBackwardTerm
        background left coordinate axis site)
      (λ axis → decodedBackwardTerm
        background right coordinate axis site))

gaugeFunctionalScaleExact : ∀ background row coefficient vector →
  gaugeFunctional background row (Linear.scaleVector coefficient vector)
  ≡ coefficient * gaugeFunctional background row vector
gaugeFunctionalScaleExact
    background (pair coordinate site) coefficient vector =
  trans
    (Sums.sumRationalCong Gauge.axes4
      (λ axis → decodedBackwardTerm background
        (Linear.scaleVector coefficient vector) coordinate axis site)
      (λ axis → coefficient
        * decodedBackwardTerm background vector coordinate axis site)
      (λ axis → decodedBackwardScaleExact
        background coefficient vector coordinate axis site))
    (Sums.sumRationalScale coefficient Gauge.axes4
      (λ axis → decodedBackwardTerm
        background vector coordinate axis site))

gaugeFunctionalPointwiseCong : ∀ background row left right →
  (∀ selected → left selected ≡ right selected) →
  gaugeFunctional background row left ≡ gaugeFunctional background row right
gaugeFunctionalPointwiseCong
    background (pair coordinate site) left right equal =
  Sums.sumRationalCong Gauge.axes4
    (λ axis → decodedBackwardTerm background left coordinate axis site)
    (λ axis → decodedBackwardTerm background right coordinate axis site)
    (λ axis → decodedBackwardPointwiseCong
      background left right equal coordinate axis site)

selectedGaugeLinearFunctional :
  Physical.RationalSU2Background4 → FlatGauge.GaugeCoordinate4 →
  Linear.FiniteLinearFunctional KKT.physicalStateCarrier
selectedGaugeLinearFunctional background row = record
  { Linear.FiniteLinearFunctional.functional =
      gaugeFunctional background row
  ; Linear.FiniteLinearFunctional.zeroExact =
      gaugeFunctionalZeroExact background row
  ; Linear.FiniteLinearFunctional.addExact =
      gaugeFunctionalAddExact background row
  ; Linear.FiniteLinearFunctional.scaleExact =
      gaugeFunctionalScaleExact background row
  ; Linear.FiniteLinearFunctional.pointwiseCong =
      gaugeFunctionalPointwiseCong background row }

selectedBackgroundGaugeConstraintMatrix :
  Physical.RationalSU2Background4 →
  Rect.RectangularMatrix FlatGauge.GaugeCoordinate4 KKT.State
selectedBackgroundGaugeConstraintMatrix background row column =
  gaugeFunctional background row
    (Linear.basisVector KKT.physicalStateCarrier column)

selectedBackgroundGaugeConstraintMatrixApplyExact :
  ∀ background vector row →
  Rect.applyRectangular KKT.physicalStateCarrier
    (selectedBackgroundGaugeConstraintMatrix background) vector row
  ≡ Gauge.backgroundGaugeFirst background
      (Coordinates.decodePhysicalSU2 vector) row
selectedBackgroundGaugeConstraintMatrixApplyExact background vector row =
  trans
    (Linear.finiteLinearFunctionalCoordinateExpansion
      (selectedGaugeLinearFunctional background row) vector)
    (gaugeFunctionalIsPhysicalDerivative background row vector)

selectedGaugeConstraintMatrixLiteralLevel : ProofLevel
selectedGaugeConstraintMatrixLiteralLevel = machineChecked

selectedGaugeConstraintMatrixActionLevel : ProofLevel
selectedGaugeConstraintMatrixActionLevel = machineChecked
