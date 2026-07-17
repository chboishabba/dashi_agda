module DASHI.Physics.YangMills.BalabanLatticeCovariantDivergence where

------------------------------------------------------------------------
-- Literal bond-to-point covariant divergence.
--
-- For each positive coordinate direction at x, the incoming bond begins at
-- x-mu and ends at x.  Its adjoint-valued coefficient is transported back to
-- x along the reversed bond before subtracting it from the outgoing
-- coefficient.  Summing the four contributions gives the finite-lattice
-- codifferential used by the gauge-fixing quadratic form.
--
-- Gauge covariance is proved from path-transport covariance and the adjoint
-- module laws.  No adjointness, positivity, or propagator estimate is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; Axis4
  ; shiftBackward
  ; shiftForwardBackward
  )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  ( DirectedBond4
  ; positiveBond
  ; source
  ; target
  )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using
  ( reverseSingle )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeEnumeration using
  ( allAxes )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure )
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( DirectedGaugeField4
  ; GaugeFunction4
  ; gaugeTransformBond
  ; directedPathTransport
  ; pathTransportGaugeCovariant
  )
open import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative using
  ( Vector
  ; action
  ; subtract
  ; actionSubtract
  )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( AdjointLinearModule
  ; additive
  ; zeroVector
  ; addVector
  ; actionZero
  ; actionAdd
  ; DirectedAdjointBondField4
  ; transformAdjointBondField
  )
open import DASHI.Physics.YangMills.BalabanLinearBlockPathAverage using
  ( conjugatedTransportAction )

incomingPositiveBond :
  ∀ {N : Nat} {{_ : NonZero N}} →
  Cube4 N → Axis4 → DirectedBond4 N
incomingPositiveBond x axis =
  positiveBond (shiftBackward axis x) axis

incomingPositiveBondTarget :
  ∀ {N : Nat} {{_ : NonZero N}}
  (x : Cube4 N) (axis : Axis4) →
  target (incomingPositiveBond x axis) ≡ x
incomingPositiveBondTarget x axis =
  shiftForwardBackward axis x

transportIncoming :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  Cube4 N → Axis4 →
  Vector (additive linear)
transportIncoming group linear U A x axis =
  action (additive linear)
    (directedPathTransport group U (reverseSingle incoming))
    (A incoming)
  where
    incoming : DirectedBond4 _
    incoming = incomingPositiveBond x axis

transportIncomingGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  (x : Cube4 N) →
  (axis : Axis4) →
  transportIncoming group linear
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField group linear gauge A)
    x axis
  ≡
  action (additive linear) (gauge x)
    (transportIncoming group linear U A x axis)
transportIncomingGaugeCovariant
  group linear gauge U A x axis =
  trans
    (cong
      (λ transport →
        action (additive linear) transport
          (action (additive linear)
            (gauge (source incoming))
            (A incoming)))
      (pathTransportGaugeCovariant
        group gauge U (reverseSingle incoming)))
    (trans
      (conjugatedTransportAction
        group linear
        (gauge (target incoming))
        (directedPathTransport group U (reverseSingle incoming))
        (gauge (source incoming))
        (A incoming))
      (cong
        (λ g →
          action (additive linear) g
            (transportIncoming group linear U A x axis))
        (cong gauge (incomingPositiveBondTarget x axis))))
  where
    incoming : DirectedBond4 _
    incoming = incomingPositiveBond x axis

axisDivergenceContribution :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  Cube4 N → Axis4 →
  Vector (additive linear)
axisDivergenceContribution group linear U A x axis =
  subtract (additive linear)
    (A (positiveBond x axis))
    (transportIncoming group linear U A x axis)

axisDivergenceContributionGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  (x : Cube4 N) →
  (axis : Axis4) →
  axisDivergenceContribution group linear
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField group linear gauge A)
    x axis
  ≡
  action (additive linear) (gauge x)
    (axisDivergenceContribution group linear U A x axis)
axisDivergenceContributionGaugeCovariant
  group linear gauge U A x axis =
  trans
    (cong
      (subtract (additive linear)
        (action (additive linear) (gauge x)
          (A (positiveBond x axis))))
      (transportIncomingGaugeCovariant
        group linear gauge U A x axis))
    (sym
      (actionSubtract (additive linear)
        (gauge x)
        (A (positiveBond x axis))
        (transportIncoming group linear U A x axis)))

sumAxisContributions :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  Cube4 N →
  List Axis4 →
  Vector (additive linear)
sumAxisContributions group linear U A x [] = zeroVector linear
sumAxisContributions group linear U A x (axis ∷ axes) =
  addVector linear
    (axisDivergenceContribution group linear U A x axis)
    (sumAxisContributions group linear U A x axes)

sumAxisContributionsGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  (x : Cube4 N) →
  (axes : List Axis4) →
  sumAxisContributions group linear
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField group linear gauge A)
    x axes
  ≡
  action (additive linear) (gauge x)
    (sumAxisContributions group linear U A x axes)
sumAxisContributionsGaugeCovariant
  group linear gauge U A x [] =
  actionZero linear (gauge x)
sumAxisContributionsGaugeCovariant
  group linear gauge U A x (axis ∷ axes) =
  trans
    (cong
      (addVector linear
        (axisDivergenceContribution group linear
          (gaugeTransformBond group gauge U)
          (transformAdjointBondField group linear gauge A)
          x axis))
      (sumAxisContributionsGaugeCovariant
        group linear gauge U A x axes))
    (trans
      (cong
        (λ head →
          addVector linear head
            (action (additive linear) (gauge x)
              (sumAxisContributions group linear U A x axes)))
        (axisDivergenceContributionGaugeCovariant
          group linear gauge U A x axis))
      (sym
        (actionAdd linear
          (gauge x)
          (axisDivergenceContribution group linear U A x axis)
          (sumAxisContributions group linear U A x axes))))

covariantDivergence :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  Cube4 N →
  Vector (additive linear)
covariantDivergence group linear U A x =
  sumAxisContributions group linear U A x allAxes

covariantDivergenceGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  (x : Cube4 N) →
  covariantDivergence group linear
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField group linear gauge A)
    x
  ≡
  action (additive linear) (gauge x)
    (covariantDivergence group linear U A x)
covariantDivergenceGaugeCovariant
  group linear gauge U A x =
  sumAxisContributionsGaugeCovariant
    group linear gauge U A x allAxes
