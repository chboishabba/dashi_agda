module DASHI.Physics.YangMills.BalabanPenaltyMismatchQuadraticForm where

------------------------------------------------------------------------
-- Literal quadratic-form realization of the `a Q*Q` versus `a I` seam.
--
-- CMP 99 (3.156) gives the physical coarse Hessian as an augmented Schur
-- form minus `a I`, whereas the next positive Gaussian representative adds
-- the next blocked constraint penalty `a Q*Q`.  On a fluctuation A the exact
-- mismatch is therefore
--
--   a <Q A, Q A> - a <A, A>.
--
-- Here Q is the already constructed blocked linear-average main term.  Both
-- finite sums are literal, and their gauge invariance is proved.  No sign,
-- smallness, determinant, or beta-projection estimate is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4 )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeEnumeration using
  ( allCube4
  ; allAxes
  )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure )
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( GaugeFunction4
  ; DirectedGaugeField4
  ; gaugeTransformBond
  )
open import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative using
  ( Vector
  ; action
  )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( additive
  ; DirectedAdjointBondField4
  ; transformAdjointBondField
  )
open import DASHI.Physics.YangMills.BalabanLinearBlockPathAverage using
  ( ScalarAdjointLinearModule
  ; linear
  ; Scalar
  )
open import DASHI.Physics.YangMills.BalabanBlockedLinearAverageMainTerm using
  ( BlockedAdjointBondField4
  ; restrictedCoarseGauge
  ; blockedLinearAverageMainTerm
  ; blockedLinearAverageMainTermGaugeCovariant
  )
open import DASHI.Physics.YangMills.BalabanFiniteAdjointQuadraticForms using
  ( AdjointInnerProductModule
  ; sumMap
  ; sumMapPointwise
  ; bondFieldSquaredNorm
  ; bondFieldSquaredNormGaugeInvariant
  )

record PenaltyQuadraticModule
  (group : GroupStructure) : Set₁ where
  field
    scalarLinear : ScalarAdjointLinearModule group

    zeroScalar : Scalar scalarLinear
    addScalar :
      Scalar scalarLinear →
      Scalar scalarLinear →
      Scalar scalarLinear
    multiplyScalar :
      Scalar scalarLinear →
      Scalar scalarLinear →
      Scalar scalarLinear
    subtractScalar :
      Scalar scalarLinear →
      Scalar scalarLinear →
      Scalar scalarLinear

    inner :
      Vector (additive (linear scalarLinear)) →
      Vector (additive (linear scalarLinear)) →
      Scalar scalarLinear

    innerActionInvariant :
      ∀ g X Y →
      inner
        (action (additive (linear scalarLinear)) g X)
        (action (additive (linear scalarLinear)) g Y)
      ≡ inner X Y

open PenaltyQuadraticModule public

asInnerProductModule :
  (group : GroupStructure) →
  PenaltyQuadraticModule group →
  AdjointInnerProductModule group
asInnerProductModule group quadratic = record
  { linear = linear (scalarLinear quadratic)
  ; Scalar = Scalar (scalarLinear quadratic)
  ; zeroScalar = zeroScalar quadratic
  ; addScalar = addScalar quadratic
  ; inner = inner quadratic
  ; innerActionInvariant = innerActionInvariant quadratic
  }

transformBlockedField :
  (M L : Nat) →
  (group : GroupStructure) →
  (quadratic : PenaltyQuadraticModule group) →
  GaugeFunction4 M group →
  BlockedAdjointBondField4 M L group (scalarLinear quadratic) →
  BlockedAdjointBondField4 M L group (scalarLinear quadratic)
transformBlockedField M L group quadratic gauge Q x axis =
  action (additive (linear (scalarLinear quadratic)))
    (gauge x) (Q x axis)

blockedFieldSquaredNorm :
  (M L : Nat) →
  (group : GroupStructure) →
  (quadratic : PenaltyQuadraticModule group) →
  BlockedAdjointBondField4 M L group (scalarLinear quadratic) →
  Scalar (scalarLinear quadratic)
blockedFieldSquaredNorm M L group quadratic Q =
  sumMap
    (zeroScalar quadratic)
    (addScalar quadratic)
    (λ x →
      sumMap
        (zeroScalar quadratic)
        (addScalar quadratic)
        (λ axis → inner quadratic (Q x axis) (Q x axis))
        allAxes)
    (allCube4 M)

blockedFieldSquaredNormPointwise :
  (M L : Nat) →
  (group : GroupStructure) →
  (quadratic : PenaltyQuadraticModule group) →
  (Q R : BlockedAdjointBondField4
    M L group (scalarLinear quadratic)) →
  (∀ x axis → Q x axis ≡ R x axis) →
  blockedFieldSquaredNorm M L group quadratic Q
  ≡ blockedFieldSquaredNorm M L group quadratic R
blockedFieldSquaredNormPointwise
  M L group quadratic Q R pointwise =
  sumMapPointwise
    (zeroScalar quadratic)
    (addScalar quadratic)
    _ _ (allCube4 M)
    (λ x →
      sumMapPointwise
        (zeroScalar quadratic)
        (addScalar quadratic)
        _ _ allAxes
        (λ axis →
          cong₂ (inner quadratic)
            (pointwise x axis)
            (pointwise x axis)))

blockedFieldSquaredNormGaugeInvariant :
  (M L : Nat) →
  (group : GroupStructure) →
  (quadratic : PenaltyQuadraticModule group) →
  (gauge : GaugeFunction4 M group) →
  (Q : BlockedAdjointBondField4
    M L group (scalarLinear quadratic)) →
  blockedFieldSquaredNorm M L group quadratic
    (transformBlockedField M L group quadratic gauge Q)
  ≡ blockedFieldSquaredNorm M L group quadratic Q
blockedFieldSquaredNormGaugeInvariant
  M L group quadratic gauge Q =
  sumMapPointwise
    (zeroScalar quadratic)
    (addScalar quadratic)
    _ _ (allCube4 M)
    (λ x →
      sumMapPointwise
        (zeroScalar quadratic)
        (addScalar quadratic)
        _ _ allAxes
        (λ axis →
          innerActionInvariant quadratic
            (gauge x) (Q x axis) (Q x axis)))

blockedAverageSquaredNormGaugeInvariant :
  (M L : Nat) →
  {{_ : NonZero (M * suc L)}} →
  (group : GroupStructure) →
  (quadratic : PenaltyQuadraticModule group) →
  (weight : Scalar (scalarLinear quadratic)) →
  (gauge : GaugeFunction4 (M * suc L) group) →
  (U : DirectedGaugeField4 (M * suc L) group) →
  (A : DirectedAdjointBondField4 (M * suc L) group
    (linear (scalarLinear quadratic))) →
  blockedFieldSquaredNorm M L group quadratic
    (blockedLinearAverageMainTerm {M = M} {L = L}
      group (scalarLinear quadratic) weight
      (gaugeTransformBond group gauge U)
      (transformAdjointBondField
        group (linear (scalarLinear quadratic)) gauge A))
  ≡
  blockedFieldSquaredNorm M L group quadratic
    (blockedLinearAverageMainTerm {M = M} {L = L}
      group (scalarLinear quadratic) weight U A)
blockedAverageSquaredNormGaugeInvariant
  M L group quadratic weight gauge U A =
  trans
    (blockedFieldSquaredNormPointwise
      M L group quadratic _ _
      (λ x axis →
        blockedLinearAverageMainTermGaugeCovariant
          {M = M} {L = L}
          group (scalarLinear quadratic) weight
          gauge U A x axis))
    (blockedFieldSquaredNormGaugeInvariant
      M L group quadratic
      (restrictedCoarseGauge {M = M} {L = L} group gauge)
      (blockedLinearAverageMainTerm {M = M} {L = L}
        group (scalarLinear quadratic) weight U A))

identityPenalty :
  (N : Nat) →
  (group : GroupStructure) →
  (quadratic : PenaltyQuadraticModule group) →
  Scalar (scalarLinear quadratic) →
  DirectedAdjointBondField4 N group
    (linear (scalarLinear quadratic)) →
  Scalar (scalarLinear quadratic)
identityPenalty N group quadratic a A =
  multiplyScalar quadratic a
    (bondFieldSquaredNorm {N = N}
      group (asInnerProductModule group quadratic) A)

blockedConstraintPenalty :
  (M L : Nat) →
  {{_ : NonZero (M * suc L)}} →
  (group : GroupStructure) →
  (quadratic : PenaltyQuadraticModule group) →
  Scalar (scalarLinear quadratic) →
  Scalar (scalarLinear quadratic) →
  DirectedGaugeField4 (M * suc L) group →
  DirectedAdjointBondField4 (M * suc L) group
    (linear (scalarLinear quadratic)) →
  Scalar (scalarLinear quadratic)
blockedConstraintPenalty M L group quadratic a weight U A =
  multiplyScalar quadratic a
    (blockedFieldSquaredNorm M L group quadratic
      (blockedLinearAverageMainTerm {M = M} {L = L}
        group (scalarLinear quadratic) weight U A))

penaltyMismatchQuadraticForm :
  (M L : Nat) →
  {{_ : NonZero (M * suc L)}} →
  (group : GroupStructure) →
  (quadratic : PenaltyQuadraticModule group) →
  Scalar (scalarLinear quadratic) →
  Scalar (scalarLinear quadratic) →
  DirectedGaugeField4 (M * suc L) group →
  DirectedAdjointBondField4 (M * suc L) group
    (linear (scalarLinear quadratic)) →
  Scalar (scalarLinear quadratic)
penaltyMismatchQuadraticForm M L group quadratic a weight U A =
  subtractScalar quadratic
    (blockedConstraintPenalty M L group quadratic a weight U A)
    (identityPenalty (M * suc L) group quadratic a A)

penaltyMismatchGaugeInvariant :
  (M L : Nat) →
  {{_ : NonZero (M * suc L)}} →
  (group : GroupStructure) →
  (quadratic : PenaltyQuadraticModule group) →
  (a weight : Scalar (scalarLinear quadratic)) →
  (gauge : GaugeFunction4 (M * suc L) group) →
  (U : DirectedGaugeField4 (M * suc L) group) →
  (A : DirectedAdjointBondField4 (M * suc L) group
    (linear (scalarLinear quadratic))) →
  penaltyMismatchQuadraticForm M L
    group quadratic a weight
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField
      group (linear (scalarLinear quadratic)) gauge A)
  ≡
  penaltyMismatchQuadraticForm M L
    group quadratic a weight U A
penaltyMismatchGaugeInvariant
  M L group quadratic a weight gauge U A =
  cong₂ (subtractScalar quadratic)
    (cong
      (multiplyScalar quadratic a)
      (blockedAverageSquaredNormGaugeInvariant
        M L group quadratic weight gauge U A))
    (cong
      (multiplyScalar quadratic a)
      (bondFieldSquaredNormGaugeInvariant
        {N = M * suc L}
        group (asInnerProductModule group quadratic)
        gauge A))
