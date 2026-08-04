module DASHI.Physics.YangMills.BalabanP33LiteralCovariantDivergenceDifferenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Expand the literal covariant divergence and prove
--
--   (d_U^* A)(x) - (d_1^* A)(x)
--
-- is exactly the sum over the four incoming positive bonds of
--
--   A(b) - Ad(U(reverse b)) A(b).
--
-- Thus the codifferential perturbation is reduced to four adjoint defects on
-- the actual periodic lattice, rather than being accepted as an operator-level
-- premise.  A finite norm induction is supplied after the exact identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using
  (cong₂; subst; sym; trans)

import Tactic.RingSolver as Solver

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  (Cube4; Axis4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  (DirectedBond4; positiveBond)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using
  (LatticePath4; empty; _▷_; reverseSingle)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeEnumeration using
  (allAxes)
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  (unitLeft)
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  (DirectedGaugeField4; directedPathTransport)
import DASHI.Physics.YangMills.BalabanLatticeCovariantDivergence as Divergence
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  (DirectedAdjointBondField4)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (SU2Quaternion; su2Identity; su2QuaternionGroup; realSolverRing)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Lie; su2LieExt; lieZero; lieAdd; lieSubtract
  ; su2Adjoint; su2AdjointUnit; su2AdjointLinearModule)
open import DASHI.Physics.YangMills.BalabanP33LiteralCovariantDerivativeDifferenceExact using
  (unitDirectedGauge)

lieSubtractCommonLeft :
  ∀ left middle right →
  lieSubtract (lieSubtract left middle) (lieSubtract left right)
  ≡ lieSubtract right middle
lieSubtractCommonLeft
    (su2Lie leftX leftY leftZ)
    (su2Lie middleX middleY middleZ)
    (su2Lie rightX rightY rightZ) =
  su2LieExt
    (Solver.solve
      (leftX ∷ middleX ∷ rightX ∷ []) realSolverRing)
    (Solver.solve
      (leftY ∷ middleY ∷ rightY ∷ []) realSolverRing)
    (Solver.solve
      (leftZ ∷ middleZ ∷ rightZ ∷ []) realSolverRing)

lieSubtractAddPair :
  ∀ firstLeft secondLeft firstRight secondRight →
  lieSubtract
    (lieAdd firstLeft secondLeft)
    (lieAdd firstRight secondRight)
  ≡ lieAdd
      (lieSubtract firstLeft firstRight)
      (lieSubtract secondLeft secondRight)
lieSubtractAddPair
    (su2Lie aX aY aZ)
    (su2Lie bX bY bZ)
    (su2Lie cX cY cZ)
    (su2Lie dX dY dZ) =
  su2LieExt
    (Solver.solve (aX ∷ bX ∷ cX ∷ dX ∷ []) realSolverRing)
    (Solver.solve (aY ∷ bY ∷ cY ∷ dY ∷ []) realSolverRing)
    (Solver.solve (aZ ∷ bZ ∷ cZ ∷ dZ ∷ []) realSolverRing)

lieSubtractZeroZero : lieSubtract lieZero lieZero ≡ lieZero
lieSubtractZeroZero =
  su2LieExt
    (Solver.solve [] realSolverRing)
    (Solver.solve [] realSolverRing)
    (Solver.solve [] realSolverRing)

directedPathTransportUnit :
  ∀ {N : Nat} {{_ : NonZero N}} {start finish : Cube4 N}
    (path : LatticePath4 start finish) →
  directedPathTransport su2QuaternionGroup unitDirectedGauge path
  ≡ su2Identity
directedPathTransportUnit empty = refl
directedPathTransportUnit (bond ▷ rest)
  rewrite directedPathTransportUnit rest =
  unitLeft su2QuaternionGroup su2Identity

flatTransportIncomingExact :
  ∀ {N : Nat} {{_ : NonZero N}}
    (bondField : DirectedAdjointBondField4
      N su2QuaternionGroup su2AdjointLinearModule)
    (site : Cube4 N) (axis : Axis4) →
  Divergence.transportIncoming
    su2QuaternionGroup su2AdjointLinearModule
    unitDirectedGauge bondField site axis
  ≡ bondField (Divergence.incomingPositiveBond site axis)
flatTransportIncomingExact bondField site axis
  rewrite directedPathTransportUnit
    (reverseSingle (Divergence.incomingPositiveBond site axis))
        | su2AdjointUnit
            (bondField (Divergence.incomingPositiveBond site axis)) =
  refl

incomingTransportDefect :
  ∀ {N : Nat} {{_ : NonZero N}} →
  DirectedGaugeField4 N su2QuaternionGroup →
  DirectedAdjointBondField4
    N su2QuaternionGroup su2AdjointLinearModule →
  Cube4 N → Axis4 → SU2LieAlgebra
incomingTransportDefect gaugeField bondField site axis =
  lieSubtract
    (bondField incoming)
    (Divergence.transportIncoming
      su2QuaternionGroup su2AdjointLinearModule
      gaugeField bondField site axis)
  where
    incoming : DirectedBond4 N
    incoming = Divergence.incomingPositiveBond site axis

axisDivergenceDifference :
  ∀ {N : Nat} {{_ : NonZero N}} →
  DirectedGaugeField4 N su2QuaternionGroup →
  DirectedAdjointBondField4
    N su2QuaternionGroup su2AdjointLinearModule →
  Cube4 N → Axis4 → SU2LieAlgebra
axisDivergenceDifference gaugeField bondField site axis =
  lieSubtract
    (Divergence.axisDivergenceContribution
      su2QuaternionGroup su2AdjointLinearModule
      gaugeField bondField site axis)
    (Divergence.axisDivergenceContribution
      su2QuaternionGroup su2AdjointLinearModule
      unitDirectedGauge bondField site axis)

axisDivergenceDifferenceExact :
  ∀ {N : Nat} {{_ : NonZero N}}
    (gaugeField : DirectedGaugeField4 N su2QuaternionGroup)
    (bondField : DirectedAdjointBondField4
      N su2QuaternionGroup su2AdjointLinearModule)
    (site : Cube4 N) (axis : Axis4) →
  axisDivergenceDifference gaugeField bondField site axis
  ≡ incomingTransportDefect gaugeField bondField site axis
axisDivergenceDifferenceExact gaugeField bondField site axis
  rewrite flatTransportIncomingExact bondField site axis =
  lieSubtractCommonLeft
    (bondField (positiveBond site axis))
    (Divergence.transportIncoming
      su2QuaternionGroup su2AdjointLinearModule
      gaugeField bondField site axis)
    (bondField (Divergence.incomingPositiveBond site axis))

sumIncomingTransportDefects :
  ∀ {N : Nat} {{_ : NonZero N}} →
  DirectedGaugeField4 N su2QuaternionGroup →
  DirectedAdjointBondField4
    N su2QuaternionGroup su2AdjointLinearModule →
  Cube4 N → List Axis4 → SU2LieAlgebra
sumIncomingTransportDefects gaugeField bondField site [] = lieZero
sumIncomingTransportDefects gaugeField bondField site (axis ∷ axes) =
  lieAdd
    (incomingTransportDefect gaugeField bondField site axis)
    (sumIncomingTransportDefects gaugeField bondField site axes)

sumAxisDivergenceDifferenceExact :
  ∀ {N : Nat} {{_ : NonZero N}}
    (gaugeField : DirectedGaugeField4 N su2QuaternionGroup)
    (bondField : DirectedAdjointBondField4
      N su2QuaternionGroup su2AdjointLinearModule)
    (site : Cube4 N) (axes : List Axis4) →
  lieSubtract
    (Divergence.sumAxisContributions
      su2QuaternionGroup su2AdjointLinearModule
      gaugeField bondField site axes)
    (Divergence.sumAxisContributions
      su2QuaternionGroup su2AdjointLinearModule
      unitDirectedGauge bondField site axes)
  ≡ sumIncomingTransportDefects gaugeField bondField site axes
sumAxisDivergenceDifferenceExact gaugeField bondField site [] =
  lieSubtractZeroZero
sumAxisDivergenceDifferenceExact
    gaugeField bondField site (axis ∷ axes) =
  trans
    (lieSubtractAddPair
      (Divergence.axisDivergenceContribution
        su2QuaternionGroup su2AdjointLinearModule
        gaugeField bondField site axis)
      (Divergence.sumAxisContributions
        su2QuaternionGroup su2AdjointLinearModule
        gaugeField bondField site axes)
      (Divergence.axisDivergenceContribution
        su2QuaternionGroup su2AdjointLinearModule
        unitDirectedGauge bondField site axis)
      (Divergence.sumAxisContributions
        su2QuaternionGroup su2AdjointLinearModule
        unitDirectedGauge bondField site axes))
    (cong₂ lieAdd
      (axisDivergenceDifferenceExact
        gaugeField bondField site axis)
      (sumAxisDivergenceDifferenceExact
        gaugeField bondField site axes))

covariantDivergenceDifference :
  ∀ {N : Nat} {{_ : NonZero N}} →
  DirectedGaugeField4 N su2QuaternionGroup →
  DirectedAdjointBondField4
    N su2QuaternionGroup su2AdjointLinearModule →
  Cube4 N → SU2LieAlgebra
covariantDivergenceDifference gaugeField bondField site =
  lieSubtract
    (Divergence.covariantDivergence
      su2QuaternionGroup su2AdjointLinearModule
      gaugeField bondField site)
    (Divergence.covariantDivergence
      su2QuaternionGroup su2AdjointLinearModule
      unitDirectedGauge bondField site)

covariantDivergenceDifferenceExact :
  ∀ {N : Nat} {{_ : NonZero N}}
    (gaugeField : DirectedGaugeField4 N su2QuaternionGroup)
    (bondField : DirectedAdjointBondField4
      N su2QuaternionGroup su2AdjointLinearModule)
    (site : Cube4 N) →
  covariantDivergenceDifference gaugeField bondField site
  ≡ sumIncomingTransportDefects gaugeField bondField site allAxes
covariantDivergenceDifferenceExact gaugeField bondField site =
  sumAxisDivergenceDifferenceExact gaugeField bondField site allAxes

------------------------------------------------------------------------
-- Finite norm induction for the four exact incoming defects.
------------------------------------------------------------------------

record NormedIncomingDefectSum (Bound : Set) : Set₁ where
  field
    vectorNorm : SU2LieAlgebra → Bound
    zeroBound : Bound
    addBound : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (addBound left right) (addBound lower upper)

    normZero : vectorNorm lieZero ≡ zeroBound
    normTriangle : ∀ left right →
      LessEqual
        (vectorNorm (lieAdd left right))
        (addBound (vectorNorm left) (vectorNorm right))

    incomingDefectMajorant :
      SU2Quaternion → SU2LieAlgebra → Bound
    incomingDefectBound : ∀ groupElement vector →
      LessEqual
        (vectorNorm (lieSubtract vector (su2Adjoint groupElement vector)))
        (incomingDefectMajorant groupElement vector)

open NormedIncomingDefectSum public

incomingPathTransport :
  ∀ {N : Nat} {{_ : NonZero N}} →
  DirectedGaugeField4 N su2QuaternionGroup →
  Cube4 N → Axis4 → SU2Quaternion
incomingPathTransport gaugeField site axis =
  directedPathTransport su2QuaternionGroup gaugeField
    (reverseSingle (Divergence.incomingPositiveBond site axis))

sumIncomingMajorants :
  ∀ {N : Nat} {{_ : NonZero N}} {Bound} →
  NormedIncomingDefectSum Bound →
  DirectedGaugeField4 N su2QuaternionGroup →
  DirectedAdjointBondField4
    N su2QuaternionGroup su2AdjointLinearModule →
  Cube4 N → List Axis4 → Bound
sumIncomingMajorants normed gaugeField bondField site [] = zeroBound normed
sumIncomingMajorants normed gaugeField bondField site (axis ∷ axes) =
  addBound normed
    (incomingDefectMajorant normed
      (incomingPathTransport gaugeField site axis)
      (bondField (Divergence.incomingPositiveBond site axis)))
    (sumIncomingMajorants normed gaugeField bondField site axes)

sumIncomingTransportDefectsNormBound :
  ∀ {N : Nat} {{_ : NonZero N}} {Bound}
    (normed : NormedIncomingDefectSum Bound)
    (gaugeField : DirectedGaugeField4 N su2QuaternionGroup)
    (bondField : DirectedAdjointBondField4
      N su2QuaternionGroup su2AdjointLinearModule)
    (site : Cube4 N) (axes : List Axis4) →
  LessEqual normed
    (vectorNorm normed
      (sumIncomingTransportDefects gaugeField bondField site axes))
    (sumIncomingMajorants normed gaugeField bondField site axes)
sumIncomingTransportDefectsNormBound
    normed gaugeField bondField site [] =
  subst
    (λ lower → LessEqual normed lower (zeroBound normed))
    (sym (normZero normed))
    (reflexive normed (zeroBound normed))
sumIncomingTransportDefectsNormBound
    normed gaugeField bondField site (axis ∷ axes) =
  transitive normed
    (normTriangle normed
      (incomingTransportDefect gaugeField bondField site axis)
      (sumIncomingTransportDefects gaugeField bondField site axes))
    (addMonotone normed
      (incomingDefectBound normed
        (incomingPathTransport gaugeField site axis)
        (bondField (Divergence.incomingPositiveBond site axis)))
      (sumIncomingTransportDefectsNormBound
        normed gaugeField bondField site axes))

covariantDivergenceDifferenceNormBound :
  ∀ {N : Nat} {{_ : NonZero N}} {Bound}
    (normed : NormedIncomingDefectSum Bound)
    (gaugeField : DirectedGaugeField4 N su2QuaternionGroup)
    (bondField : DirectedAdjointBondField4
      N su2QuaternionGroup su2AdjointLinearModule)
    (site : Cube4 N) →
  LessEqual normed
    (vectorNorm normed
      (covariantDivergenceDifference gaugeField bondField site))
    (sumIncomingMajorants normed gaugeField bondField site allAxes)
covariantDivergenceDifferenceNormBound
    normed gaugeField bondField site =
  subst
    (λ selected → LessEqual normed
      (vectorNorm normed selected)
      (sumIncomingMajorants normed gaugeField bondField site allAxes))
    (sym (covariantDivergenceDifferenceExact gaugeField bondField site))
    (sumIncomingTransportDefectsNormBound
      normed gaugeField bondField site allAxes)

literalCovariantDivergenceDifferenceLevel : ProofLevel
literalCovariantDivergenceDifferenceLevel = machineChecked

literalCovariantDivergenceFourDefectsLevel : ProofLevel
literalCovariantDivergenceFourDefectsLevel = machineChecked

covariantDivergenceFiniteNormReductionLevel : ProofLevel
covariantDivergenceFiniteNormReductionLevel = machineChecked
