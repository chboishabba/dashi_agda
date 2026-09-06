{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact where

------------------------------------------------------------------------
-- CMP98 EQ. (119): PATH13 GLOBAL/LOCAL PERTURBATION CARRIER WELD
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- R147 uses one abstract `Vector` both for the global input A of Q' and for
-- every local bond/R0 Lie value.  R178 specializes that one carrier to the
-- three-coordinate `SU2LieAlgebra`.
--
-- The physical Path13 lane already owns the actual finite perturbation carrier
--
--   PhysicalSU2Coordinate 13 -> Q,
--
-- i.e. three rational Lie coordinates on every one of the four positive bonds
-- at every side-13 site.  This module makes the global/local distinction
-- explicit and constructs both the positive-bond and signed-bond projections.
--
-- For the left perturbation convention U_b(t)=exp(t A_b)U_b, the already-owned
-- oriented path calculus gives
--
--   positive occurrence:  A_b,
--   negative occurrence: -Ad_{U_b^-1} A_b.
--
-- The negative occurrence is constructed here entirely on the exact rational
-- Path13 quaternion carrier before applying the existing R207 rational-Lie3 to
-- real-SU(2) embedding compiler.  The local scalar action is likewise fixed to
-- literal Lie scaling by the embedded rational coefficient.
--
-- What remains open after this module is the genuinely global/local operator
-- seam: rebuild Eq.(119) with global Q' acting on the Path13 field while local
-- R0 values live in SU2LieAlgebra.  No SFGC action-scalar fixture is involved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; -_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Axis4; PositiveBond; pair)
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Blocks
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanFederbushRationalLieToRealSU2CarrierRound207Exact as R207
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Embed
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreTransportMatrixExact as Centre

Path13PerturbationCoordinate : Set
Path13PerturbationCoordinate = Physical.PhysicalSU2Coordinate Side13.side13

Path13RationalPerturbation : Set
Path13RationalPerturbation = Path13PerturbationCoordinate → ℚ

Path13PositiveBond : Set
Path13PositiveBond = PositiveBond Side13.side13

------------------------------------------------------------------------
-- Positive-bond projection.
------------------------------------------------------------------------

positiveBondLie3 :
  Path13RationalPerturbation →
  Path13PositiveBond → Jacobian.Lie3Vector
positiveBondLie3 perturbation (pair site axis) coordinate =
  perturbation (pair coordinate (pair axis site))

positiveBondLie3XExact :
  ∀ perturbation site axis →
  positiveBondLie3 perturbation (pair site axis) Physical.coordinateX
  ≡ perturbation (pair Physical.coordinateX (pair axis site))
positiveBondLie3XExact perturbation site axis = refl

positiveBondLie3YExact :
  ∀ perturbation site axis →
  positiveBondLie3 perturbation (pair site axis) Physical.coordinateY
  ≡ perturbation (pair Physical.coordinateY (pair axis site))
positiveBondLie3YExact perturbation site axis = refl

positiveBondLie3ZExact :
  ∀ perturbation site axis →
  positiveBondLie3 perturbation (pair site axis) Physical.coordinateZ
  ≡ perturbation (pair Physical.coordinateZ (pair axis site))
positiveBondLie3ZExact perturbation site axis = refl

positiveBondRealLie :
  Embed.OrderedAdditiveRationalRealEmbedding →
  Path13RationalPerturbation →
  Path13PositiveBond → Lie.SU2LieAlgebra
positiveBondRealLie embedding perturbation bond =
  R207.embedRationalLie3 embedding (positiveBondLie3 perturbation bond)

positiveBondRealLieCoordinateExact :
  ∀ embedding perturbation bond coordinate →
  R207.realLieCoordinate coordinate
    (positiveBondRealLie embedding perturbation bond)
  ≡ Embed.embed (Embed.base embedding)
      (positiveBondLie3 perturbation bond coordinate)
positiveBondRealLieCoordinateExact embedding perturbation bond coordinate =
  R207.embedRationalLie3CoordinateExact
    embedding (positiveBondLie3 perturbation bond) coordinate

------------------------------------------------------------------------
-- Signed occurrence projection on the exact rational Path13 background.
------------------------------------------------------------------------

negativeUnderlyingSite :
  Blocks.PhysicalBlockL Side13.side13 → Axis4 →
  Blocks.PhysicalBlockL Side13.side13
negativeUnderlyingSite site axis =
  Bond.negativeStep {n = R192.path13PeriodicIndex} site axis

signedUnderlyingBond :
  Blocks.PhysicalBlockL Side13.side13 → Word.SignedAxis4 → Path13PositiveBond
signedUnderlyingBond site (pair axis true) = pair site axis
signedUnderlyingBond site (pair axis false) =
  pair (negativeUnderlyingSite site axis) axis

rationalSignedBondLie3 :
  Background.RationalSU2Background13 →
  Path13RationalPerturbation →
  Blocks.PhysicalBlockL Side13.side13 →
  Word.SignedAxis4 → Jacobian.Lie3Vector
rationalSignedBondLie3 background perturbation site (pair axis true) =
  positiveBondLie3 perturbation (pair site axis)
rationalSignedBondLie3 background perturbation site (pair axis false) coordinate =
  - Background.quaternionCoordinate coordinate
      (Adjoint.adjointTransport
        (Background.inverseLink13 background axis
          (negativeUnderlyingSite site axis))
        (Centre.lieVectorQuaternion
          (positiveBondLie3 perturbation
            (pair (negativeUnderlyingSite site axis) axis))))

rationalSignedBondPositiveExact :
  ∀ background perturbation site axis coordinate →
  rationalSignedBondLie3 background perturbation site (pair axis true) coordinate
  ≡ positiveBondLie3 perturbation (pair site axis) coordinate
rationalSignedBondPositiveExact background perturbation site axis coordinate = refl

rationalSignedBondNegativeExact :
  ∀ background perturbation site axis coordinate →
  rationalSignedBondLie3 background perturbation site (pair axis false) coordinate
  ≡
  - Background.quaternionCoordinate coordinate
      (Adjoint.adjointTransport
        (Background.inverseLink13 background axis
          (negativeUnderlyingSite site axis))
        (Centre.lieVectorQuaternion
          (positiveBondLie3 perturbation
            (pair (negativeUnderlyingSite site axis) axis))))
rationalSignedBondNegativeExact background perturbation site axis coordinate = refl

signedBondRealLie :
  Embed.OrderedAdditiveRationalRealEmbedding →
  Background.RationalSU2Background13 →
  Path13RationalPerturbation →
  Blocks.PhysicalBlockL Side13.side13 →
  Word.SignedAxis4 → Lie.SU2LieAlgebra
signedBondRealLie embedding background perturbation site direction =
  R207.embedRationalLie3 embedding
    (rationalSignedBondLie3 background perturbation site direction)

signedBondRealLieCoordinateExact :
  ∀ embedding background perturbation site direction coordinate →
  R207.realLieCoordinate coordinate
    (signedBondRealLie embedding background perturbation site direction)
  ≡ Embed.embed (Embed.base embedding)
      (rationalSignedBondLie3
        background perturbation site direction coordinate)
signedBondRealLieCoordinateExact
    embedding background perturbation site direction coordinate =
  R207.embedRationalLie3CoordinateExact
    embedding
    (rationalSignedBondLie3 background perturbation site direction)
    coordinate

------------------------------------------------------------------------
-- Canonical local scalar action.
------------------------------------------------------------------------

canonicalLocalScalarAction :
  Embed.OrderedAdditiveRationalRealEmbedding →
  ℚ → Lie.SU2LieAlgebra → Lie.SU2LieAlgebra
canonicalLocalScalarAction embedding scalar vector =
  Lie.lieScale (Embed.embed (Embed.base embedding) scalar) vector

------------------------------------------------------------------------
-- Historical one-carrier audit and strengthened physical target.
------------------------------------------------------------------------

HistoricalEq119Vector : Set
HistoricalEq119Vector = R126.Vector (R146.additive R178.su2SignedCarrier)

historicalEq119VectorIsLocalLie : HistoricalEq119Vector → Lie.SU2LieAlgebra
historicalEq119VectorIsLocalLie value = value

record Path13GlobalLocalPerturbationSemantics : Set₁ where
  field
    rationalRealEmbedding : Embed.OrderedAdditiveRationalRealEmbedding
    background : Background.RationalSU2Background13

    globalPerturbation : Set
    localLie : Set

    globalPerturbationIsPath13 : globalPerturbation ≡ Path13RationalPerturbation
    localLieIsSU2 : localLie ≡ Lie.SU2LieAlgebra

    positiveBondProjection :
      Path13RationalPerturbation → Path13PositiveBond → Lie.SU2LieAlgebra

    positiveBondProjectionIsCanonical :
      ∀ perturbation bond →
      positiveBondProjection perturbation bond
      ≡ positiveBondRealLie rationalRealEmbedding perturbation bond

    signedBondProjection :
      Path13RationalPerturbation →
      Blocks.PhysicalBlockL Side13.side13 →
      Word.SignedAxis4 →
      Lie.SU2LieAlgebra

    signedBondProjectionIsCanonical :
      ∀ perturbation site direction →
      signedBondProjection perturbation site direction
      ≡ signedBondRealLie
          rationalRealEmbedding background perturbation site direction

    scalarAction : ℚ → Lie.SU2LieAlgebra → Lie.SU2LieAlgebra

    scalarActionIsCanonical :
      scalarAction ≡ canonicalLocalScalarAction rationalRealEmbedding

    physicalQPrime : Nat → Path13RationalPerturbation → Path13RationalPerturbation

open Path13GlobalLocalPerturbationSemantics public

cmp98Path13PositiveBondPerturbationProjectionLevel : ProofLevel
cmp98Path13PositiveBondPerturbationProjectionLevel = machineChecked

cmp98Path13RationalSignedBondProjectionLevel : ProofLevel
cmp98Path13RationalSignedBondProjectionLevel = machineChecked

cmp98Path13SignedBondRealEmbeddingCompilerLevel : ProofLevel
cmp98Path13SignedBondRealEmbeddingCompilerLevel = machineChecked

cmp98Path13CanonicalLocalScalarActionLevel : ProofLevel
cmp98Path13CanonicalLocalScalarActionLevel = machineChecked

cmp98HistoricalEq119LocalCarrierAuditLevel : ProofLevel
cmp98HistoricalEq119LocalCarrierAuditLevel = machineChecked

-- Bond projection and local scalar action are no longer open subleaves.  The
-- surviving producer is the two-carrier global/local Eq.(119) operator itself.
literalCMP98Path13GlobalLocalPerturbationSemanticsLevel : ProofLevel
literalCMP98Path13GlobalLocalPerturbationSemanticsLevel = conditional
