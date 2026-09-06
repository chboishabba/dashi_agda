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
-- explicit and constructs the positive-bond rational Lie3 projection exactly.
--
-- The remaining physical weld must combine this spatial projection with:
--   * rational Lie3 -> real SU(2) transport (R207, already generic theorem);
--   * the exact signed-orientation rule for negative bonds;
--   * rational scalar multiplication -> real Lie scalar multiplication;
--   * a two-carrier Eq.(119) formula whose global Q' input/output is the
--     Path13 field while local R0 values live in SU2LieAlgebra.
--
-- No direct identification with the unrelated SFGC three-point variation
-- fixture is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (PositiveBond; pair)
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

Path13PerturbationCoordinate : Set
Path13PerturbationCoordinate = Physical.PhysicalSU2Coordinate Side13.side13

Path13RationalPerturbation : Set
Path13RationalPerturbation = Path13PerturbationCoordinate → ℚ

Path13PositiveBond : Set
Path13PositiveBond = PositiveBond Side13.side13

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

HistoricalEq119Vector : Set
HistoricalEq119Vector = R126.Vector (R146.additive R178.su2SignedCarrier)

historicalEq119VectorIsLocalLie : HistoricalEq119Vector → Lie.SU2LieAlgebra
historicalEq119VectorIsLocalLie value = value

record Path13GlobalLocalPerturbationSemantics : Set₁ where
  field
    rationalRealEmbedding : Embed.OrderedAdditiveRationalRealEmbedding

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

    scalarAction : ℚ → Lie.SU2LieAlgebra → Lie.SU2LieAlgebra

    physicalQPrime : Nat → Path13RationalPerturbation → Path13RationalPerturbation

open Path13GlobalLocalPerturbationSemantics public

cmp98Path13PositiveBondPerturbationProjectionLevel : ProofLevel
cmp98Path13PositiveBondPerturbationProjectionLevel = machineChecked

cmp98HistoricalEq119LocalCarrierAuditLevel : ProofLevel
cmp98HistoricalEq119LocalCarrierAuditLevel = machineChecked

literalCMP98Path13GlobalLocalPerturbationSemanticsLevel : ProofLevel
literalCMP98Path13GlobalLocalPerturbationSemanticsLevel = conditional
