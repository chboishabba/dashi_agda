module DASHI.Physics.YangMills.BalabanCMP109FixedCoordinateGaussianPositivePatchExact where

------------------------------------------------------------------------
-- ROW A1: POSITIVE PATCH FOR THE SOURCE-NATIVE FIXED-COORDINATE GAUSSIAN
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- SOURCE-NATIVE REPLACEMENT FOR THE OLDER W/Q/R PATCH
--
-- After the CMP109 linearizing change of variables the Gaussian is written on
-- free coordinates B with restricted operator
--
--      Ahat(U) = C(U)^* A(U) C(U).
--
-- Its first variation is
--
--      Ahat' = C'^* A C + C^* A' C + C^* A C'.
--
-- The old positive-patch consumer treated Wilson, averaging and projection
-- changes as three unrelated additive errors.  This file instead separates the
-- source-native derivative into:
--
--   * middlePhysical = C^* A' C;
--   * tangentialConnection = the C'=CK part, which cancels the induced
--     coordinate-volume Jacobian exactly;
--   * normalConnection = genuine motion of the constrained subspace.
--
-- Thus only middlePhysical + normalConnection has to win on the positive patch.
-- The Wilson part of A' is now supplied by the exact physical 64-atom mixed
-- Wilson jet; Q' enters only through the normal C' solve QC'=-Q'C.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanFiniteRationalTraceConnectionCancellationExact as Trace

------------------------------------------------------------------------
-- Exact patch arithmetic after tangential coordinate cancellation.
------------------------------------------------------------------------

record FixedCoordinatePatchContribution : Set₁ where
  field
    middlePhysical normalConnection totalContribution : ℚ
    middleFloor normalBudget : ℚ

    totalExact : totalContribution ≡ middlePhysical + normalConnection
    middleLower : middleFloor ≤ middlePhysical
    normalConnectionLower : - normalBudget ≤ normalConnection

open FixedCoordinatePatchContribution public

fixedCoordinatePatchLower :
  (dataSet : FixedCoordinatePatchContribution) →
  middleFloor dataSet - normalBudget dataSet
  ≤ totalContribution dataSet
fixedCoordinatePatchLower dataSet =
  let
    summed :
      middleFloor dataSet + (- normalBudget dataSet)
      ≤ middlePhysical dataSet + normalConnection dataSet
    summed = ℚP.+-mono-≤
      (middleLower dataSet) (normalConnectionLower dataSet)
  in
  subst
    (λ upper → middleFloor dataSet - normalBudget dataSet ≤ upper)
    (sym (totalExact dataSet))
    (subst
      (λ lower → lower
        ≤ middlePhysical dataSet + normalConnection dataSet)
      (ℚRing.solve-∀ (middleFloor dataSet) (normalBudget dataSet))
      summed)

record FixedCoordinatePatchBox : Set₁ where
  field
    box : Integral.BoxIntegralEnclosure
    contribution : FixedCoordinatePatchContribution

    -- The box lower enclosure is for the SAME restricted trace contribution
    -- after the tangential coordinate/Jacobian cancellation.
    boxLowerIsRestrictedContribution :
      Integral.lowerContribution box ≡ totalContribution contribution

open FixedCoordinatePatchBox public

fixedCoordinateFloorBelowBoxLower :
  (patch : FixedCoordinatePatchBox) →
  middleFloor (contribution patch) - normalBudget (contribution patch)
  ≤ Integral.lowerContribution (box patch)
fixedCoordinateFloorBelowBoxLower patch =
  subst
    (λ upper →
      middleFloor (contribution patch) - normalBudget (contribution patch)
      ≤ upper)
    (sym (boxLowerIsRestrictedContribution patch))
    (fixedCoordinatePatchLower (contribution patch))

------------------------------------------------------------------------
-- One positive-measure patch plus nonnegative complement.
------------------------------------------------------------------------

record CMP109FixedCoordinateGaussianPositivePatch : Set₁ where
  field
    positivePatch : FixedCoordinatePatchBox
    complement : Agda.Builtin.List.List Integral.BoxIntegralEnclosure

    patchHasCutoffVolumeUniformPositiveMeasure : Set
    patchUsesMixedLorentzColorComponent : Set
    patchAvoidsWilsonMixedVertexZeroSet : Set

    complementIsSameRestrictedGaussianTrace : Set
    complementLowerNonnegative : 0ℚ ≤ Integral.boxLowerSum complement

    -- Tangential free-coordinate motion is paired with the SAME induced
    -- coordinate-volume Jacobian and therefore contributes zero.
    TangentialIndex : Set
    tangentialResponse : Trace.InducedVolumeJacobianResponse TangentialIndex

open CMP109FixedCoordinateGaussianPositivePatch public

globalFixedCoordinateLowerFromPatch :
  (dataSet : CMP109FixedCoordinateGaussianPositivePatch) →
  middleFloor (contribution (positivePatch dataSet))
    - normalBudget (contribution (positivePatch dataSet))
  ≤ Integral.boxLowerSum
      (box (positivePatch dataSet) Agda.Builtin.List.∷ complement dataSet)
globalFixedCoordinateLowerFromPatch dataSet =
  let
    patchLower = fixedCoordinateFloorBelowBoxLower (positivePatch dataSet)
    rest = complementLowerNonnegative dataSet
    appendLower :
      Integral.lowerContribution (box (positivePatch dataSet))
      ≤ Integral.lowerContribution (box (positivePatch dataSet))
        + Integral.boxLowerSum (complement dataSet)
    appendLower =
      subst
        (λ left → left
          ≤ Integral.lowerContribution (box (positivePatch dataSet))
            + Integral.boxLowerSum (complement dataSet))
        (ℚP.+-identityʳ
          (Integral.lowerContribution (box (positivePatch dataSet))))
        (ℚP.+-monoʳ-≤
          (Integral.lowerContribution (box (positivePatch dataSet))) rest)
  in
  ℚP.≤-trans patchLower appendLower

tangentialCoordinateContributionIsZero :
  (dataSet : CMP109FixedCoordinateGaussianPositivePatch) →
  Trace.logVolumeDerivative (tangentialResponse dataSet)
    - (+ 1 / 2)
      * Trace.matrixTrace
          (Trace.carrier (Trace.connection (tangentialResponse dataSet)))
          (DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact.multiplyMatrix
            (Trace.carrier (Trace.connection (tangentialResponse dataSet)))
            (Trace.inverseRestricted (Trace.connection (tangentialResponse dataSet)))
            (Trace.connectionVariation (Trace.connection (tangentialResponse dataSet))))
  ≡ 0ℚ
tangentialCoordinateContributionIsZero dataSet =
  Trace.gaussianTangentialConnectionCancelsVolumeJacobian
    (tangentialResponse dataSet)

------------------------------------------------------------------------
-- Literal source target.
------------------------------------------------------------------------

record CMP109FixedCoordinatePatchSourceTarget : Set₁ where
  field
    patchData : CMP109FixedCoordinateGaussianPositivePatch

    -- A' on the same restricted carrier.
    literalWilson64AtomMiddleTerm : Set
    literalCMP99GaugeFixingMiddleTerm : Set
    literalMiddlePhysicalAssembly : Set

    -- C' normal motion from the differentiated literal averaging constraint.
    literalCMP98OneStepQPrime : Set
    literalCMP99IteratedQPrime : Set
    literalEliminatedPivotNonzero : Set
    literalNormalCPrimeFromQPrime : Set
    literalNormalConnectionPatchBudget : Set

    -- Same-object measure statement needed by the exact tangential cancellation
    -- theorem rather than an independently supplied Jacobian correction.
    literalInducedCoordinateVolumeJacobian : Set

    -- Fourier same-object wiring.
    literal64AtomMixedWilsonFourierSymbol : Set
    literalRestrictedTraceUsesCanonicalWilsonPeriod : Set

open CMP109FixedCoordinatePatchSourceTarget public

fixedCoordinatePatchArithmeticLevel : ProofLevel
fixedCoordinatePatchArithmeticLevel = machineChecked

fixedCoordinateTangentialTraceCancellationLevel : ProofLevel
fixedCoordinateTangentialTraceCancellationLevel =
  Trace.tangentialConnectionTraceCancellationLevel

-- Physical/source leaves still open.
cmp109LiteralInducedCoordinateVolumeJacobianLevel : ProofLevel
cmp109LiteralInducedCoordinateVolumeJacobianLevel = conditional

cmp99LiteralNormalConnectionPatchBudgetLevel : ProofLevel
cmp99LiteralNormalConnectionPatchBudgetLevel = conditional

cmp99LiteralMixedWilson64AtomFourierSymbolLevel : ProofLevel
cmp99LiteralMixedWilson64AtomFourierSymbolLevel = conditional

cmp109FixedCoordinateGaussianPositivePatchLevel : ProofLevel
cmp109FixedCoordinateGaussianPositivePatchLevel = conditional
