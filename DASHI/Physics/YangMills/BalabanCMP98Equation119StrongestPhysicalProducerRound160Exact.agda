{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119StrongestPhysicalProducerRound160Exact where

------------------------------------------------------------------------
-- ROUND160 A1 BIDI: STRONGEST EQ. (119) PRODUCER
--
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- This module composes the least-privilege improvements rather than exposing an
-- older, weaker interface to downstream consumers:
--   R158 fixes the coarse fine-segment length to L=13 and, after R162/R163,
--        derives translation commutation, c+, and the whole plus embedding from
--        one minus embedding plus source axis/orientation;
--   R155-R157 construct Y_x from literal path holonomy and route chart admission
--        through the generic physical principal-log interface;
--   R159 constructs the full left/right dexp family from one exp/log
--        differential calculus plus adjoint transport.
--
-- IMPORTANT BIDI AUDIT: `PhysicalSU2PrincipalLogMeaning` is an interface whose
-- fields include the physical small-field/image theorem; it is not by itself a
-- concrete source instantiation.  Therefore R157 removes duplicate pointwise
-- receipts only CONDITIONALLY on that physical meaning being instantiated for
-- the literal Balaban background.  We do not count that physical theorem closed.
--
-- Consequently the direct Eq. (119) consumer below accepts no arbitrary Q', no
-- arbitrary path values, no point Y_x values, no log function, no arbitrary LR
-- family, no arbitrary coarse segment length, no independent plus embedding,
-- and no translation-commutation proof.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119PhysicalPrincipalImageRound157Exact as R157
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log

strongestPhysicalOneStepDerivative :
  ∀ {C n Group group Field CoarseBond FineBond Radius}
    (source : R158.CanonicalL13Equation119Source C n Group group)
    (meaning : Log.PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond
      (R126.Vector (R146.additive C)) Group Radius) →
  R157.CMP98RelativeContourPhysicalBridge
    (R158.asRound152Source source) meaning →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
strongestPhysicalOneStepDerivative source meaning bridge calculus =
  R157.physicalPrincipalImageOneStepDerivative
    (R158.asRound152Source source)
    meaning
    bridge
    (R159.asUniformLeftRightDexpFamily calculus)

strongestPhysicalMultiscaleDerivative :
  ∀ {C n Group group Field CoarseBond FineBond Radius}
    (source : R158.CanonicalL13Equation119Source C n Group group)
    (meaning : Log.PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond
      (R126.Vector (R146.additive C)) Group Radius) →
  R157.CMP98RelativeContourPhysicalBridge
    (R158.asRound152Source source) meaning →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
strongestPhysicalMultiscaleDerivative source meaning bridge calculus =
  R157.physicalPrincipalImageMultiscaleDerivative
    (R158.asRound152Source source)
    meaning
    bridge
    (R159.asUniformLeftRightDexpFamily calculus)

cmp98Equation119StrongestPhysicalProducerRound160Level : ProofLevel
cmp98Equation119StrongestPhysicalProducerRound160Level = machineChecked

-- Current literal same-object cut after R161-R163:
--   * identify which source axis/orientation is CMP98's printed coarse bond c;
--     the translated c+ embedding/endpoint is then construction;
--   * instantiate the physical small-field principal-log interface on the
--     literal Round155 relative holonomy, rather than merely postulating a
--     generic `PhysicalSU2PrincipalLogMeaning`;
--   * identify the principal-log/differential/adjoint normalizations with
--     CMP98's printed exp(iY), (1/i)log, g and R conventions.
-- R161 additionally welds the path reversal/holonomy convention to the existing
-- periodic inverse-path and P33 occurrence-holonomy owners.
literalCMP98StrongestSameObjectCutRound160Level : ProofLevel
literalCMP98StrongestSameObjectCutRound160Level = conditional
