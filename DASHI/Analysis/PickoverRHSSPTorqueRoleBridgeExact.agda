module DASHI.Analysis.PickoverRHSSPTorqueRoleBridgeExact where

------------------------------------------------------------------------
-- CONDITIONAL RH SOURCE-ROLE -> SIGNED SSP -> TORQUE PHASE WELD.
--
-- Reuses the source-owning RiemannSSP15ProducerMarkedSignedFRACTRANExact:
-- its producer-role certificate is an EXPLICIT parameter.  The chosen
-- O/j/s -> negative/neutral/positive indexing is a codec; its source
-- status must not be promoted to a theorem about analytic zeta zeros.
--
-- DASHI contribution: exact compiled orientation/phase transport into
-- the ALREADY-owned torque bracket/C3 chart and the pointed-zero firewall.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannSSP15DepthFiveRoleCodecExact as Roles
import DASHI.Analysis.RiemannSSP15FilteredProvenanceCapstoneExact as Capstone
import DASHI.Analysis.RiemannSSP15ProducerMarkedSignedFRACTRANExact as Machine
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Physics.Foundations.OrientedThreeAxisBracket369Exact as Torque
import DASHI.Moonshine.C3FourierConjugationExact as C3
import DASHI.Analysis.PickoverSignedSSPTorquePhaseBridgeExact as Bridge

------------------------------------------------------------------------
-- Same source-marked instruction/pointed-state carrier.
------------------------------------------------------------------------

torqueVoxelOfProducerMarked :
  {certificate : Capstone.PrimitiveRowProducerRoleCertificate} →
  Capstone.ProducerMarkedSSP15Code certificate →
  Torque.BracketVoxel
torqueVoxelOfProducerMarked code =
  Bridge.torqueVoxelFromOrientation
    (Signed.orientation (Machine.producerMarkedHyperformLane code))

------------------------------------------------------------------------
-- Three selected semantic ROLE indices compile to existing C3 phase
-- orientations.  Not an identity between a real sine, a zeta zero,
-- an RH producer coordinate, and a mechanical torque.
------------------------------------------------------------------------

originCompilesToInverseTorquePhase :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) →
  (mode : Nonary.ComplementMode5) →
  Torque.bracketPhase
    (torqueVoxelOfProducerMarked
      (Capstone.canonicalProducerMarkedCode
        certificate mode Roles.originRole))
  ≡ C3.zetaSquared
originCompilesToInverseTorquePhase certificate mode
  rewrite Machine.originRoleHyperformOrientationInverse certificate mode =
  refl

jCompilesToNeutralTorquePhase :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) →
  (mode : Nonary.ComplementMode5) →
  Torque.bracketPhase
    (torqueVoxelOfProducerMarked
      (Capstone.canonicalProducerMarkedCode
        certificate mode Roles.jRole))
  ≡ C3.one
jCompilesToNeutralTorquePhase certificate mode
  rewrite Machine.jRoleHyperformOrientationMediated certificate mode =
  refl

sCompilesToForwardTorquePhase :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) →
  (mode : Nonary.ComplementMode5) →
  Torque.bracketPhase
    (torqueVoxelOfProducerMarked
      (Capstone.canonicalProducerMarkedCode
        certificate mode Roles.sRole))
  ≡ C3.zeta
sCompilesToForwardTorquePhase certificate mode
  rewrite Machine.sRoleHyperformOrientationForward certificate mode =
  refl

torqueReversalConjugatesProducerRolePhase :
  {certificate : Capstone.PrimitiveRowProducerRoleCertificate} →
  (code : Capstone.ProducerMarkedSSP15Code certificate) →
  Torque.bracketPhase
    (Torque.swapBracketInputs (torqueVoxelOfProducerMarked code))
  ≡
  C3.inversePhase
    (Torque.bracketPhase (torqueVoxelOfProducerMarked code))
torqueReversalConjugatesProducerRolePhase code =
  Torque.swapBracketInputsConjugatesPhase
    (torqueVoxelOfProducerMarked code)

-- This is the *existing* source-owner theorem, carried into the weld:
-- all j instruction effects are empty, but the pointed selected SSP lane
-- is retained.  Zero token count does not decode the mode or prime.

jRoleStillExecutesEmptyWeave :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) →
  (mode : Nonary.ComplementMode5) →
  Machine.executeProducerMarked
    (Capstone.canonicalProducerMarkedCode
      certificate mode Roles.jRole)
  ≡ Signed.emptyWeaveEffect
jRoleStillExecutesEmptyWeave =
  Machine.jRoleProgramEffectIsEmpty

------------------------------------------------------------------------
-- Explicit fail-closed frontier: phase table is source-written algebra,
-- NOT a selected physical torque amplitude or an analytic RH producer.
------------------------------------------------------------------------

record RolePhaseBoundary : Set where
  constructor role-phase-boundary
  field
    producerMarkedRoleChartReused : Bool
    signedPrimePointedProvenanceRetained : Bool
    torqueC3ConjugationReused : Bool
    neutralJEffectRetained : Bool
    actualZetaZeroMappedToTorque : Bool
    actualZetaZeroMappedToPickoverPhase : Bool

canonicalRolePhaseBoundary : RolePhaseBoundary
canonicalRolePhaseBoundary =
  role-phase-boundary true true true true false false
