module DASHI.Crypto.MLKEMCandidateMoveFanoutExact where

------------------------------------------------------------------------
-- CANDIDATE-MOVE FANOUT ACROSS FIPS-203 REPRESENTATIONS
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Round 17's dataflow theorem is directional: one scalar NTT component depends
-- on all 128 source coefficients of its parity class.  Equivalently for search
-- geometry, changing one source coefficient is potentially visible in all 128
-- scalar NTT coordinates of that parity class.  BaseCaseMultiply then lets one
-- local secret component feed both public output components in each residue.
-- Across k public rows, the structural public-residual fanout is therefore
-- 2*128*k = 256*k scalar coordinates.
--
-- "Potentially affected" is deliberately not "numerically changed": concrete
-- matrix coefficients may cancel or vanish.  The theorem is a dataflow/update
-- geometry bound, not a cryptographic work-factor claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS
import DASHI.Crypto.MLKEMNTTDataflowCouplingExact as NTT

secretNTTScalarFanoutPerSourceCoefficient : Nat
secretNTTScalarFanoutPerSourceCoefficient = NTT.sourceCoefficientsPerScalarNTTCoordinate

secretNTTScalarFanoutIs128 : secretNTTScalarFanoutPerSourceCoefficient ≡ 128
secretNTTScalarFanoutIs128 = refl

publicResidualScalarFanout : FIPS.MLKEMParameters → Nat
publicResidualScalarFanout p =
  2 * secretNTTScalarFanoutPerSourceCoefficient * FIPS.k p

mlKem512PublicResidualMoveFanout :
  publicResidualScalarFanout FIPS.params512 ≡ 512
mlKem512PublicResidualMoveFanout = refl

mlKem768PublicResidualMoveFanout :
  publicResidualScalarFanout FIPS.params768 ≡ 768
mlKem768PublicResidualMoveFanout = refl

mlKem1024PublicResidualMoveFanout :
  publicResidualScalarFanout FIPS.params1024 ≡ 1024
mlKem1024PublicResidualMoveFanout = refl

------------------------------------------------------------------------
-- Representation-geometry tradeoff.
------------------------------------------------------------------------

record CandidateMoveGeometry : Set where
  constructor candidateMoveGeometry
  field
    sourceCoordinateChanges : Nat
    secretRepresentationPotentialFanout : Nat
    publicResidualPotentialFanout : Nat

open CandidateMoveGeometry public

moveGeometry : FIPS.MLKEMParameters → CandidateMoveGeometry
moveGeometry p =
  candidateMoveGeometry
    1
    secretNTTScalarFanoutPerSourceCoefficient
    (publicResidualScalarFanout p)

mlKem512OneCoefficientMoveGeometry :
  publicResidualPotentialFanout (moveGeometry FIPS.params512) ≡ 512
mlKem512OneCoefficientMoveGeometry = refl

------------------------------------------------------------------------
-- Boundary: locality depends on what is regarded as a primitive search move.
-- A coefficient-local move is broad in NTT/public residual space; an NTT-local
-- move is not automatically prior-local because the CBD prior originated in
-- coefficient space.
------------------------------------------------------------------------

record CandidateMoveBoundary : Set where
  constructor candidateMoveBoundary
  field
    coefficientLocalMeansNTTLocal : Bool
    coefficientLocalMeansNTTLocalIsFalse : coefficientLocalMeansNTTLocal ≡ false
    nttLocalMeansCBDPriorLocal : Bool
    nttLocalMeansCBDPriorLocalIsFalse : nttLocalMeansCBDPriorLocal ≡ false
    structuralFanoutEqualsActualRuntimeWork : Bool
    structuralFanoutEqualsActualRuntimeWorkIsFalse :
      structuralFanoutEqualsActualRuntimeWork ≡ false

open CandidateMoveBoundary public

canonicalCandidateMoveBoundary : CandidateMoveBoundary
canonicalCandidateMoveBoundary =
  candidateMoveBoundary false refl false refl false refl
