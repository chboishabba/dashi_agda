module DASHI.Physics.QuantumVacuum.CasimirU1InvariantPairingRestrictionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.List.Base using ([]; _∷_)

import Tactic.RingSolver as Solver

open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_*R_; realSolverRing)
import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct as Inner
import DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact as U1

------------------------------------------------------------------------
-- CARTAN U(1) RESTRICTION OF THE LIVE SU(2) INVARIANT PAIRING
--
-- The canonical electromagnetic embedding is
--
--   a |-> (0,0,a) in su(2).
--
-- The repository's actual Ad-invariant su(2) pairing is the Euclidean dot
-- product on those three imaginary-quaternion coordinates.  Hence its
-- restriction to the Cartan U(1) axis is literally ordinary multiplication.
-- This is an algebraic normalization theorem.  It does not choose a physical
-- gauge coupling, electric charge unit, SI normalization, or Maxwell action
-- prefactor.
------------------------------------------------------------------------

u1EmbeddedInvariantPairing :
  ∀ a b →
  Inner.su2Dot (U1.embedU1Lie a) (U1.embedU1Lie b)
  ≡ a *R b
u1EmbeddedInvariantPairing a b =
  Solver.solve (a ∷ b ∷ []) realSolverRing

u1EmbeddedInvariantNormSquare :
  ∀ a →
  Inner.su2Dot (U1.embedU1Lie a) (U1.embedU1Lie a)
  ≡ a *R a
u1EmbeddedInvariantNormSquare a =
  u1EmbeddedInvariantPairing a a

u1PairingIsInheritedFromAdInvariantSU2Pairing : Bool
u1PairingIsInheritedFromAdInvariantSU2Pairing = true

record CasimirU1InvariantPairingBoundary : Set where
  constructor casimir-u1-invariant-pairing-boundary
  field
    su2InvariantPairingReused : Bool
    cartesianU1PairingRestrictionPaid : Bool
    independentKillingDecompositionRequired : Bool
    physicalChargeCouplingNormalizationPaid : Bool

open CasimirU1InvariantPairingBoundary public

canonicalCasimirU1InvariantPairingBoundary : CasimirU1InvariantPairingBoundary
canonicalCasimirU1InvariantPairingBoundary =
  casimir-u1-invariant-pairing-boundary true true false false

data RemainingCasimirU1NormalizationBlocker : Set where
  missingPhysicalChargeCouplingNormalization : RemainingCasimirU1NormalizationBlocker

firstNormalizationBlocker : RemainingCasimirU1NormalizationBlocker
firstNormalizationBlocker = missingPhysicalChargeCouplingNormalization

data CartanPairingRestrictionAutomaticallyFixesPhysicalChargeNormalization : Set where

cartanPairingDoesNotFixPhysicalChargeNormalization :
  CartanPairingRestrictionAutomaticallyFixesPhysicalChargeNormalization → ⊥
cartanPairingDoesNotFixPhysicalChargeNormalization ()

casimirU1InvariantPairingReading : String
casimirU1InvariantPairingReading =
  "The live Ad-invariant SU(2) inner product restricts exactly along the canonical electromagnetic Cartan embedding: <embed a, embed b> = a*b. Therefore a separate algebraic Killing/trace-pairing decomposition is not an independent Casimir payment on this axis. The remaining normalization leaf is physical: choose and same-object-weld the Maxwell/electric-charge/gauge-coupling convention and action prefactor."
