module DASHI.Physics.Closure.NSTriadKNComOutputFibreOrthogonalityRound52Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Correct the tempting incidence-orthogonality shortcut.  Fourier Plancherel
-- separates distinct OUTPUT modes, but many resonant pairs p+r=k may share the
-- same k and can interfere coherently.  Hence the physical lifting problem is
-- fibrewise over
--
--   pi_out(tau) = k(tau).
--
-- Orthogonality removes cross-fibre interference exactly; no theorem here
-- assumes orthogonality inside one output fibre.  The preferred remaining PDE
-- theorem is therefore a WHOLE shell-block norm bound, or failing that a
-- same-output-fibre collision estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad

outputMode : Triad.PhysicalTriadIncidence → Z3.FourierMode
outputMode = Triad.k

SameOutputFibre :
  Triad.PhysicalTriadIncidence → Triad.PhysicalTriadIncidence → Set
SameOutputFibre left right = outputMode left ≡ outputMode right

DifferentOutputFibre :
  Triad.PhysicalTriadIncidence → Triad.PhysicalTriadIncidence → Set
DifferentOutputFibre left right = SameOutputFibre left right → ⊥

record OutputModeOrthogonalIncidencePairing : Set₁ where
  field
    PairingValue :
      Triad.PhysicalTriadIncidence → Triad.PhysicalTriadIncidence → Set

    distinctOutputsAnnihilatePairing : ∀ left right →
      DifferentOutputFibre left right →
      PairingValue left right → ⊥

open OutputModeOrthogonalIncidencePairing public

survivingPairingCannotHaveDistinctOutputs :
  (pairing : OutputModeOrthogonalIncidencePairing) →
  ∀ left right →
  PairingValue pairing left right →
  DifferentOutputFibre left right → ⊥
survivingPairingCannotHaveDistinctOutputs pairing left right survives distinct =
  distinctOutputsAnnihilatePairing pairing left right distinct survives

record SameOutputCollisionProblem : Set₁ where
  field
    left right : Triad.PhysicalTriadIncidence
    sameOutput : SameOutputFibre left right

open SameOutputCollisionProblem public

-- A same-output collision is not forced to be the same incidence.  Its two
-- input pairs remain explicit proof-relevant data, so no cardinality-one or
-- per-incidence orthogonality claim can be smuggled into the shell estimate.
record FibrewiseComLiftingTarget : Set₁ where
  field
    WholeShellBlockBound : Set
    wholeShellBlockBound : WholeShellBlockBound

    CrossOutputPlancherel : Set
    crossOutputPlancherel : CrossOutputPlancherel

    SameOutputFibreEstimate : Set
    sameOutputFibreEstimate : SameOutputFibreEstimate

open FibrewiseComLiftingTarget public

plancherelOnlyRemovesCrossOutputMultiplicity : Bool
plancherelOnlyRemovesCrossOutputMultiplicity = true

sameOutputTriadCollisionsRemainAnalytic : Bool
sameOutputTriadCollisionsRemainAnalytic = true

wholeShellBlockNormIsPreferredComTarget : Bool
wholeShellBlockNormIsPreferredComTarget = true

plancherelOnlyRemovesCrossOutputMultiplicityIsTrue :
  plancherelOnlyRemovesCrossOutputMultiplicity ≡ true
plancherelOnlyRemovesCrossOutputMultiplicityIsTrue = refl
