module DASHI.Physics.Closure.NSTriadKNFluxHierarchyEstimate where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNDissipationNormalizedFluxRemainder as Flux
import DASHI.Physics.Closure.NSTriadKNLocalViscousEdgeAllocation as Allocation
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- The scaling-consistent NS gate.
--
-- For d_e quadratic in u, the extended quotient is quartic in amplitude.
-- It may therefore be bounded by X(u) D_z(u), not by D_z(u) alone.  This
-- record is the precise point at which a small-data, depletion, integrability
-- or barrier theorem must enter.  It is intentionally not an old Schur or
-- q-gap receipt.
------------------------------------------------------------------------

record FluxHierarchyEstimate
    (S : Scalar.ExactOrderedScalar)
    (M : Nat) (z : Energy.AdmissibleFourierMultiplier S M)
    (triads : List Energy.ZeroSumTriad)
    (allocation : Allocation.LocalViscousEdgeAllocation S M z triads) : Set₁ where
  field
    hierarchyEnergy : Scalar.Scalar S
    tailRemainder : Scalar.Scalar S
    viscosity : Scalar.Scalar S
    epsilon : Scalar.Scalar S
    hierarchyConstant : Scalar.Scalar S
    fluxRemainder : Flux.ExtendedFlux S

    -- Intended finite-cutoff theorem:
    -- FluxRem_epsilon <= C/(epsilon*nu) X D_z + TailRem.
    -- The concrete inequality is withheld until an extended nonnegative
    -- scalar/order authority and a physical estimate for transfer differences
    -- are available.
    hierarchyBound : Set

open FluxHierarchyEstimate public

-- A global conclusion requires an independent dynamical mechanism for X:
-- small critical data, scale-local depletion, time integrability, or a
-- barrier.  The finite algebra developed so far supplies none of these.
fluxHierarchyEstimateClosed : Bool
fluxHierarchyEstimateClosed = false
