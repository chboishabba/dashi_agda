module DASHI.Physics.Textile.FiniteTextileEquilibriumNetworkExact where

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.QuasiStaticTextileLoadTransferExact as Local
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Finite coupled equilibrium network.
--
-- This module lifts the local signed-force balance into one finite network in
-- which every edge contributes to two endpoints and every vertex satisfies a
-- simultaneous equilibrium equation.  The scalar carrier remains abstract;
-- producers must supply an additive inverse compatible with the local algebra.
------------------------------------------------------------------------

record OrientedMechanicalAlgebra (Scalar : Set) : Set₁ where
  constructor oriented-mechanical-algebra
  field
    localAlgebra : Local.ScalarMechanicalAlgebra Scalar
    negate : Scalar → Scalar
    additiveInverse :
      (x : Scalar) →
      Local.add localAlgebra x (negate x)
      ≡ Local.zero localAlgebra

open OrientedMechanicalAlgebra public

sumFin :
  {Scalar : Set} →
  (algebra : Local.ScalarMechanicalAlgebra Scalar) →
  (n : Nat) →
  (Fin n → Scalar) →
  Scalar
sumFin algebra zero values = Local.zero algebra
sumFin algebra (suc n) values =
  Local.add algebra
    (values zero)
    (sumFin algebra n (λ i → values (suc i)))

record FiniteTextileEquilibriumNetwork
    {Scalar : Set}
    (algebra : OrientedMechanicalAlgebra Scalar)
    (vertexCount edgeCount : Nat) : Set₁ where
  constructor finite-textile-equilibrium-network
  field
    source : Fin edgeCount → Fin vertexCount
    target : Fin edgeCount → Fin vertexCount

    edgeForce : Fin edgeCount → Local.Force Scalar
    externalForce : Fin vertexCount → Local.Force Scalar

    signedContribution :
      Fin vertexCount → Fin edgeCount → Scalar

    sourceContribution :
      (edge : Fin edgeCount) →
      signedContribution (source edge) edge
      ≡ Dim.magnitude (edgeForce edge)

    targetContribution :
      (edge : Fin edgeCount) →
      signedContribution (target edge) edge
      ≡ negate algebra (Dim.magnitude (edgeForce edge))

    nonEndpointContributionIsZero :
      (vertex : Fin vertexCount) →
      (edge : Fin edgeCount) →
      (vertex ≡ source edge → ⊥) →
      (vertex ≡ target edge → ⊥) →
      signedContribution vertex edge
      ≡ Local.zero (localAlgebra algebra)

    equilibriumAt :
      (vertex : Fin vertexCount) →
      Local.add (localAlgebra algebra)
        (sumFin (localAlgebra algebra) edgeCount
          (signedContribution vertex))
        (Dim.magnitude (externalForce vertex))
      ≡ Local.zero (localAlgebra algebra)

open FiniteTextileEquilibriumNetwork public

edgeActionReaction :
  {Scalar : Set}
  {vertexCount edgeCount : Nat}
  (algebra : OrientedMechanicalAlgebra Scalar) →
  (network : FiniteTextileEquilibriumNetwork algebra vertexCount edgeCount) →
  (edge : Fin edgeCount) →
  Local.add (localAlgebra algebra)
    (signedContribution network (source network edge) edge)
    (signedContribution network (target network edge) edge)
  ≡ Local.zero (localAlgebra algebra)
edgeActionReaction algebra network edge
  rewrite sourceContribution network edge
        | targetContribution network edge =
  additiveInverse algebra (Dim.magnitude (edgeForce network edge))

------------------------------------------------------------------------
-- Same-object bridge back to the stitch hyperfabric.
--
-- Network vertices are explicitly assigned to loop/anchor sites.  Coverage is
-- proof-bearing for every loop and anchor stored by the stitch state, and also
-- for every currently live frontier loop.  This is therefore stronger than an
-- unrelated equilibrium graph sitting beside the textile topology.
------------------------------------------------------------------------

data MechanicalSite : Set where
  loopSite : Stitch.LoopId → MechanicalSite
  anchorSite : Stitch.AnchorId → MechanicalSite

record WholeStitchEquilibriumReceipt
    {Scalar : Set}
    (algebra : OrientedMechanicalAlgebra Scalar)
    (vertexCount edgeCount : Nat)
    (topology : Stitch.StitchState) : Set₁ where
  constructor whole-stitch-equilibrium-receipt
  field
    network :
      FiniteTextileEquilibriumNetwork algebra vertexCount edgeCount

    siteAtVertex : Fin vertexCount → MechanicalSite

    everyStoredLoopCovered :
      (loop : Stitch.LoopId) →
      loop ∈ Stitch.loops topology →
      Σ (Fin vertexCount) (λ vertex → siteAtVertex vertex ≡ loopSite loop)

    everyAnchorCovered :
      (anchor : Stitch.AnchorId) →
      anchor ∈ Stitch.anchors topology →
      Σ (Fin vertexCount) (λ vertex → siteAtVertex vertex ≡ anchorSite anchor)

    everyLiveLoopCovered :
      (loop : Stitch.LoopId) →
      loop ∈ Stitch.liveLoops (Stitch.frontier topology) →
      Σ (Fin vertexCount) (λ vertex → siteAtVertex vertex ≡ loopSite loop)

open WholeStitchEquilibriumReceipt public

------------------------------------------------------------------------
-- Boundary: a proof-bearing equilibrium receipt certifies one supplied finite
-- solution.  It is not yet a constructive numerical solver, and 1-D signed
-- edge forces are not full rod/shell mechanics.
------------------------------------------------------------------------

data EquilibriumReceiptIsConstructiveNetworkSolver : Set where

equilibriumReceiptIsNotConstructiveNetworkSolver :
  EquilibriumReceiptIsConstructiveNetworkSolver → ⊥
equilibriumReceiptIsNotConstructiveNetworkSolver ()

data FiniteAxialNetworkIsFullRodShellTextileMechanics : Set where

finiteAxialNetworkIsNotFullRodShellTextileMechanics :
  FiniteAxialNetworkIsFullRodShellTextileMechanics → ⊥
finiteAxialNetworkIsNotFullRodShellTextileMechanics ()
