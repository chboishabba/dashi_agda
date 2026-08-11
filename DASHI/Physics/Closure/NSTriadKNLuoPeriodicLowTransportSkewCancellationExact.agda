module DASHI.Physics.Closure.NSTriadKNLuoPeriodicLowTransportSkewCancellationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The leading low-high transport term is skew in the periodic enstrophy
-- pairing.  Componentwise,
--
--   d_j (u_j omega_i^2)
--     = (d_j u_j) omega_i^2
--       + 2 omega_i u_j d_j omega_i.
--
-- This module proves the identity exactly over rational finite coordinates,
-- sums it recursively, and then proves that periodic flux cancellation plus
-- divergence-free low velocity imply
--
--   2 <u_< . grad omega_q, omega_q> = 0.
--
-- Hence F9 should not pay viscosity for the bare resolved low transport.  The
-- genuine lower-lane obligations are the commutator created by filtering,
-- low-frequency stretching, comparable interactions and tails.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; trans)

record TransportCoordinate : Set where
  constructor transportCoordinate
  field
    velocity velocityDerivative : ℚ
    vorticity vorticityDerivative : ℚ

open TransportCoordinate public

fluxDerivative : TransportCoordinate → ℚ
fluxDerivative coordinate =
  velocityDerivative coordinate
    * (vorticity coordinate * vorticity coordinate)
  + velocity coordinate
    * (2 * vorticity coordinate * vorticityDerivative coordinate)

divergenceContribution : TransportCoordinate → ℚ
divergenceContribution coordinate =
  velocityDerivative coordinate
  * (vorticity coordinate * vorticity coordinate)

twiceTransportPairing : TransportCoordinate → ℚ
twiceTransportPairing coordinate =
  2 * vorticity coordinate
    * (velocity coordinate * vorticityDerivative coordinate)

transportFluxProductRule :
  ∀ coordinate →
  fluxDerivative coordinate
  ≡ divergenceContribution coordinate + twiceTransportPairing coordinate
transportFluxProductRule coordinate =
  solve
    ( velocity coordinate
    ∷ velocityDerivative coordinate
    ∷ vorticity coordinate
    ∷ vorticityDerivative coordinate
    ∷ [])

sumFluxDerivative : List TransportCoordinate → ℚ
sumFluxDerivative [] = 0ℚ
sumFluxDerivative (coordinate ∷ coordinates) =
  fluxDerivative coordinate + sumFluxDerivative coordinates

sumDivergenceContribution : List TransportCoordinate → ℚ
sumDivergenceContribution [] = 0ℚ
sumDivergenceContribution (coordinate ∷ coordinates) =
  divergenceContribution coordinate
  + sumDivergenceContribution coordinates

sumTwiceTransportPairing : List TransportCoordinate → ℚ
sumTwiceTransportPairing [] = 0ℚ
sumTwiceTransportPairing (coordinate ∷ coordinates) =
  twiceTransportPairing coordinate
  + sumTwiceTransportPairing coordinates

finiteTransportFluxProductRule :
  ∀ coordinates →
  sumFluxDerivative coordinates
  ≡ sumDivergenceContribution coordinates
    + sumTwiceTransportPairing coordinates
finiteTransportFluxProductRule [] = solve []
finiteTransportFluxProductRule (coordinate ∷ coordinates)
  rewrite transportFluxProductRule coordinate
        | finiteTransportFluxProductRule coordinates =
  solve
    ( divergenceContribution coordinate
    ∷ twiceTransportPairing coordinate
    ∷ sumDivergenceContribution coordinates
    ∷ sumTwiceTransportPairing coordinates
    ∷ [])

record PeriodicDivergenceFreeTransport : Set where
  constructor periodicDivergenceFreeTransport
  field
    coordinates : List TransportCoordinate
    periodicFluxIntegralVanishes : sumFluxDerivative coordinates ≡ 0ℚ
    divergenceIntegralVanishes :
      sumDivergenceContribution coordinates ≡ 0ℚ

open PeriodicDivergenceFreeTransport public

periodicLowTransportSkewCancellation :
  ∀ dataSet → sumTwiceTransportPairing (coordinates dataSet) ≡ 0ℚ
periodicLowTransportSkewCancellation dataSet =
  let
    divergence = sumDivergenceContribution (coordinates dataSet)
    transport = sumTwiceTransportPairing (coordinates dataSet)

    zeroToSplit : 0ℚ ≡ divergence + transport
    zeroToSplit =
      trans
        (sym (periodicFluxIntegralVanishes dataSet))
        (finiteTransportFluxProductRule (coordinates dataSet))

    splitToZeroPlusTransport : divergence + transport ≡ 0ℚ + transport
    splitToZeroPlusTransport =
      cong (λ value → value + transport)
        (divergenceIntegralVanishes dataSet)

    zeroPlusTransportToTransport : 0ℚ + transport ≡ transport
    zeroPlusTransportToTransport = solve (transport ∷ [])

    zeroToTransport : 0ℚ ≡ transport
    zeroToTransport =
      trans zeroToSplit
        (trans splitToZeroPlusTransport zeroPlusTransportToTransport)
  in
  sym zeroToTransport

record LowTransportAuthorityBoundary : Set where
  constructor lowTransportAuthorityBoundary
  field
    pointwiseFluxProductRuleProved : Set
    finiteCoordinateSummationProved : Set
    periodicDivergenceFreeCancellationProved : Set
    filteredTransportCommutatorEstimated : Set
    lowStretchingCriticalTaxProved : Set

canonicalLowTransportAuthorityBoundary : LowTransportAuthorityBoundary
canonicalLowTransportAuthorityBoundary =
  lowTransportAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
