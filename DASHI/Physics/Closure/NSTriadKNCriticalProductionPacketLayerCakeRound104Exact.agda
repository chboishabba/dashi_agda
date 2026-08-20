module DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Author: Gregory L. Eyink.
-- Title: "Locality of turbulent cascades".
-- Physica D 207 (2005), 91--116.
-- DOI: 10.1016/j.physd.2005.05.018.
--
-- Authors: Gregory L. Eyink; Hussein Aluie.
-- Title: "Localness of energy cascade in hydrodynamic turbulence. I.
-- Smooth coarse graining".
-- Physics of Fluids 21 (2009), 115107.
-- DOI: 10.1063/1.3266883.
--
-- ROUND104 / RADIAL ABEL LAYER-CAKE
--
-- Round103 wrote the three-radius derivative-weighted transfer as an edge
-- gradient pairing.  Round96/98 independently proved a more physical fact:
-- the literal selected projected Galerkin pairing is exactly a normalized
-- packet-boundary flux, because fully internal triads cancel before
-- majorisation.
--
-- This file supplies the missing finite algebra joining those viewpoints for
-- an ARBITRARY number of ordered radial bands.  For band weights lambda_i and
-- signed nonlinear transfers q_i, let
--
--   Q_j = sum_{i>=j} q_i
--
-- be the suffix/upper-packet transfer.  Then exact Abel summation gives
--
--   sum_i lambda_i q_i
--     = lambda_0 sum_i q_i
--       + sum_{j>=1} (lambda_j-lambda_{j-1}) Q_j.
--
-- Navier--Stokes nonlinear energy transfer is conservative, so sum_i q_i=0
-- and therefore
--
--   CRITICAL PRODUCTION
--     = sum_{j>=1} radialIncrement_j * upperPacketFlux_j.
--
-- This is strictly more flexible than a pointwise Leith mobility: individual
-- packet fluxes may have either sign.  A Clay proof only needs their complete
-- weighted sum to be subordinate to viscosity plus an integrable remainder.
-- Round98 already owns the same-object theorem identifying each selected PDE
-- pairing with normalized physical boundary flux; the remaining physical seam
-- is the literal radial-band/suffix-selector realization and its quantitative
-- weighted-flux estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact as Packet

sub : ℚ → ℚ → ℚ
sub x y = x + (- y)

BandTransfer : Set
BandTransfer = ℚ × ℚ

weight transfer : BandTransfer → ℚ
weight = proj₁
transfer = proj₂

totalTransfer : List BandTransfer → ℚ
totalTransfer [] = 0ℚ
totalTransfer (b ∷ rest) = transfer b + totalTransfer rest

weightedTransfer : List BandTransfer → ℚ
weightedTransfer [] = 0ℚ
weightedTransfer (b ∷ rest) =
  weight b * transfer b + weightedTransfer rest

baseWeight : List BandTransfer → ℚ
baseWeight [] = 0ℚ
baseWeight (b ∷ rest) = weight b

-- The layer-cake consists of every adjacent radial increment multiplied by the
-- transfer of the entire suffix packet above that interface.
radialLayerCake : List BandTransfer → ℚ
radialLayerCake [] = 0ℚ
radialLayerCake (b ∷ []) = 0ℚ
radialLayerCake (b0 ∷ b1 ∷ rest) =
  sub (weight b1) (weight b0) * totalTransfer (b1 ∷ rest)
  + radialLayerCake (b1 ∷ rest)

-- Exact finite Abel identity, with no monotonicity or sign hypothesis.
weightedTransferAbelIdentity :
  (bands : List BandTransfer) →
  weightedTransfer bands
  ≡ baseWeight bands * totalTransfer bands + radialLayerCake bands
weightedTransferAbelIdentity [] = refl
weightedTransferAbelIdentity (b ∷ []) =
  solve (weight b ∷ transfer b ∷ [])
weightedTransferAbelIdentity (b0 ∷ b1 ∷ rest) =
  let
    tail = b1 ∷ rest
    tailIdentity = weightedTransferAbelIdentity tail
    exposeTail :
      weight b0 * transfer b0 + weightedTransfer tail
      ≡
      weight b0 * transfer b0
      + (baseWeight tail * totalTransfer tail + radialLayerCake tail)
    exposeTail = cong (weight b0 * transfer b0 +_) tailIdentity

    endpoint :
      weight b0 * transfer b0
      + (baseWeight tail * totalTransfer tail + radialLayerCake tail)
      ≡
      weight b0 * (transfer b0 + totalTransfer tail)
      + (sub (weight b1) (weight b0) * totalTransfer tail
        + radialLayerCake tail)
    endpoint =
      solve
        ( weight b0 ∷ transfer b0 ∷ weight b1
        ∷ totalTransfer tail ∷ radialLayerCake tail ∷ [])
  in
  trans exposeTail endpoint

conservativeWeightedTransferIsLayerCake :
  (bands : List BandTransfer) →
  totalTransfer bands ≡ 0ℚ →
  weightedTransfer bands ≡ radialLayerCake bands
conservativeWeightedTransferIsLayerCake bands conservation =
  trans
    (weightedTransferAbelIdentity bands)
    (cong
      (λ total → baseWeight bands * total + radialLayerCake bands)
      conservation)

------------------------------------------------------------------------
-- Explicit four-band expansion: useful as a regression against accidental
-- prefix/suffix orientation reversal.
------------------------------------------------------------------------

fourBandLayerCakeExpansion :
  (l0 l1 l2 l3 q0 q1 q2 q3 : ℚ) →
  radialLayerCake
    ((l0 , q0) ∷ (l1 , q1) ∷ (l2 , q2) ∷ (l3 , q3) ∷ [])
  ≡
    sub l1 l0 * (q1 + q2 + q3)
    + sub l2 l1 * (q2 + q3)
    + sub l3 l2 * q3
fourBandLayerCakeExpansion l0 l1 l2 l3 q0 q1 q2 q3 =
  solve (l0 ∷ l1 ∷ l2 ∷ l3 ∷ q0 ∷ q1 ∷ q2 ∷ q3 ∷ [])

round104FiniteRadialAbelLayerCakeClosed : Bool
round104FiniteRadialAbelLayerCakeClosed = true

round104ConservativeCriticalProductionIsPacketFluxLayerCake : Bool
round104ConservativeCriticalProductionIsPacketFluxLayerCake = true

round104LiteralSelectedProjectedPairingBoundaryFluxReused : Bool
round104LiteralSelectedProjectedPairingBoundaryFluxReused =
  Packet.round98SelectedWeightedOutputFiberIdentificationClosed

-- Physical next theorem: build the radial band list/suffix selectors from the
-- actual finite Galerkin Fourier support and show the resulting layer-cake
-- weighted boundary flux satisfies the uniform signed-production estimate.
round104PhysicalRadialBandLayerCakeEstimateClosed : Bool
round104PhysicalRadialBandLayerCakeEstimateClosed = false

round104FiniteRadialAbelLayerCakeClosedIsTrue :
  round104FiniteRadialAbelLayerCakeClosed ≡ true
round104FiniteRadialAbelLayerCakeClosedIsTrue = refl

round104PhysicalRadialBandLayerCakeEstimateClosedIsFalse :
  round104PhysicalRadialBandLayerCakeEstimateClosed ≡ false
round104PhysicalRadialBandLayerCakeEstimateClosedIsFalse = refl