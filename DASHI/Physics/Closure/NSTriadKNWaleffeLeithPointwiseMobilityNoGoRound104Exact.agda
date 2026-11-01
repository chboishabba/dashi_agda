module DASHI.Physics.Closure.NSTriadKNWaleffeLeithPointwiseMobilityNoGoRound104Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Author: C. E. Leith.
-- Title: "Diffusion Approximation to Inertial Energy Transfer in Isotropic
-- Turbulence".
-- The Physics of Fluids 10(7) (1967), 1409--1416.
-- DOI: 10.1063/1.1762300.
--
-- Authors: T. T. Clark; R. Rubinstein; J. Weinstock.
-- Title: "Reassessment of the classical turbulence closures: the Leith
-- diffusion model".
-- Journal of Turbulence 10 (2009), article N35.
-- DOI: 10.1080/14685240903154172.
--
-- SOURCE ROLE BOUNDARY
--
-- Leith's diffusion model is cited as the historical spectral-diffusion
-- analogy only.  It is not used as an exact Navier--Stokes theorem.  Clark,
-- Rubinstein and Weinstock explicitly describe the Leith diffusion model as
-- representing a subset of nonlinear interactions.  The exact finite no-go
-- below is a DASHI theorem derived from the repository's Waleffe cell algebra
-- plus the Round103 graph-Dirichlet identity.
--
-- ROUND104 / POINTWISE LEITH MOBILITY NO-GO
--
-- Round102 gives the exact heterochiral critical-production formula on one
-- Waleffe cell.  Round103 proves that any three-edge radial flux of the form
--
--   Jij = mij (lambda_j-lambda_i),   mij >= 0,
--
-- has nonpositive derivative-weighted transfer.
--
-- This file connects those two statements without an intermediate receipt.
-- Any Waleffe cell is converted to a conservative radial edge flux whose node
-- transfers are exactly the three Waleffe transfers.  Hence its radial
-- weighted transfer is exactly its H^(1/2) critical production.
--
-- The concrete 3-4-5 radial geometry with k the minority-helicity leg has
--
--   rk = 5, rp = 3, rq = 4, A = 1,
--   (lambda_k,lambda_p,lambda_q) = (-5,3,4),
--
-- and exact critical production +10.  Flipping only the common amplitude in
-- the algebraic cell gives -10 at the SAME radii and helicity signs.  Therefore
-- radius/helicity geometry alone cannot assign a universal dissipative sign.
--
-- More strongly, no all-nonnegative three-edge gradient mobility can have the
-- same weighted transfer as the +10 cell: Round103 makes every such gradient
-- transfer <= 0, while the Waleffe transfer is exactly +10.
--
-- Consequently the Clay frontier must not be phrased as a pointwise theorem
-- "literal Waleffe transfer has nonnegative Leith mobility".  Any successful
-- coercivity theorem has to be aggregate/network-level, preserving signed
-- phase correlations across the complete Galerkin interaction graph before
-- majorisation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNHeterochiralMinorityLegReductionRound102Exact as W
import DASHI.Physics.Closure.NSTriadKNRadialFluxIntegrationByPartsRound103Exact as Radial

zero one three four five ten : ℚ
zero = Int.+ 0 / 1
one = Int.+ 1 / 1
three = Int.+ 3 / 1
four = Int.+ 4 / 1
five = Int.+ 5 / 1
ten = Int.+ 10 / 1

------------------------------------------------------------------------
-- Exact bridge from one Waleffe cell to the Round103 radial-flux carrier.
------------------------------------------------------------------------

waleffeTransfersConserve :
  (lambdaK lambdaP lambdaQ A : ℚ) →
  W.transferK lambdaK lambdaP lambdaQ A
  + W.transferP lambdaK lambdaP lambdaQ A
  + W.transferQ lambdaK lambdaP lambdaQ A
  ≡ 0ℚ
waleffeTransfersConserve lambdaK lambdaP lambdaQ A =
  solve (lambdaK ∷ lambdaP ∷ lambdaQ ∷ A ∷ [])

waleffeRadialFlux :
  W.WaleffeCriticalCell →
  ℚ → ℚ → ℚ →
  Radial.ThreeEdgeRadialFlux
waleffeRadialFlux C lambdaK lambdaP lambdaQ =
  Radial.three-edge-radial-flux
    (W.radiusK C)
    (W.radiusP C)
    (W.radiusQ C)
    (W.transferK lambdaK lambdaP lambdaQ (W.amplitude C))
    0ℚ
    (- W.transferQ lambdaK lambdaP lambdaQ (W.amplitude C))

waleffeRadialTransfer1IsK :
  (C : W.WaleffeCriticalCell)
  (lambdaK lambdaP lambdaQ : ℚ) →
  Radial.transfer1 (waleffeRadialFlux C lambdaK lambdaP lambdaQ)
  ≡ W.transferK lambdaK lambdaP lambdaQ (W.amplitude C)
waleffeRadialTransfer1IsK C lambdaK lambdaP lambdaQ =
  solve
    (lambdaK ∷ lambdaP ∷ lambdaQ ∷ W.amplitude C ∷ [])

waleffeRadialTransfer2IsP :
  (C : W.WaleffeCriticalCell)
  (lambdaK lambdaP lambdaQ : ℚ) →
  Radial.transfer2 (waleffeRadialFlux C lambdaK lambdaP lambdaQ)
  ≡ W.transferP lambdaK lambdaP lambdaQ (W.amplitude C)
waleffeRadialTransfer2IsP C lambdaK lambdaP lambdaQ =
  solve
    (lambdaK ∷ lambdaP ∷ lambdaQ ∷ W.amplitude C ∷ [])

waleffeRadialTransfer3IsQ :
  (C : W.WaleffeCriticalCell)
  (lambdaK lambdaP lambdaQ : ℚ) →
  Radial.transfer3 (waleffeRadialFlux C lambdaK lambdaP lambdaQ)
  ≡ W.transferQ lambdaK lambdaP lambdaQ (W.amplitude C)
waleffeRadialTransfer3IsQ C lambdaK lambdaP lambdaQ =
  solve
    (lambdaK ∷ lambdaP ∷ lambdaQ ∷ W.amplitude C ∷ [])

waleffeRadialFluxMatchesCriticalProduction :
  (C : W.WaleffeCriticalCell)
  (lambdaK lambdaP lambdaQ : ℚ) →
  Radial.weightedTransfer (waleffeRadialFlux C lambdaK lambdaP lambdaQ)
  ≡ W.criticalProduction C lambdaK lambdaP lambdaQ
waleffeRadialFluxMatchesCriticalProduction C lambdaK lambdaP lambdaQ =
  solve
    ( W.radiusK C ∷ W.radiusP C ∷ W.radiusQ C
    ∷ W.amplitude C ∷ lambdaK ∷ lambdaP ∷ lambdaQ ∷ [])

------------------------------------------------------------------------
-- Phase/amplitude reversal at fixed radii and fixed helicity signs.
------------------------------------------------------------------------

flipAmplitude : W.WaleffeCriticalCell → W.WaleffeCriticalCell
flipAmplitude C =
  W.waleffe-critical-cell
    (W.radiusK C)
    (W.radiusP C)
    (W.radiusQ C)
    (- W.amplitude C)

criticalProductionAmplitudeFlip :
  (C : W.WaleffeCriticalCell)
  (lambdaK lambdaP lambdaQ : ℚ) →
  W.criticalProduction (flipAmplitude C) lambdaK lambdaP lambdaQ
  ≡ - W.criticalProduction C lambdaK lambdaP lambdaQ
criticalProductionAmplitudeFlip C lambdaK lambdaP lambdaQ =
  solve
    ( W.radiusK C ∷ W.radiusP C ∷ W.radiusQ C
    ∷ W.amplitude C ∷ lambdaK ∷ lambdaP ∷ lambdaQ ∷ [])

------------------------------------------------------------------------
-- Exact 3-4-5 heterochiral witness.
--
-- These radii are not an arbitrary impossible triangle: they are the familiar
-- Pythagorean integer geometry |(3,0,0)|=3, |(0,4,0)|=4,
-- |(3,4,0)|=5 with p+q=k.  This module only needs the already-established
-- scalar Waleffe normal form, so the lattice incidence itself is not rebuilt.
------------------------------------------------------------------------

threeFourFivePositiveCell : W.WaleffeCriticalCell
threeFourFivePositiveCell = W.waleffe-critical-cell five three four one

threeFourFiveNegativeCell : W.WaleffeCriticalCell
threeFourFiveNegativeCell = flipAmplitude threeFourFivePositiveCell

threeFourFiveMinorityKPositiveProduction :
  W.criticalProduction
    threeFourFivePositiveCell
    (- five) three four
  ≡ ten
threeFourFiveMinorityKPositiveProduction = solve []

threeFourFiveMinorityKNegativeProduction :
  W.criticalProduction
    threeFourFiveNegativeCell
    (- five) three four
  ≡ - ten
threeFourFiveMinorityKNegativeProduction = solve []

threeFourFivePositiveRadialFlux : Radial.ThreeEdgeRadialFlux
threeFourFivePositiveRadialFlux =
  waleffeRadialFlux threeFourFivePositiveCell (- five) three four

threeFourFiveNegativeRadialFlux : Radial.ThreeEdgeRadialFlux
threeFourFiveNegativeRadialFlux =
  waleffeRadialFlux threeFourFiveNegativeCell (- five) three four

threeFourFivePositiveRadialWeightedTransfer :
  Radial.weightedTransfer threeFourFivePositiveRadialFlux ≡ ten
threeFourFivePositiveRadialWeightedTransfer =
  trans
    (waleffeRadialFluxMatchesCriticalProduction
      threeFourFivePositiveCell (- five) three four)
    threeFourFiveMinorityKPositiveProduction

threeFourFiveNegativeRadialWeightedTransfer :
  Radial.weightedTransfer threeFourFiveNegativeRadialFlux ≡ - ten
threeFourFiveNegativeRadialWeightedTransfer =
  trans
    (waleffeRadialFluxMatchesCriticalProduction
      threeFourFiveNegativeCell (- five) three four)
    threeFourFiveMinorityKNegativeProduction

zeroLessTen : 0ℚ < ten
zeroLessTen = ℚP.positive⁻¹ ten

------------------------------------------------------------------------
-- Pointwise all-nonnegative Leith/graph-Laplacian representation is refuted.
------------------------------------------------------------------------

nonnegativeGradientMobilityCannotMatchPositiveWaleffeWitness :
  (M : Radial.ThreeEdgeGradientMobility) →
  0ℚ ≤ Radial.mobility12 M →
  0ℚ ≤ Radial.mobility13 M →
  0ℚ ≤ Radial.mobility23 M →
  ¬ ( Radial.weightedTransfer (Radial.gradientFlux M)
      ≡ Radial.weightedTransfer threeFourFivePositiveRadialFlux )
nonnegativeGradientMobilityCannotMatchPositiveWaleffeWitness
    M m12NN m13NN m23NN matching =
  let
    gradientNonpositive :
      Radial.weightedTransfer (Radial.gradientFlux M) ≤ 0ℚ
    gradientNonpositive =
      Radial.nonnegativeGradientMobilityWeightedTransferNonpositive
        M m12NN m13NN m23NN

    witnessNonpositive :
      Radial.weightedTransfer threeFourFivePositiveRadialFlux ≤ 0ℚ
    witnessNonpositive =
      subst
        (λ value → value ≤ 0ℚ)
        matching
        gradientNonpositive

    tenNonpositive : ten ≤ 0ℚ
    tenNonpositive =
      subst
        (λ value → value ≤ 0ℚ)
        threeFourFivePositiveRadialWeightedTransfer
        witnessNonpositive
  in
  ℚP.<-irrefl 0ℚ
    (ℚP.<-≤-trans zeroLessTen tenNonpositive)

------------------------------------------------------------------------
-- The scalar isotropic gradient projection makes the sign flip numerical.
-- For radial weights (5,3,4), the squared radial-gradient sum is
--   (5-3)^2 + (5-4)^2 + (3-4)^2 = 6.
-- Hence +10 corresponds to effective isotropic mobility -5/3, whereas the
-- amplitude-flipped -10 cell corresponds to +5/3.
------------------------------------------------------------------------

isotropicThreeFourFiveMobility : ℚ → Radial.ThreeEdgeGradientMobility
isotropicThreeFourFiveMobility m =
  Radial.three-edge-gradient-mobility five three four m m m

minusFiveThirds plusFiveThirds : ℚ
minusFiveThirds = - (Int.+ 5 / 3)
plusFiveThirds = Int.+ 5 / 3

threeFourFiveNegativeEffectiveMobilityProducesPlusTen :
  Radial.weightedTransfer
    (Radial.gradientFlux
      (isotropicThreeFourFiveMobility minusFiveThirds))
  ≡ ten
threeFourFiveNegativeEffectiveMobilityProducesPlusTen = solve []

threeFourFivePositiveEffectiveMobilityProducesMinusTen :
  Radial.weightedTransfer
    (Radial.gradientFlux
      (isotropicThreeFourFiveMobility plusFiveThirds))
  ≡ - ten
threeFourFivePositiveEffectiveMobilityProducesMinusTen = solve []

round104WaleffeTransfersWireExactlyIntoRadialFlux : Bool
round104WaleffeTransfersWireExactlyIntoRadialFlux = true

round104FixedGeometryCriticalProductionChangesSignWithAmplitude : Bool
round104FixedGeometryCriticalProductionChangesSignWithAmplitude = true

round104UniversalPointwiseNonnegativeLeithMobilityRefuted : Bool
round104UniversalPointwiseNonnegativeLeithMobilityRefuted = true

-- What survives is a complete-network signed coercivity theorem.  Individual
-- cells may be adverse; the new Clay-level question is whether favourable
-- cells, exact phase/orbit cancellation and viscosity dominate the adverse
-- population after summing the literal finite Galerkin network.
round104AggregateSignedNetworkCoercivityClosed : Bool
round104AggregateSignedNetworkCoercivityClosed = false

round104UniversalPointwiseNonnegativeLeithMobilityRefutedIsTrue :
  round104UniversalPointwiseNonnegativeLeithMobilityRefuted ≡ true
round104UniversalPointwiseNonnegativeLeithMobilityRefutedIsTrue = refl

round104AggregateSignedNetworkCoercivityClosedIsFalse :
  round104AggregateSignedNetworkCoercivityClosed ≡ false
round104AggregateSignedNetworkCoercivityClosedIsFalse = refl