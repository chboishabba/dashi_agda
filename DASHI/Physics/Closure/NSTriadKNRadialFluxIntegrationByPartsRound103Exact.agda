module DASHI.Physics.Closure.NSTriadKNRadialFluxIntegrationByPartsRound103Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- Proceedings of the IRE 44(7) (1956), 904--913.
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- ROUND103 / RADIAL FLUX INTEGRATION BY PARTS
--
-- Round102 falsified the naive statement that conservative internal transfer
-- automatically annihilates derivative-weighted radial production.  The right
-- exact replacement is a discrete integration-by-parts identity.
--
-- Orient the three radial edges 1->2, 1->3, 2->3 and write their signed fluxes
-- J12,J13,J23.  The induced node transfers are
--
--   q1 =  J12 + J13
--   q2 = -J12 + J23
--   q3 = -J13 - J23.
--
-- Then total transfer vanishes IDENTICALLY, while the derivative-weighted
-- transfer is
--
--   lambda1 q1 + lambda2 q2 + lambda3 q3
--     = (lambda1-lambda2) J12
--       + (lambda1-lambda3) J13
--       + (lambda2-lambda3) J23.
--
-- Thus conservation removes the zero-th radial moment but leaves the first
-- spectral moment.  This is the exact finite statement behind the Round102
-- observation that a radial transfer defect is not a free telescope.
--
-- There is nevertheless a genuine signed closure mechanism: if every edge
-- flux is down the lambda-gradient,
--
--   Jij = mij (lambda_j-lambda_i),
--
-- then the weighted transfer is exactly the NEGATIVE Dirichlet form
--
--   - m12 (lambda1-lambda2)^2
--   - m13 (lambda1-lambda3)^2
--   - m23 (lambda2-lambda3)^2.
--
-- No positivity assumption is needed for the polynomial identity itself.
-- A physical Navier--Stokes closure must prove the corresponding mobility/sign
-- statement (or a stronger summed substitute) on the literal heterochiral
-- Waleffe transfer.  That is a materially sharper target than generic circle
-- Schur decay.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

sub : ℚ → ℚ → ℚ
sub x y = x + (- y)

record ThreeEdgeRadialFlux : Set where
  constructor three-edge-radial-flux
  field
    lambda1 lambda2 lambda3 : ℚ
    flux12 flux13 flux23 : ℚ

open ThreeEdgeRadialFlux public

transfer1 transfer2 transfer3 : ThreeEdgeRadialFlux → ℚ
transfer1 F = flux12 F + flux13 F
transfer2 F = (- flux12 F) + flux23 F
transfer3 F = (- flux13 F) + (- flux23 F)

totalTransfer : ThreeEdgeRadialFlux → ℚ
totalTransfer F = transfer1 F + transfer2 F + transfer3 F

weightedTransfer : ThreeEdgeRadialFlux → ℚ
weightedTransfer F =
  lambda1 F * transfer1 F
  + lambda2 F * transfer2 F
  + lambda3 F * transfer3 F

edgeGradientPairing : ThreeEdgeRadialFlux → ℚ
edgeGradientPairing F =
  sub (lambda1 F) (lambda2 F) * flux12 F
  + sub (lambda1 F) (lambda3 F) * flux13 F
  + sub (lambda2 F) (lambda3 F) * flux23 F

radialFluxIsConservative :
  (F : ThreeEdgeRadialFlux) → totalTransfer F ≡ 0ℚ
radialFluxIsConservative F =
  solve (flux12 F ∷ flux13 F ∷ flux23 F ∷ [])

radialFluxIntegrationByParts :
  (F : ThreeEdgeRadialFlux) →
  weightedTransfer F ≡ edgeGradientPairing F
radialFluxIntegrationByParts F =
  solve
    ( lambda1 F ∷ lambda2 F ∷ lambda3 F
    ∷ flux12 F ∷ flux13 F ∷ flux23 F ∷ [])

record ThreeEdgeGradientMobility : Set where
  constructor three-edge-gradient-mobility
  field
    lambda1 lambda2 lambda3 : ℚ
    mobility12 mobility13 mobility23 : ℚ

open ThreeEdgeGradientMobility public

gradientFlux : ThreeEdgeGradientMobility → ThreeEdgeRadialFlux
gradientFlux M =
  three-edge-radial-flux
    (ThreeEdgeGradientMobility.lambda1 M)
    (ThreeEdgeGradientMobility.lambda2 M)
    (ThreeEdgeGradientMobility.lambda3 M)
    (mobility12 M * sub (ThreeEdgeGradientMobility.lambda2 M)
                         (ThreeEdgeGradientMobility.lambda1 M))
    (mobility13 M * sub (ThreeEdgeGradientMobility.lambda3 M)
                         (ThreeEdgeGradientMobility.lambda1 M))
    (mobility23 M * sub (ThreeEdgeGradientMobility.lambda3 M)
                         (ThreeEdgeGradientMobility.lambda2 M))

gradientDirichletForm : ThreeEdgeGradientMobility → ℚ
gradientDirichletForm M =
  mobility12 M
    * (sub (ThreeEdgeGradientMobility.lambda1 M)
           (ThreeEdgeGradientMobility.lambda2 M)
       * sub (ThreeEdgeGradientMobility.lambda1 M)
             (ThreeEdgeGradientMobility.lambda2 M))
  + mobility13 M
    * (sub (ThreeEdgeGradientMobility.lambda1 M)
           (ThreeEdgeGradientMobility.lambda3 M)
       * sub (ThreeEdgeGradientMobility.lambda1 M)
             (ThreeEdgeGradientMobility.lambda3 M))
  + mobility23 M
    * (sub (ThreeEdgeGradientMobility.lambda2 M)
           (ThreeEdgeGradientMobility.lambda3 M)
       * sub (ThreeEdgeGradientMobility.lambda2 M)
             (ThreeEdgeGradientMobility.lambda3 M))

downGradientFluxWeightedTransferIsNegativeDirichlet :
  (M : ThreeEdgeGradientMobility) →
  weightedTransfer (gradientFlux M) ≡ - gradientDirichletForm M
downGradientFluxWeightedTransferIsNegativeDirichlet M =
  solve
    ( ThreeEdgeGradientMobility.lambda1 M
    ∷ ThreeEdgeGradientMobility.lambda2 M
    ∷ ThreeEdgeGradientMobility.lambda3 M
    ∷ mobility12 M ∷ mobility13 M ∷ mobility23 M ∷ [])

round103RadialFluxConservationClosed : Bool
round103RadialFluxConservationClosed = true

round103RadialFluxIntegrationByPartsClosed : Bool
round103RadialFluxIntegrationByPartsClosed = true

round103DownGradientRadialFluxGivesSignedDirichletForm : Bool
round103DownGradientRadialFluxGivesSignedDirichletForm = true

-- The physical theorem identifying the literal heterochiral Waleffe transfer
-- with a down-gradient mobility (or another equally strong signed summed
-- mechanism) is deliberately not manufactured here.
round103PhysicalWaleffeDownGradientMobilityClosed : Bool
round103PhysicalWaleffeDownGradientMobilityClosed = false

round103RadialFluxIntegrationByPartsClosedIsTrue :
  round103RadialFluxIntegrationByPartsClosed ≡ true
round103RadialFluxIntegrationByPartsClosedIsTrue = refl

round103DownGradientRadialFluxGivesSignedDirichletFormIsTrue :
  round103DownGradientRadialFluxGivesSignedDirichletForm ≡ true
round103DownGradientRadialFluxGivesSignedDirichletFormIsTrue = refl

round103PhysicalWaleffeDownGradientMobilityClosedIsFalse :
  round103PhysicalWaleffeDownGradientMobilityClosed ≡ false
round103PhysicalWaleffeDownGradientMobilityClosedIsFalse = refl
