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
-- Round104 strengthens the polynomial identity with the ordered-rational
-- consequence actually needed by a Leith/graph-Laplacian interpretation:
-- if all three mobilities are nonnegative, the Dirichlet form is nonnegative
-- and the weighted transfer is nonpositive.  This makes pointwise
-- nonnegative-mobility falsification possible using one positive Waleffe
-- critical-production cell.
--
-- No physical Navier--Stokes mobility/sign statement is imported here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Algebra.Properties.Group as GroupProperties
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _*_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order

module AddGroup = GroupProperties ℚₚ.+-0-group

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

-- Keep the mobility radii projection names distinct from the flux radii.
-- Round103 originally opened both records with lambda1/lambda2/lambda3,
-- which relied on overloaded projection resolution and had not received a
-- fresh Agda kernel check in the connector environment.
record ThreeEdgeGradientMobility : Set where
  constructor three-edge-gradient-mobility
  field
    mobilityLambda1 mobilityLambda2 mobilityLambda3 : ℚ
    mobility12 mobility13 mobility23 : ℚ

open ThreeEdgeGradientMobility public

gradientFlux : ThreeEdgeGradientMobility → ThreeEdgeRadialFlux
gradientFlux M =
  three-edge-radial-flux
    (mobilityLambda1 M)
    (mobilityLambda2 M)
    (mobilityLambda3 M)
    (mobility12 M * sub (mobilityLambda2 M) (mobilityLambda1 M))
    (mobility13 M * sub (mobilityLambda3 M) (mobilityLambda1 M))
    (mobility23 M * sub (mobilityLambda3 M) (mobilityLambda2 M))

gradientDirichletForm : ThreeEdgeGradientMobility → ℚ
gradientDirichletForm M =
  mobility12 M
    * (sub (mobilityLambda1 M) (mobilityLambda2 M)
       * sub (mobilityLambda1 M) (mobilityLambda2 M))
  + mobility13 M
    * (sub (mobilityLambda1 M) (mobilityLambda3 M)
       * sub (mobilityLambda1 M) (mobilityLambda3 M))
  + mobility23 M
    * (sub (mobilityLambda2 M) (mobilityLambda3 M)
       * sub (mobilityLambda2 M) (mobilityLambda3 M))

downGradientFluxWeightedTransferIsNegativeDirichlet :
  (M : ThreeEdgeGradientMobility) →
  weightedTransfer (gradientFlux M) ≡ - gradientDirichletForm M
downGradientFluxWeightedTransferIsNegativeDirichlet M =
  solve
    ( mobilityLambda1 M ∷ mobilityLambda2 M ∷ mobilityLambda3 M
    ∷ mobility12 M ∷ mobility13 M ∷ mobility23 M ∷ [])

mobilityTimesSquareNonnegative :
  (m x : ℚ) →
  0ℚ ≤ m →
  0ℚ ≤ m * (x * x)
mobilityTimesSquareNonnegative m x mNonnegativeProof =
  let
    xSquareNonnegative : 0ℚ ≤ x * x
    xSquareNonnegative = Order.squareNonnegative x

    instance
      mNN = ℚ.nonNegative mNonnegativeProof
      xSquareNN = ℚ.nonNegative xSquareNonnegative
      productNN = ℚₚ.nonNeg*nonNeg⇒nonNeg m (x * x)
  in
  ℚₚ.nonNegative⁻¹ (m * (x * x))

gradientDirichletFormNonnegative :
  (M : ThreeEdgeGradientMobility) →
  0ℚ ≤ mobility12 M →
  0ℚ ≤ mobility13 M →
  0ℚ ≤ mobility23 M →
  0ℚ ≤ gradientDirichletForm M
gradientDirichletFormNonnegative M m12NN m13NN m23NN =
  Order.addNonnegative
    (Order.addNonnegative
      (mobilityTimesSquareNonnegative
        (mobility12 M)
        (sub (mobilityLambda1 M) (mobilityLambda2 M))
        m12NN)
      (mobilityTimesSquareNonnegative
        (mobility13 M)
        (sub (mobilityLambda1 M) (mobilityLambda3 M))
        m13NN))
    (mobilityTimesSquareNonnegative
      (mobility23 M)
      (sub (mobilityLambda2 M) (mobilityLambda3 M))
      m23NN)

nonnegativeGradientMobilityWeightedTransferNonpositive :
  (M : ThreeEdgeGradientMobility) →
  0ℚ ≤ mobility12 M →
  0ℚ ≤ mobility13 M →
  0ℚ ≤ mobility23 M →
  weightedTransfer (gradientFlux M) ≤ 0ℚ
nonnegativeGradientMobilityWeightedTransferNonpositive M m12NN m13NN m23NN =
  let
    dirichletNN : 0ℚ ≤ gradientDirichletForm M
    dirichletNN =
      gradientDirichletFormNonnegative M m12NN m13NN m23NN

    negativeDirichletNonpositive : - gradientDirichletForm M ≤ 0ℚ
    negativeDirichletNonpositive =
      subst
        (λ upper → - gradientDirichletForm M ≤ upper)
        AddGroup.ε⁻¹≈ε
        (ℚₚ.neg-antimono-≤ dirichletNN)
  in
  subst
    (λ value → value ≤ 0ℚ)
    (sym (downGradientFluxWeightedTransferIsNegativeDirichlet M))
    negativeDirichletNonpositive

round103RadialFluxConservationClosed : Bool
round103RadialFluxConservationClosed = true

round103RadialFluxIntegrationByPartsClosed : Bool
round103RadialFluxIntegrationByPartsClosed = true

round103DownGradientRadialFluxGivesSignedDirichletForm : Bool
round103DownGradientRadialFluxGivesSignedDirichletForm = true

round104NonnegativeGradientMobilityIsNonpositive : Bool
round104NonnegativeGradientMobilityIsNonpositive = true

-- The physical theorem identifying the literal heterochiral Waleffe transfer
-- with a down-gradient mobility (or another equally strong signed summed
-- mechanism) is deliberately not manufactured here.  Round104 will show that
-- the universal pointwise all-nonnegative version is in fact too strong.
round103PhysicalWaleffeDownGradientMobilityClosed : Bool
round103PhysicalWaleffeDownGradientMobilityClosed = false

round103RadialFluxIntegrationByPartsClosedIsTrue :
  round103RadialFluxIntegrationByPartsClosed ≡ true
round103RadialFluxIntegrationByPartsClosedIsTrue = refl

round103DownGradientRadialFluxGivesSignedDirichletFormIsTrue :
  round103DownGradientRadialFluxGivesSignedDirichletForm ≡ true
round103DownGradientRadialFluxGivesSignedDirichletFormIsTrue = refl

round104NonnegativeGradientMobilityIsNonpositiveIsTrue :
  round104NonnegativeGradientMobilityIsNonpositive ≡ true
round104NonnegativeGradientMobilityIsNonpositiveIsTrue = refl

round103PhysicalWaleffeDownGradientMobilityClosedIsFalse :
  round103PhysicalWaleffeDownGradientMobilityClosed ≡ false
round103PhysicalWaleffeDownGradientMobilityClosedIsFalse = refl