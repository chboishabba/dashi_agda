module DASHI.Physics.Closure.NSTriadKNFrankSukochevZaninCommutatorSourceAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Rupert L. Frank; Fedor Sukochev; Dmitriy Zanin.
-- Title: "Endpoint Schatten Class Properties of Commutators".
-- Advances in Mathematics 450 (2024), article 109738.
-- DOI: 10.1016/j.aim.2024.109738.
-- arXiv DOI: 10.48550/arXiv.2405.10652.
--
-- PURPOSE
-- Audit the supplied operator-theoretic paper against the DASHI dyadic
-- Navier--Stokes commutator.  The source proves endpoint weak-Schatten
-- characterisations for
--
--   [(-Delta)^(epsilon/2), M_f]
--
-- and develops a finite spectral-projection approximation followed by a
-- strong/ideal limit.  That approximation architecture is relevant to the
-- proposed Galerkin-uniform route, but the source does not prove the specific
-- Littlewood--Paley transport estimate [Delta_q,a.grad]g.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

data CommutatorSetting : Set where
  fractionalLaplacianMultiplication : CommutatorSetting
  dyadicTransportLittlewoodPaley : CommutatorSetting
  rieszModulatedEnergy : CommutatorSetting

sourceSetting : CommutatorSetting
sourceSetting = fractionalLaplacianMultiplication

sourceIsNotDyadicTransport :
  sourceSetting ≢ dyadicTransportLittlewoodPaley
sourceIsNotDyadicTransport ()

sourceIsNotRieszEnergy :
  sourceSetting ≢ rieszModulatedEnergy
sourceIsNotRieszEnergy ()

data SourceContribution : Set where
  endpointWeakSchattenBound : SourceContribution
  spectralProjectionApproximation : SourceContribution
  uniformBoundThenLimit : SourceContribution
  leadingLaplacianCommutator : SourceContribution
  completeSixThreeDyadicEstimate : SourceContribution

sourceSuppliesProjectionArchitecture : SourceContribution
sourceSuppliesProjectionArchitecture = spectralProjectionApproximation

sourceSuppliesUniformLimitArchitecture : SourceContribution
sourceSuppliesUniformLimitArchitecture = uniformBoundThenLimit

sourceSuppliesLeadingCommutator : SourceContribution
sourceSuppliesLeadingCommutator = leadingLaplacianCommutator

sourceDoesNotDirectlySupplySixThree :
  sourceSuppliesLeadingCommutator ≢ completeSixThreeDyadicEstimate
sourceDoesNotDirectlySupplySixThree ()

-- Exact scalar Leibniz algebra behind the leading commutator
--
--   [Delta,M_f]g = (Delta f) g + 2 grad f . grad g
--
-- up to the sign convention chosen for Delta.  The theorem is deliberately
-- stated as an algebraic identity so no analytic sign convention is hidden.
laplacianProductExpansion :
  (f fFirst fSecond g gFirst gSecond : ℚ) →
  fSecond * g + (fFirst * gFirst + fFirst * gFirst) + f * gSecond
    - f * gSecond
  ≡ fSecond * g + (fFirst * gFirst + fFirst * gFirst)
laplacianProductExpansion
  f fFirst fSecond g gFirst gSecond =
  solve (f ∷ fFirst ∷ fSecond ∷ g ∷ gFirst ∷ gSecond ∷ [])

-- A finite projection sandwich is distinct from the untruncated operator,
-- but a uniform estimate may be transported once the chosen convergence
-- theorem is supplied.
data ApproximationStage : Set where
  finiteProjectionSandwich : ApproximationStage
  strongOperatorLimit : ApproximationStage

finiteStageIsNotLimit :
  finiteProjectionSandwich ≢ strongOperatorLimit
finiteStageIsNotLimit ()
