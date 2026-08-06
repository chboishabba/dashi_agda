module DASHI.Physics.Closure.NSTriadKNLuoFilteredVorticitySubfilterStressExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Anthony Leonard.
-- Title: "Energy Cascade in Large-Eddy Simulations of Turbulent Fluid
-- Flows".
-- DOI: 10.1016/S0065-2687(08)60464-1.
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
-- Status: arXiv preprint, submitted 25 June 2026.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "A Unified Approach to Regularity Problems for the 3D Navier-Stokes
-- and Euler Equations: The Use of Kolmogorov's Dissipation Range".
-- DOI: 10.1007/s00021-014-0167-4.
--
-- DASHI CONTRIBUTION
--
-- This module derives the literal subfilter-stress form of one filtered
-- vorticity component.  A product-filter jet records only the primitive facts
-- used in the derivation:
--
--   d F(ab) = F((da)b) + F(a db),
--   F((da)b) = 0,        da_bar = 0.
--
-- It then proves exactly
--
--   d ( F(ab) - a_bar b_bar )
--     = F(a db) - a_bar db_bar.
--
-- Applying this once to transport and once to stretching gives
--
--   d_t omega_bar + u_bar . grad omega_bar
--     = omega_bar . grad u_bar + nu Delta omega_bar
--       - div tau^{u omega} + div tau^{omega u}.
--
-- The result is finite and componentwise, but is not a numerical-LES model:
-- the two stresses are exact residuals.  The continuum filter, torus
-- differentiation and dyadic paraproduct index ranges remain separate analytic
-- and formal interfaces.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; trans)

record ProductFilterJet : Set where
  constructor productFilterJet
  field
    filteredProductDerivative : ℚ
    filteredDivergenceProduct : ℚ
    filteredAdvectiveProduct : ℚ

    resolvedTransporter : ℚ
    resolvedTransported : ℚ
    resolvedTransporterDerivative : ℚ
    resolvedTransportedDerivative : ℚ

    filteredProductRule :
      filteredProductDerivative
      ≡ filteredDivergenceProduct + filteredAdvectiveProduct

    filteredDivergenceFree :
      filteredDivergenceProduct ≡ 0ℚ

    resolvedDivergenceFree :
      resolvedTransporterDerivative ≡ 0ℚ

open ProductFilterJet public

resolvedAdvectiveProduct : ProductFilterJet → ℚ
resolvedAdvectiveProduct jet =
  resolvedTransporter jet * resolvedTransportedDerivative jet

resolvedProductDerivative : ProductFilterJet → ℚ
resolvedProductDerivative jet =
  resolvedTransporterDerivative jet * resolvedTransported jet
  + resolvedAdvectiveProduct jet

subfilterStressDivergence : ProductFilterJet → ℚ
subfilterStressDivergence jet =
  filteredProductDerivative jet - resolvedProductDerivative jet

subfilterStressDivergenceIdentity :
  ∀ jet →
  subfilterStressDivergence jet
  ≡ filteredAdvectiveProduct jet - resolvedAdvectiveProduct jet
subfilterStressDivergenceIdentity jet
  rewrite filteredProductRule jet
        | filteredDivergenceFree jet
        | resolvedDivergenceFree jet =
  solve
    ( filteredAdvectiveProduct jet
    ∷ resolvedTransporter jet
    ∷ resolvedTransportedDerivative jet
    ∷ [])

sumFilteredAdvective : List ProductFilterJet → ℚ
sumFilteredAdvective [] = 0ℚ
sumFilteredAdvective (jet ∷ jets) =
  filteredAdvectiveProduct jet + sumFilteredAdvective jets

sumResolvedAdvective : List ProductFilterJet → ℚ
sumResolvedAdvective [] = 0ℚ
sumResolvedAdvective (jet ∷ jets) =
  resolvedAdvectiveProduct jet + sumResolvedAdvective jets

sumStressDivergence : List ProductFilterJet → ℚ
sumStressDivergence [] = 0ℚ
sumStressDivergence (jet ∷ jets) =
  subfilterStressDivergence jet + sumStressDivergence jets

finiteSubfilterStressDivergenceIdentity :
  ∀ jets →
  sumStressDivergence jets
  ≡ sumFilteredAdvective jets - sumResolvedAdvective jets
finiteSubfilterStressDivergenceIdentity [] = solve []
finiteSubfilterStressDivergenceIdentity (jet ∷ jets)
  rewrite subfilterStressDivergenceIdentity jet
        | finiteSubfilterStressDivergenceIdentity jets =
  solve
    ( filteredAdvectiveProduct jet
    ∷ resolvedAdvectiveProduct jet
    ∷ sumFilteredAdvective jets
    ∷ sumResolvedAdvective jets
    ∷ [])

record FilteredVorticityComponentEquation : Set where
  constructor filteredVorticityComponentEquation
  field
    timeDerivative viscosityLaplacian : ℚ
    transportJets stretchingJets : List ProductFilterJet

    filteredCurlEquation :
      timeDerivative + sumFilteredAdvective transportJets
      ≡ sumFilteredAdvective stretchingJets + viscosityLaplacian

open FilteredVorticityComponentEquation public

resolvedFilteredVorticityEquation :
  ∀ equation →
  timeDerivative equation
    + sumResolvedAdvective (transportJets equation)
  ≡
  sumResolvedAdvective (stretchingJets equation)
    + viscosityLaplacian equation
    - sumStressDivergence (transportJets equation)
    + sumStressDivergence (stretchingJets equation)
resolvedFilteredVorticityEquation equation =
  let
    filteredTransport = sumFilteredAdvective (transportJets equation)
    resolvedTransport = sumResolvedAdvective (transportJets equation)
    transportStress = sumStressDivergence (transportJets equation)

    filteredStretch = sumFilteredAdvective (stretchingJets equation)
    resolvedStretch = sumResolvedAdvective (stretchingJets equation)
    stretchStress = sumStressDivergence (stretchingJets equation)

    shifted =
      cong
        (λ value → value - filteredTransport + resolvedTransport)
        (filteredCurlEquation equation)

    leftMeaning :
      (timeDerivative equation + filteredTransport)
        - filteredTransport + resolvedTransport
      ≡ timeDerivative equation + resolvedTransport
    leftMeaning =
      solve
        ( timeDerivative equation
        ∷ filteredTransport
        ∷ resolvedTransport
        ∷ [])

    rightMeaning :
      (filteredStretch + viscosityLaplacian equation)
        - filteredTransport + resolvedTransport
      ≡
      resolvedStretch + viscosityLaplacian equation
        - transportStress + stretchStress
    rightMeaning
      rewrite finiteSubfilterStressDivergenceIdentity
                (transportJets equation)
            | finiteSubfilterStressDivergenceIdentity
                (stretchingJets equation) =
      solve
        ( filteredTransport ∷ resolvedTransport
        ∷ filteredStretch ∷ resolvedStretch
        ∷ viscosityLaplacian equation
        ∷ [])
  in
  trans (sym leftMeaning) (trans shifted rightMeaning)

record FilteredStressAuthorityBoundary : Set where
  constructor filteredStressAuthorityBoundary
  field
    componentStressIdentityProved : Set
    finiteDivergenceSummationProved : Set
    exactResolvedTransportEquationProved : Set
    periodicFilterCommutationConstructed : Set
    dyadicParaproductRangesDerived : Set
    subfilterStressCriticalEstimateProved : Set

canonicalFilteredStressAuthorityBoundary : FilteredStressAuthorityBoundary
canonicalFilteredStressAuthorityBoundary =
  filteredStressAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
