module DASHI.Physics.Closure.NSTriadKNCherevanHeatSchrodingerSourceAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Pylyp Cherevan.
-- Title: "A log-free estimate for the diagonal paraproduct high x high to
-- low in the 3D Navier--Stokes equation".
-- arXiv:2510.07848v1.
-- arXiv DOI: 10.48550/arXiv.2510.07848.
--
-- Dispersive reference used by that source:
-- Authors: Markus Keel; Terence Tao.
-- Title: "Endpoint Strichartz Estimates".
-- DOI: 10.2307/121095.
--
-- PURPOSE
-- Correct a possible source misclassification and expose the exact bridge
-- obligation.  arXiv:2510.07848 is itself another Navier--Stokes preprint,
-- not a separate Schrodinger-equation paper.  Nevertheless its Section 3
-- explicitly establishes a local endpoint estimate for the Schrodinger flow
-- and uses that block in the final assembly, while Appendix A says the
-- heat--Schrodinger comparison does not enter the exponent balance.
--
-- A dispersive endpoint estimate and a heat-semigroup estimate are therefore
-- different producer lanes.  A valid transfer must exhibit a quantitative
-- error estimate on the same window and in the same norm; it cannot be
-- supplied by renaming the generator.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

data EvolutionGenerator : Set where
  heatGenerator : EvolutionGenerator
  schrodingerGenerator : EvolutionGenerator

navierStokesLinearGenerator : EvolutionGenerator
navierStokesLinearGenerator = heatGenerator

paperEndpointEstimateGenerator : EvolutionGenerator
paperEndpointEstimateGenerator = schrodingerGenerator

heatIsNotSchrodinger :
  navierStokesLinearGenerator ≢ paperEndpointEstimateGenerator
heatIsNotSchrodinger ()

data SourceKind : Set where
  navierStokesPreprint : SourceKind
  schrodingerEquationPaper : SourceKind

secondSourceKind : SourceKind
secondSourceKind = navierStokesPreprint

secondSourceIsNotSchrodingerPaper :
  secondSourceKind ≢ schrodingerEquationPaper
secondSourceIsNotSchrodingerPaper ()

data QuantitativeRole : Set where
  entersExponentBalance : QuantitativeRole
  auxiliaryOnly : QuantitativeRole

paperStrichartzRole : QuantitativeRole
paperStrichartzRole = entersExponentBalance

paperAppendixComparisonRole : QuantitativeRole
paperAppendixComparisonRole = auxiliaryOnly

strichartzAndAuxiliaryComparisonAreDistinct :
  paperStrichartzRole ≢ paperAppendixComparisonRole
strichartzAndAuxiliaryComparisonAreDistinct ()

record HeatFromSchrodingerBridge : Set₁ where
  field
    heatStatement : Set
    schrodingerStatement : Set
    comparisonErrorStatement : Set
    transfer :
      schrodingerStatement →
      comparisonErrorStatement →
      heatStatement

-- No inhabitant is manufactured here.  A later use of the source must provide
-- the bridge with the actual time window, frequency localization, norm and
-- quantitative error visible in its fields.
