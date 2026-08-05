module DASHI.Physics.Closure.NSTriadKNGrujicLocalizedVorticityCoherenceSourceAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Zoran Grujic.
-- Title: "Localization and Geometric Depletion of Vortex-Stretching in the
-- 3D NSE".
-- Communications in Mathematical Physics 290 (2009), 861--870.
-- DOI: 10.1007/s00220-008-0726-8.
--
-- Earlier geometric anchor:
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- PURPOSE
-- Expose the exact logical role of the classical localized theorem.  It proves
-- regularity from a one-half Holder coherence condition on the vorticity
-- direction in the high-vorticity region of a parabolic cylinder.  It does
-- not derive that coherence condition from the energy inequality.
--
-- The source supplies the established physical-space geometric mechanism for
-- a future comparable-shell producer, while the automatic production of the
-- required coherence or its dyadic averaged substitute remains a frontier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

halfHolderExponent : ℚ
halfHolderExponent = Int.+ 1 / 2

data CoherenceStatus : Set where
  assumedHighVorticityCoherence : CoherenceStatus
  derivedFromEnergy : CoherenceStatus

classicalTheoremCoherenceStatus : CoherenceStatus
classicalTheoremCoherenceStatus = assumedHighVorticityCoherence

coherenceIsNotDerivedFromEnergy :
  classicalTheoremCoherenceStatus ≢ derivedFromEnergy
coherenceIsNotDerivedFromEnergy ()

record LocalizedVorticityCoherenceCriterion : Set₁ where
  field
    leraySolutionOnCylinder : Set
    smoothBelowTerminalTime : Set
    highVorticityRegion : Set
    halfHolderDirectionCoherence : Set
    localizedEnstrophyBounded : Set

    criterion :
      leraySolutionOnCylinder →
      smoothBelowTerminalTime →
      highVorticityRegion →
      halfHolderDirectionCoherence →
      localizedEnstrophyBounded

record DyadicCoherenceBridge : Set₁ where
  field
    physicalSpaceCoherence : Set
    comparableShellDefectBound : Set
    transfer : physicalSpaceCoherence → comparableShellDefectBound

-- No dyadic bridge is invented.  It must preserve the high-vorticity cutoff,
-- the one-half exponent, localization costs and the singular strain kernel.
