module DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

bedroyaBackgroundSource : Source.AttributedSource
bedroyaBackgroundSource =
  Source.mkDOISource
    "Alek Bedroya; Georges Obied; Cumrun Vafa; David H. Wu"
    "Evolving Dark Sector and the Dark Dimension Scenario"
    "Physical Review D"
    "2026"
    "10.1103/1rsq-cv2m"
    "https://doi.org/10.1103/1rsq-cv2m"
    Source.academicArticleSource
    "source for the fading-dark-sector background equations, DESI background-distance observables, and fitted c/cPrime coordinates; equation availability does not import the authors' complete numerical MCMC manifest"
    Source.publicAttribution

paperArXiv : String
paperArXiv = "2507.03090"

potentialEquation : String
potentialEquation = "V = V0 exp(-c phi)"

darkMatterMassEquation : String
darkMatterMassEquation = "m_DM = m0 exp(-cPrime phi)"

effectivePotentialEquation : String
effectivePotentialEquation =
  "V_eff = V0 exp(-c phi) + m0 n0 a^-3 exp(-cPrime phi)"

friedmannEquation : String
friedmannEquation =
  "3 H^2 = 1/2 phi_dot^2 + V_eff + Omega_R0 a^-4 (3 H0^2) + Omega_B0 a^-3 (3 H0^2)"

kleinGordonEquation : String
kleinGordonEquation =
  "phi_ddot + 3 H phi_dot + dV_eff/dphi = 0"

transverseDistanceEquation : String
transverseDistanceEquation = "D_M(z) = integral_0^z dzPrime / H(zPrime)"

radialDistanceEquation : String
radialDistanceEquation = "D_H(z) = 1 / H(z)"

pantheonNegativeCBestFitC : String
pantheonNegativeCBestFitC = "-0.85"

pantheonNegativeCBestFitCPrime : String
pantheonNegativeCBestFitCPrime = "0.05"

record BedroyaBackgroundReconstructionStatus : Set where
  constructor bedroyaBackgroundReconstructionStatus
  field
    potentialEquationLocated : Bool
    darkMatterMassEquationLocated : Bool
    effectivePotentialEquationLocated : Bool
    friedmannEquationLocated : Bool
    kleinGordonEquationLocated : Bool
    desiBackgroundObservableEquationLocated : Bool
    pantheonNegativeCBestFitLocated : Bool
    standardCosmologyBestFitManifestLocated : Bool
    normalizationManifestLocated : Bool
    backgroundIntegratorExecutable : Bool
    sixKeyBAOVectorDerived : Bool

open BedroyaBackgroundReconstructionStatus public

canonicalBedroyaBackgroundReconstructionStatus : BedroyaBackgroundReconstructionStatus
canonicalBedroyaBackgroundReconstructionStatus =
  bedroyaBackgroundReconstructionStatus
    true true true true true true true false false false false

data LocatedEquationsEqualNumericalManifest : Set where

data BestFitCouplingsDetermineBackgroundVector : Set where

equationsDoNotEqualNumericalManifest :
  LocatedEquationsEqualNumericalManifest → ⊥
equationsDoNotEqualNumericalManifest ()

bestFitCouplingsDoNotDetermineBackgroundVector :
  BestFitCouplingsDetermineBackgroundVector → ⊥
bestFitCouplingsDoNotDetermineBackgroundVector ()

backgroundReconstructionStillOpen :
  backgroundIntegratorExecutable canonicalBedroyaBackgroundReconstructionStatus ≡ false
backgroundReconstructionStillOpen = refl

standardCosmologyManifestStillOpen :
  standardCosmologyBestFitManifestLocated canonicalBedroyaBackgroundReconstructionStatus ≡ false
standardCosmologyManifestStillOpen = refl

normalizationManifestStillOpen :
  normalizationManifestLocated canonicalBedroyaBackgroundReconstructionStatus ≡ false
normalizationManifestStillOpen = refl

sixKeyVectorStillOpen :
  sixKeyBAOVectorDerived canonicalBedroyaBackgroundReconstructionStatus ≡ false
sixKeyVectorStillOpen = refl
