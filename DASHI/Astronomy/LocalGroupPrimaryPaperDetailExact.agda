module DASHI.Astronomy.LocalGroupPrimaryPaperDetailExact where

open import DASHI.Core.Prelude
open import DASHI.Core.AttributedSourceCore using (AttributedSource)
open import DASHI.Astronomy.LocalGroupObservationFrameProvenanceExact
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Finer-grained source-paper formalisation for the first-light snowball.
-- These are source claims/artifact statements, not DASHI remeasurements.
------------------------------------------------------------------------

data EvidenceRole : Set where
  paperAbstractClaim : EvidenceRole
  paperMethodClaim : EvidenceRole
  paperDataAvailabilityClaim : EvidenceRole
  paperModelResultClaim : EvidenceRole
  paperCoordinateConventionClaim : EvidenceRole

record PaperDetail : Set where
  constructor paperDetail
  field
    paper : AttributedSource
    role : EvidenceRole
    subject : String
    retainedStatement : String
    formalisationUse : String
    independentlyReproducedHere : Bool

open PaperDetail public

kallivayalilLMCProperMotionDetail : PaperDetail
kallivayalilLMCProperMotionDetail = paperDetail
  kallivayalil2013
  paperAbstractClaim
  "LMC centre-of-mass proper motion"
  "mu_W(LMC) = -1.910 +/- 0.020 mas/yr; mu_N(LMC) = 0.229 +/- 0.047 mas/yr"
  "component-level benchmark target for the Virtual Observatory Galactocentric frame kernel"
  false

kallivayalilSMCProperMotionDetail : PaperDetail
kallivayalilSMCProperMotionDetail = paperDetail
  kallivayalil2013
  paperAbstractClaim
  "SMC centre-of-mass proper motion"
  "mu_W(SMC) = -0.772 +/- 0.063 mas/yr; mu_N(SMC) = -1.117 +/- 0.061 mas/yr"
  "retains the companion Magellanic-Cloud benchmark rather than only the LMC scalar speed"
  false

kallivayalilGalactocentricVelocityDetail : PaperDetail
kallivayalilGalactocentricVelocityDetail = paperDetail
  kallivayalil2013
  paperAbstractClaim
  "derived Galactocentric total velocities"
  "v_tot,LMC = 321 +/- 24 km/s; v_tot,SMC = 217 +/- 26 km/s"
  "separates source-derived Galactocentric velocities from directly observed proper motions"
  false

reidBrunthalerPlaneMotionDetail : PaperDetail
reidBrunthalerPlaneMotionDetail = paperDetail
  reidBrunthaler2020
  paperAbstractClaim
  "Sgr A* proper motion along Galactic plane"
  "-6.411 +/- 0.008 mas/yr"
  "external frame benchmark for the independently assembled Galactocentric frame"
  false

reidBrunthalerNorthMotionDetail : PaperDetail
reidBrunthalerNorthMotionDetail = paperDetail
  reidBrunthaler2020
  paperAbstractClaim
  "Sgr A* proper motion toward North Galactic Pole"
  "-0.219 +/- 0.007 mas/yr"
  "retains the orthogonal component rather than quotienting the benchmark to one scalar"
  false

reidBrunthalerResidualDetail : PaperDetail
reidBrunthalerResidualDetail = paperDetail
  reidBrunthaler2020
  paperAbstractClaim
  "solar-orbit-subtracted Sgr A* residual velocity"
  "-0.58 +/- 2.23 km/s in Galactic rotation direction; -0.85 +/- 0.75 km/s toward North Galactic Pole"
  "records the source interpretation after removing the Sun's orbital contribution; not a direct Cartesian Local Group measurement"
  false

vasilievCatalogueDetail : PaperDetail
vasilievCatalogueDetail = paperDetail
  vasilievBelokurovErkal2021
  paperMethodClaim
  "Sagittarius candidate-member catalogue"
  "about 55,000 high-probability stream members with 5D information and about 4,500 with 6D phase-space information, combining Gaia DR2 astrometry, RR Lyrae distances, and spectroscopic line-of-sight velocities"
  "source-bound comparison surface for any claimed last-printed-digit phase-space reproduction"
  false

vasilievCoordinateConventionDetail : PaperDetail
vasilievCoordinateConventionDetail = paperDetail
  vasilievBelokurovErkal2021
  paperCoordinateConventionClaim
  "Sagittarius Lambda/B coordinate convention"
  "right-handed celestial coordinate convention chosen with Lambda increasing toward the leading arm and zero at the Sgr remnant centre"
  "forces the Virtual Observatory comparison to pin handedness/sign convention before declaring coordinate agreement"
  false

vasilievTimeDependenceDetail : PaperDetail
vasilievTimeDependenceDetail = paperDetail
  vasilievBelokurovErkal2021
  paperModelResultClaim
  "time-dependent perturbation and LMC interaction"
  "leading-arm stream-track/proper-motion misalignment is interpreted as time-dependent gravitational-potential perturbation; models including an LMC mass around (1.3 +/- 0.3) x 10^11 solar masses rectify key deficiencies"
  "motivates a dynamic Local Group twin while preserving model-dependence and uncertainty"
  false

vasilievMilkyWayMassDetail : PaperDetail
vasilievMilkyWayMassDetail = paperDetail
  vasilievBelokurovErkal2021
  paperModelResultClaim
  "Milky Way mass constraints from Sgr/LMC modelling"
  "enclosed mass within 100 kpc = (5.6 +/- 0.4) x 10^11 solar masses; virial mass = (9.0 +/- 1.3) x 10^11 solar masses"
  "possible source-bound prior/check for future dynamical-twin mass uncertainty; not imported as a universal MW mass truth"
  false

record PublishedDataArtifact : Set where
  constructor publishedDataArtifact
  field
    sourcePaper : AttributedSource
    artifactLabel : String
    publicLocator : String
    artifactRole : String
    exactIdentityPinned : Bool
    acquiredIntoDASHI : Bool

open PublishedDataArtifact public

vasilievSagittariusCatalogueArtifact : PublishedDataArtifact
vasilievSagittariusCatalogueArtifact = publishedDataArtifact
  vasilievBelokurovErkal2021
  "Sagittarius high-probability candidate-member catalogue"
  "Zenodo record 4038137"
  "positions/proper motions plus RR-Lyrae-derived distances and a spectroscopic-velocity subset"
  true
  false

vasilievModelArchiveArtifact : PublishedDataArtifact
vasilievModelArchiveArtifact = publishedDataArtifact
  vasilievBelokurovErkal2021
  "fiducial Sgr+LMC model / time-dependent potential archive"
  "Zenodo record 4038141"
  "present-time N-body snapshot, MW+LMC time-dependent multipole expansions, trajectories, non-inertial-frame acceleration, and scripts for initial conditions/orbit integration"
  true
  false

publishedArtifactExistsImpliesVirtualObservatoryUsesSameArtifact : PublishedDataArtifact → Bool
publishedArtifactExistsImpliesVirtualObservatoryUsesSameArtifact _ = false

publishedArtifactExistsImpliesVirtualObservatoryUsesSameArtifactIsFalse :
  (a : PublishedDataArtifact) →
  publishedArtifactExistsImpliesVirtualObservatoryUsesSameArtifact a ≡ false
publishedArtifactExistsImpliesVirtualObservatoryUsesSameArtifactIsFalse a = refl

paperModelResultImpliesValidatedLocalGroupTwin : PaperDetail → Bool
paperModelResultImpliesValidatedLocalGroupTwin _ = false

paperModelResultImpliesValidatedLocalGroupTwinIsFalse :
  (d : PaperDetail) → paperModelResultImpliesValidatedLocalGroupTwin d ≡ false
paperModelResultImpliesValidatedLocalGroupTwinIsFalse d = refl
