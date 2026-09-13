module DASHI.Astronomy.LocalGroupFirstLightScientificClaimsExact where

open import DASHI.Core.Prelude
open import DASHI.Core.AttributedSourceCore using (AttributedSource)
open import DASHI.Astronomy.LocalGroupObservationFrameProvenanceExact
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-bound scientific claims used around the first-light reconstruction.
-- Numerical text is retained as source transcription, not silently promoted
-- into a unit-safe numerical library by this module.
------------------------------------------------------------------------

record SourceBoundScientificClaim : Set where
  constructor sourceBoundScientificClaim
  field
    source : AttributedSource
    subject : String
    sourceClaim : String
    quantityRole : QuantityRole
    sourceScope : String

open SourceBoundScientificClaim public

kallivayalilLMCProperMotion : SourceBoundScientificClaim
kallivayalilLMCProperMotion =
  sourceBoundScientificClaim
    kallivayalil2013
    "Large Magellanic Cloud centre-of-mass proper motion"
    "mu_W = -1.910 +/- 0.020 mas/yr; mu_N = 0.229 +/- 0.047 mas/yr"
    sourceDerived
    "three-epoch HST proper-motion analysis; paper value, not a DASHI measurement"

kallivayalilLMCGalactocentricSpeed : SourceBoundScientificClaim
kallivayalilLMCGalactocentricSpeed =
  sourceBoundScientificClaim
    kallivayalil2013
    "Large Magellanic Cloud Galactocentric total velocity"
    "v_tot,LMC = 321 +/- 24 km/s"
    sourceDerived
    "derived by combining proper-motion results with revised solar-motion assumptions"

kallivayalilSMCGalactocentricSpeed : SourceBoundScientificClaim
kallivayalilSMCGalactocentricSpeed =
  sourceBoundScientificClaim
    kallivayalil2013
    "Small Magellanic Cloud Galactocentric total velocity"
    "v_tot,SMC = 217 +/- 26 km/s"
    sourceDerived
    "derived by combining proper-motion results with revised solar-motion assumptions"

reidBrunthalerSgrAPlaneMotion : SourceBoundScientificClaim
reidBrunthalerSgrAPlaneMotion =
  sourceBoundScientificClaim
    reidBrunthaler2020
    "Sagittarius A* apparent proper motion along Galactic plane"
    "-6.411 +/- 0.008 mas/yr"
    directlyObserved
    "18-year VLBA baseline relative to extragalactic radio sources"

reidBrunthalerSgrANorthMotion : SourceBoundScientificClaim
reidBrunthalerSgrANorthMotion =
  sourceBoundScientificClaim
    reidBrunthaler2020
    "Sagittarius A* apparent proper motion toward North Galactic Pole"
    "-0.219 +/- 0.007 mas/yr"
    directlyObserved
    "18-year VLBA baseline relative to extragalactic radio sources"

vasilievSagittariusCatalogue : SourceBoundScientificClaim
vasilievSagittariusCatalogue =
  sourceBoundScientificClaim
    vasilievBelokurovErkal2021
    "candidate Sagittarius stream member catalogue"
    "5D and 6D phase-space information assembled from Gaia DR2 astrometry, RR Lyrae distances, and spectroscopic line-of-sight velocities"
    catalogTabulated
    "candidate stream membership and heterogeneous observational inputs"

vasilievTimeDependentPerturbation : SourceBoundScientificClaim
vasilievTimeDependentPerturbation =
  sourceBoundScientificClaim
    vasilievBelokurovErkal2021
    "Sagittarius stream dynamics"
    "leading-arm stream-track / reflex-corrected-proper-motion misalignment is interpreted as a signature of a time-dependent gravitational-potential perturbation, with the LMC as a likely cause"
    modelConstructed
    "paper interpretation/model result; not equivalent to a direct observation of the gravitational potential"

mcConnachieCensusScope : SourceBoundScientificClaim
mcConnachieCensusScope =
  sourceBoundScientificClaim
    mcConnachie2012
    "nearby dwarf-galaxy census"
    "over 100 nearby galaxies with distance estimates placing them within 3 Mpc of the Sun, spanning MW and M31 satellites, outer Local Group dwarfs, and isolated nearby galaxies"
    catalogTabulated
    "2012 collated/homogenized observational catalogue and discussion"

------------------------------------------------------------------------
-- Paper-scope firewalls.
------------------------------------------------------------------------

mcConnachieCensusImpliesIndependentCrossSurveyConfirmation : Bool
mcConnachieCensusImpliesIndependentCrossSurveyConfirmation = false

mcConnachieCensusImpliesIndependentCrossSurveyConfirmationIsFalse :
  mcConnachieCensusImpliesIndependentCrossSurveyConfirmation ≡ false
mcConnachieCensusImpliesIndependentCrossSurveyConfirmationIsFalse = refl

kallivayalilProperMotionImpliesUniqueOrbitHistory : Bool
kallivayalilProperMotionImpliesUniqueOrbitHistory = false

kallivayalilProperMotionImpliesUniqueOrbitHistoryIsFalse :
  kallivayalilProperMotionImpliesUniqueOrbitHistory ≡ false
kallivayalilProperMotionImpliesUniqueOrbitHistoryIsFalse = refl

vasilievCandidateMembershipImpliesCertainMembership : Bool
vasilievCandidateMembershipImpliesCertainMembership = false

vasilievCandidateMembershipImpliesCertainMembershipIsFalse :
  vasilievCandidateMembershipImpliesCertainMembership ≡ false
vasilievCandidateMembershipImpliesCertainMembershipIsFalse = refl

vasilievTimeDependentInterpretationImpliesUniqueLMCCause : Bool
vasilievTimeDependentInterpretationImpliesUniqueLMCCause = false

vasilievTimeDependentInterpretationImpliesUniqueLMCCauseIsFalse :
  vasilievTimeDependentInterpretationImpliesUniqueLMCCause ≡ false
vasilievTimeDependentInterpretationImpliesUniqueLMCCauseIsFalse = refl

reidBrunthalerProperMotionImpliesVirtualObservatoryFrameCorrect : Bool
reidBrunthalerProperMotionImpliesVirtualObservatoryFrameCorrect = false

reidBrunthalerProperMotionImpliesVirtualObservatoryFrameCorrectIsFalse :
  reidBrunthalerProperMotionImpliesVirtualObservatoryFrameCorrect ≡ false
reidBrunthalerProperMotionImpliesVirtualObservatoryFrameCorrectIsFalse = refl

------------------------------------------------------------------------
-- KKH 86: retain the first-light exception rather than quotienting it away.
------------------------------------------------------------------------

record DerivedDistanceResidual : Set where
  constructor derivedDistanceResidual
  field
    memberIdentity : String
    residualComparisonSource : AttributedSource
    claimant : String
    residualKpcText : String
    printedPrecisionKpcText : String
    causeStatus : String
    rowInputsAcquired : Bool
    independentlyRecomputedByDASHI : Bool
    unresolved : Bool

open DerivedDistanceResidual public

kkh86FirstLightResidual : DerivedDistanceResidual
kkh86FirstLightResidual =
  derivedDistanceResidual
    "KKH 86"
    mcConnachie2012
    "Poppie / NOUS — private post displayed 2026-09-07 23:38"
    "1.2 kpc"
    "+/-0.5 kpc printed precision claimed for the compared derived column"
    "no identifiable cause in the inputs according to the attributed post"
    false
    false
    true

unresolvedResidualMayBeErasedByAggregateAgreement : DerivedDistanceResidual → Bool
unresolvedResidualMayBeErasedByAggregateAgreement _ = false

unresolvedResidualMayBeErasedByAggregateAgreementIsFalse :
  (r : DerivedDistanceResidual) →
  unresolvedResidualMayBeErasedByAggregateAgreement r ≡ false
unresolvedResidualMayBeErasedByAggregateAgreementIsFalse r = refl

------------------------------------------------------------------------
-- State reconstruction is not yet a validated dynamical digital twin.
------------------------------------------------------------------------

record LocalGroupStateReconstruction : Set where
  constructor localGroupStateReconstruction
  field
    positionStatePresent : Bool
    velocityStatePresent : Bool
    sourceBoundState : Bool
    timeIndexedEvolutionLawPresent : Bool
    gravitationalPotentialValidated : Bool
    dataAssimilationReceiptPresent : Bool

firstLightStateClass : LocalGroupStateReconstruction
firstLightStateClass =
  localGroupStateReconstruction
    true
    true
    true
    false
    false
    false

staticPhaseSpaceImpliesValidatedDynamics : LocalGroupStateReconstruction → Bool
staticPhaseSpaceImpliesValidatedDynamics _ = false

staticPhaseSpaceImpliesValidatedDynamicsIsFalse :
  (s : LocalGroupStateReconstruction) →
  staticPhaseSpaceImpliesValidatedDynamics s ≡ false
staticPhaseSpaceImpliesValidatedDynamicsIsFalse s = refl

renderingImpliesDigitalTwinValidation : LocalGroupStateReconstruction → Bool
renderingImpliesDigitalTwinValidation _ = false

renderingImpliesDigitalTwinValidationIsFalse :
  (s : LocalGroupStateReconstruction) →
  renderingImpliesDigitalTwinValidation s ≡ false
renderingImpliesDigitalTwinValidationIsFalse s = refl
