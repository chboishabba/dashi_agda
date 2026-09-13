module DASHI.Astronomy.LocalGroupObservationFrameProvenanceExact where

open import DASHI.Core.Prelude
open import DASHI.Core.AttributedSourceCore
open import DASHI.Astronomy.LocalGroupVirtualObservatoryFirstLightSourceExact
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Primary-source provenance for the first-light Local Group reconstruction.
--
-- Source publication claims, poster-authored benchmark claims, and later
-- independent DASHI verification are deliberately distinct coordinates.
------------------------------------------------------------------------

mcConnachie2012 : AttributedSource
mcConnachie2012 =
  mkDOISource
    "Alan W. McConnachie"
    "The Observed Properties of Dwarf Galaxies in and around the Local Group"
    "The Astronomical Journal 144(1):4"
    "2012"
    "10.1088/0004-6256/144/1/4"
    "https://doi.org/10.1088/0004-6256/144/1/4"
    academicArticleSource
    "source for the Local Group / nearby-dwarf census and tabulated observational quantities used by the first-light reconstruction"
    publicAttribution

kallivayalil2013 : AttributedSource
kallivayalil2013 =
  mkDOISource
    "Nitya Kallivayalil; Roeland P. van der Marel; Gurtina Besla; Jay Anderson; Charles Alcock"
    "Third-Epoch Magellanic Cloud Proper Motions I: HST/WFC3 Data and Orbit Implications"
    "The Astrophysical Journal 764(2):161"
    "2013"
    "10.1088/0004-637X/764/2/161"
    "https://doi.org/10.1088/0004-637X/764/2/161"
    academicArticleSource
    "primary source for Magellanic-Cloud proper motions and derived Galactocentric velocities used as a frame benchmark"
    publicAttribution

vasilievBelokurovErkal2021 : AttributedSource
vasilievBelokurovErkal2021 =
  mkDOISource
    "Eugene Vasiliev; Vasily Belokurov; Denis Erkal"
    "Tango for three: Sagittarius, LMC, and the Milky Way"
    "Monthly Notices of the Royal Astronomical Society 501(2):2279-2304"
    "2021"
    "10.1093/mnras/staa3673"
    "https://doi.org/10.1093/mnras/staa3673"
    academicArticleSource
    "source for candidate Sagittarius-stream 5D/6D phase-space information and time-dependent LMC/Milky-Way dynamical context"
    publicAttribution

reidBrunthaler2020 : AttributedSource
reidBrunthaler2020 =
  mkDOISource
    "Mark J. Reid; Andreas Brunthaler"
    "The Proper Motion of Sagittarius A*: III. The Case for a Supermassive Black Hole"
    "The Astrophysical Journal 892:39"
    "2020"
    "10.3847/1538-4357/ab76cd"
    "https://doi.org/10.3847/1538-4357/ab76cd"
    academicArticleSource
    "primary VLBA proper-motion source used as an external frame benchmark"
    publicAttribution

localGroupPrimarySourceAtlas : AttributedSourceAtlas
localGroupPrimarySourceAtlas =
  mkSourceAtlas
    "Local Group first-light primary-source atlas"
    "DASHI.Astronomy.LocalGroupObservationFrameProvenanceExact"
    (mcConnachie2012 ∷ kallivayalil2013 ∷ vasilievBelokurovErkal2021 ∷ reidBrunthaler2020 ∷ [])
    "paper identity and scientific-source provenance only; does not promote the poster's reproduction claims to independently verified results"

------------------------------------------------------------------------
-- Typed distinction between observed/tabulated/derived/modelled coordinates.
------------------------------------------------------------------------

data QuantityRole : Set where
  directlyObserved : QuantityRole
  catalogTabulated : QuantityRole
  sourceDerived : QuantityRole
  locallyRecomputed : QuantityRole
  modelConstructed : QuantityRole
  renderedQuantity : QuantityRole

data ClaimStatus : Set where
  sourcePublicationClaim : ClaimStatus
  attributedPosterClaim : ClaimStatus
  independentlyReproduced : ClaimStatus
  unresolvedResidual : ClaimStatus

data BenchmarkKind : Set where
  lmcSixComponent : BenchmarkKind
  sagittariusPhaseSpace : BenchmarkKind
  sgrAProperMotion : BenchmarkKind
  mcConnachieDerivedDistances : BenchmarkKind

record BenchmarkClaim : Set where
  constructor benchmarkClaim
  field
    benchmark : BenchmarkKind
    claimant : String
    claimStatus : ClaimStatus
    claimText : String
    comparisonSource : AttributedSource
    computationArtifact : String
    exactRerunClaim : Bool
    independentDASHIVerification : Bool

open BenchmarkClaim public

lmcPostClaim : BenchmarkClaim
lmcPostClaim =
  benchmarkClaim
    lmcSixComponent
    "Poppie / NOUS — private post 2026-09-07 23:38"
    attributedPosterClaim
    "Galactocentric frame kernel reproduces the Kallivayalil et al. LMC velocity to within 0.03 sigma on all six components"
    kallivayalil2013
    "Virtual Observatory first-light computation; exact underlying run not yet acquired by this formalisation"
    true
    false

sagittariusPostClaim : BenchmarkClaim
sagittariusPostClaim =
  benchmarkClaim
    sagittariusPhaseSpace
    "Poppie / NOUS — private post 2026-09-07 23:38"
    attributedPosterClaim
    "Sagittarius phase space reproduces Vasiliev et al. to the last printed digit"
    vasilievBelokurovErkal2021
    "Virtual Observatory first-light computation; exact underlying run not yet acquired by this formalisation"
    true
    false

sgrAPostClaim : BenchmarkClaim
sgrAPostClaim =
  benchmarkClaim
    sgrAProperMotion
    "Poppie / NOUS — private post 2026-09-07 23:38"
    attributedPosterClaim
    "independently assembled frame agrees with Reid and Brunthaler Sgr A* proper motion at 0.85 sigma"
    reidBrunthaler2020
    "Virtual Observatory first-light computation; exact underlying run not yet acquired by this formalisation"
    true
    false

mcConnachiePostClaim : BenchmarkClaim
mcConnachiePostClaim =
  benchmarkClaim
    mcConnachieDerivedDistances
    "Poppie / NOUS — private post 2026-09-07 23:38"
    attributedPosterClaim
    "recomputing three McConnachie derived-distance columns gives RMS residuals 0.26, 0.30, 0.33 kpc; two columns within +/-0.5 kpc printed precision for 101/101 members and the third for 100/101, with KKH 86 differing by 1.2 kpc"
    mcConnachie2012
    "Virtual Observatory first-light computation; exact row-level producer not yet acquired by this formalisation"
    true
    false

------------------------------------------------------------------------
-- Scientific firewalls: agreement and reproducibility are indexed separately.
------------------------------------------------------------------------

posterClaimImportsIndependentVerification : BenchmarkClaim → Bool
posterClaimImportsIndependentVerification _ = false

posterClaimImportsIndependentVerificationIsFalse :
  (c : BenchmarkClaim) →
  posterClaimImportsIndependentVerification c ≡ false
posterClaimImportsIndependentVerificationIsFalse c = refl

bitForBitRerunImpliesObservationalTruth : BenchmarkClaim → Bool
bitForBitRerunImpliesObservationalTruth _ = false

bitForBitRerunImpliesObservationalTruthIsFalse :
  (c : BenchmarkClaim) →
  bitForBitRerunImpliesObservationalTruth c ≡ false
bitForBitRerunImpliesObservationalTruthIsFalse c = refl

frameAgreementImpliesDynamicalModelCorrectness : Bool
frameAgreementImpliesDynamicalModelCorrectness = false

frameAgreementImpliesDynamicalModelCorrectnessIsFalse :
  frameAgreementImpliesDynamicalModelCorrectness ≡ false
frameAgreementImpliesDynamicalModelCorrectnessIsFalse = refl

catalogMembershipImpliesIndependentConfirmation : Bool
catalogMembershipImpliesIndependentConfirmation = false

catalogMembershipImpliesIndependentConfirmationIsFalse :
  catalogMembershipImpliesIndependentConfirmation ≡ false
catalogMembershipImpliesIndependentConfirmationIsFalse = refl

derivedCoordinateImpliesDirectMeasurement : Bool
derivedCoordinateImpliesDirectMeasurement = false

derivedCoordinateImpliesDirectMeasurementIsFalse :
  derivedCoordinateImpliesDirectMeasurement ≡ false
derivedCoordinateImpliesDirectMeasurementIsFalse = refl
