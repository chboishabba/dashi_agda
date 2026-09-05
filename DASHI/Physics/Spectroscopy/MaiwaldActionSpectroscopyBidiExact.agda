module DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.FiniteObservationClosureBidiExact as Closure

-- JPL SURP 2023: messenger photodissociation action spectroscopy for
-- discriminating biomarkers from structural isomers using cryogenic trapping
-- and coherent radiation from mid-IR through UV.

data SpectralObject : Set where biomarker structuralIsomer messengerTaggedComplex : SpectralObject

data SpectralStage : Set where ionise cryogenicTrap irradiate photodissociate detectFragments inferIdentity : SpectralStage

record ActionSpectroscopyExperiment : Set where
  constructor action-spectroscopy-experiment
  field
    target : SpectralObject
    trapMinimumK trapMaximumK : ℕ
    sourceReference : String

open ActionSpectroscopyExperiment public

maiwaldSURP : ActionSpectroscopyExperiment
maiwaldSURP = action-spectroscopy-experiment messengerTaggedComplex 10 300
  "JPL FY23 SURP: Unambiguous Detection of Biosignatures by Action Spectroscopy; PI Frank Maiwald"

record ActionSpectroscopyBoundary : Set where
  constructor action-spectroscopy-boundary
  field
    massMatchAloneProvesMolecularIdentity : Bool
    massMatchAloneProvesMolecularIdentityIsFalse : massMatchAloneProvesMolecularIdentity ≡ false
    structuralIsomersNeedNotShareActionSpectrum : Bool
    structuralIsomersNeedNotShareActionSpectrumIsTrue : structuralIsomersNeedNotShareActionSpectrum ≡ true
    actionSignalIsDirectAbsorptionSpectrum : Bool
    actionSignalIsDirectAbsorptionSpectrumIsFalse : actionSignalIsDirectAbsorptionSpectrum ≡ false
    detectedFragmentAutomaticallyProvesBiosignature : Bool
    detectedFragmentAutomaticallyProvesBiosignatureIsFalse : detectedFragmentAutomaticallyProvesBiosignature ≡ false

canonicalActionSpectroscopyBoundary : ActionSpectroscopyBoundary
canonicalActionSpectroscopyBoundary = action-spectroscopy-boundary false refl true refl false refl false refl

maiwaldReverseIdentity : Closure.ReverseClosureObligation
maiwaldReverseIdentity = Closure.reverse-closure-obligation
  "messenger photodissociation action spectroscopy"
  "fragment-yield versus irradiation frequency"
  "reference-spectrum / structural-isomer discrimination receipt"
  "molecular-identity assignment"
  "biological origin or life detection by itself"
