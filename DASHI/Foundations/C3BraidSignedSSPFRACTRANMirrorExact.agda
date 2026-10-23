module DASHI.Foundations.C3BraidSignedSSPFRACTRANMirrorExact where

-- Reuses actual SSP signed arithmetic and C3 balanced-sheet reflection.
-- Product involution is real theorem content, not a claim that arithmetic
-- negation is identical to geometric reflection or physical KK charge.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Moonshine.Monster369SignedSSPTauInversionSeamExact as Seam
import DASHI.Moonshine.JInvariant369SignedSSPFRACTRANPhaseFibreExact as Phase
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Foundations.C3NineSiteAlternatingOrbitExact as Orbit
import DASHI.Foundations.C3NineSiteSixStepMirrorExact as Mirror

record SiteSignedState : Set where
  constructor site-signed
  field
    site : Orbit.Site
    multiplicity : SSP.SignedMultiplicity
open SiteSignedState public

invert : SiteSignedState → SiteSignedState
invert (site-signed s m) =
  site-signed (Mirror.mirror s) (SSP.negateMultiplicity m)

invertTwice : ∀ x → invert (invert x) ≡ x
invertTwice (site-signed s m)
  rewrite Mirror.mirror² s | Seam.signedNegationInvolutive m = refl

spectralObservation : SiteSignedState → Spectral.AxisFrequency
spectralObservation x = Phase.signedSSPPhaseObserver (multiplicity x)

spectralInversion :
  ∀ x → spectralObservation (invert x) ≡
         Spectral.conjugateFrequency (spectralObservation x)
spectralInversion (site-signed s m) =
  Phase.signedSSPNegationIsSpectralConjugation m

sampledSixStep :
  ∀ t m → invert (site-signed (Orbit.orbit t) m) ≡
    site-signed (Orbit.orbit (Mirror.shift6 t)) (SSP.negateMultiplicity m)
sampledSixStep t m rewrite Mirror.sixStepMirror t = refl
