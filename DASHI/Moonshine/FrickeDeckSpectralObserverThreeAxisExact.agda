module DASHI.Moonshine.FrickeDeckSpectralObserverThreeAxisExact where

------------------------------------------------------------------------
-- THREE INDEPENDENT OBSERVER AXES ON THE MARKED MOONSHINE CARRIER
--
--  (1) coarse Fricke/Frobenius selector geometry;
--  (2) marked deck representation type;
--  (3) marked scalar Hecke/Frobenius spectral coordinate.
--
-- FrickeSelectorDeckObserverIncomparabilityExact already proves axes (1) and
-- (2) are incomparable.  This file proves their PRODUCT still cannot determine
-- axis (3), using two explicit source-native p=37 standard-deck eigenmodes.
--
-- Both modes live in the same standard S3 isotypic block and therefore share:
--
--   coarse Frobenius pair defect = 1,
--   deck type = standard.
--
-- But their exact scalar joint spectra differ:
--
--   mode A: (T3,T5,F) = ( 1, 0,+1),
--   mode B: (T3,T5,F) = (-3,-2,-1).
--
-- Consequently neither the coarse Ogg/Fricke selector nor the deck irrep label,
-- nor their product, recovers the spectral/multiplicity coordinate.  The three
-- axes have distinct consumer roles and must not be flattened into one slogan.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Rational using (_/_; -_)

import DASHI.Moonshine.P37MarkedDeckIsotypicJointDecompositionExact as Iso
import DASHI.Moonshine.P37MarkedDeckIsotypicCollisionExact as Collision
import DASHI.Moonshine.P11P37MarkedDeckSelectorCutsetExact as Cutset
import DASHI.Moonshine.FrickeSelectorDeckObserverIncomparabilityExact as Axes

------------------------------------------------------------------------
-- Existing standard mode A: eigenpacket (1,0,+1).
------------------------------------------------------------------------

standardModeA : Iso.StdBlock3
standardModeA = Collision.p37StandardCollisionVector

standardModeAT3 : Iso.standardT3 standardModeA ≡ standardModeA
standardModeAT3 = Collision.p37StandardT3EigenOne

standardModeAT5 :
  Iso.standardT5 standardModeA
  ≡ Iso.stdBlock3
      (Iso.std2 (+ 0 / 1) (+ 0 / 1))
      (Iso.std2 (+ 0 / 1) (+ 0 / 1))
      (Iso.std2 (+ 0 / 1) (+ 0 / 1))
standardModeAT5 = Collision.p37StandardT5EigenZero

standardModeAF : Iso.standardF standardModeA ≡ standardModeA
standardModeAF = Collision.p37StandardFrobeniusEven

------------------------------------------------------------------------
-- New explicit standard mode B: eigenpacket (-3,-2,-1).
------------------------------------------------------------------------

standardModeB : Iso.StdBlock3
standardModeB =
  Iso.stdBlock3
    (Iso.std2 (+ 3 / 1) (+ 0 / 1))
    (Iso.std2 (- (+ 1 / 1)) (- (+ 1 / 1)))
    (Iso.std2 (+ 1 / 1) (+ 1 / 1))

standardModeBT3 :
  Iso.standardT3 standardModeB
  ≡ Iso.stdBlock3
      (Iso.std2 (- (+ 9 / 1)) (+ 0 / 1))
      (Iso.std2 (+ 3 / 1) (+ 3 / 1))
      (Iso.std2 (- (+ 3 / 1)) (- (+ 3 / 1)))
standardModeBT3 = refl

standardModeBT5 :
  Iso.standardT5 standardModeB
  ≡ Iso.stdBlock3
      (Iso.std2 (- (+ 6 / 1)) (+ 0 / 1))
      (Iso.std2 (+ 2 / 1) (+ 2 / 1))
      (Iso.std2 (- (+ 2 / 1)) (- (+ 2 / 1)))
standardModeBT5 = refl

standardModeBF :
  Iso.standardF standardModeB
  ≡ Iso.stdBlock3
      (Iso.std2 (- (+ 3 / 1)) (+ 0 / 1))
      (Iso.std2 (+ 1 / 1) (+ 1 / 1))
      (Iso.std2 (- (+ 1 / 1)) (- (+ 1 / 1)))
standardModeBF = refl

------------------------------------------------------------------------
-- Exact scalar fingerprints.
------------------------------------------------------------------------

record ScalarSpectrum : Set where
  constructor scalarSpectrum
  field
    t3 t5 frobenius : ℤ
open ScalarSpectrum public

spectrumA spectrumB : ScalarSpectrum
spectrumA = scalarSpectrum (+ 1) (+ 0) (+ 1)
spectrumB = scalarSpectrum (-[1+ 2 ]) (-[1+ 1 ]) (-[1+ 0 ])

spectraDiffer : spectrumA ≡ spectrumB → ⊥
spectraDiffer ()

------------------------------------------------------------------------
-- Same selector + same deck type for both modes.
------------------------------------------------------------------------

data StandardModeChoice : Set where
  modeA modeB : StandardModeChoice

selectorDeckObservation : StandardModeChoice → Axes.SelectorDeckObservation
selectorDeckObservation modeA =
  Axes.selectorDeck Cutset.p37CoarseFrobeniusPairDefect Axes.deckStandard
selectorDeckObservation modeB =
  Axes.selectorDeck Cutset.p37CoarseFrobeniusPairDefect Axes.deckStandard

scalarSpectrumObservation : StandardModeChoice → ScalarSpectrum
scalarSpectrumObservation modeA = spectrumA
scalarSpectrumObservation modeB = spectrumB

sameSelectorDeckObservation :
  selectorDeckObservation modeA ≡ selectorDeckObservation modeB
sameSelectorDeckObservation = refl

SelectorDeckDeterminesSpectrum : Set
SelectorDeckDeterminesSpectrum =
  Σ (Axes.SelectorDeckObservation → ScalarSpectrum)
    (λ decode →
      (x : StandardModeChoice) →
      decode (selectorDeckObservation x) ≡ scalarSpectrumObservation x)

selectorDeckCannotDetermineSpectrum : SelectorDeckDeterminesSpectrum → ⊥
selectorDeckCannotDetermineSpectrum (decode , factors) =
  spectraDiffer
    (trans
      (sym (factors modeA))
      (trans
        (cong decode sameSelectorDeckObservation)
        (factors modeB)))

------------------------------------------------------------------------
-- Full role product retains all three coordinates on this witness family.
------------------------------------------------------------------------

record ThreeAxisObservation : Set where
  constructor threeAxis
  field
    selectorDeck : Axes.SelectorDeckObservation
    spectrum : ScalarSpectrum
open ThreeAxisObservation public

threeAxisObservation : StandardModeChoice → ThreeAxisObservation
threeAxisObservation x =
  threeAxis (selectorDeckObservation x) (scalarSpectrumObservation x)

threeAxisSeparatesModes :
  threeAxisObservation modeA ≡ threeAxisObservation modeB → ⊥
threeAxisSeparatesModes ()

record FrickeDeckSpectralObserverThreeAxisBoundary : Set where
  field
    coarseSelectorAxisRetained : Bool
    deckRepresentationAxisRetained : Bool
    scalarSpectralAxisRetained : Bool
    selectorDeckProductDeterminesSpectrum : Bool
    threeAxisProductSeparatesWitnessModes : Bool
    standardBlockMultiplicityCollapsedToDeckLabel : Bool
    finiteOggTableUsed : Bool

canonicalFrickeDeckSpectralObserverThreeAxisBoundary :
  FrickeDeckSpectralObserverThreeAxisBoundary
canonicalFrickeDeckSpectralObserverThreeAxisBoundary = record
  { coarseSelectorAxisRetained = true
  ; deckRepresentationAxisRetained = true
  ; scalarSpectralAxisRetained = true
  ; selectorDeckProductDeterminesSpectrum = false
  ; threeAxisProductSeparatesWitnessModes = true
  ; standardBlockMultiplicityCollapsedToDeckLabel = false
  ; finiteOggTableUsed = false
  }
