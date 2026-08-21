module DASHI.Biology.ConsciousAccessWaveSourceRegistry where

------------------------------------------------------------------------
-- Source registry for the wave-control / symmetry-resolved access tranche.
--
-- These rows calibrate empirical and mathematical neighbourhoods.  They do
-- not import empirical findings as Agda theorems and do not authorize a
-- phenomenal-consciousness, clinical, or Monster interpretation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data SourceRole : Set where
  analogWaveControlRole : SourceRole
  ephapticCouplingRole : SourceRole
  travelingWaveGeometryRole : SourceRole
  travelingWaveMechanismReviewRole : SourceRole
  quaternionTimeFrequencyRole : SourceRole
  anesthesiaPhaseAlignmentRole : SourceRole

record WaveSource : Set where
  constructor waveSource
  field
    authors : String
    title : String
    publication : String
    year : Nat
    doi : String
    role : SourceRole
    importedReading : String
    excludedPromotion : String

open WaveSource public

millerBrincatRoySource : WaveSource
millerBrincatRoySource =
  waveSource
    "Earl K. Miller; Scott L. Brincat; Jefferson E. Roy"
    "Analog Cognition and Consciousness"
    "PsyArXiv preprint, version 3"
    2026
    "10.31234/osf.io/z48x7_v3"
    analogWaveControlRole
    "Motivates fast wave-mediated control, analog interference, mixed-selectivity routing, and an access-consciousness candidate bridge."
    "The review explicitly motivates empirical tests; it is not imported as proof that analog wave computation or phenomenal consciousness has been established."

pinotsisMillerSource : WaveSource
pinotsisMillerSource =
  waveSource
    "Dimitris A. Pinotsis; Earl K. Miller"
    "Ephaptic coupling can explain variability in neural activity"
    "Cerebral Cortex"
    2026
    "10.1093/cercor/bhag098"
    ephapticCouplingRole
    "Motivates a bidirectional field/neuron causal lane and trial-varying field-control strength."
    "Ephaptic influence is not promoted as the universal generator of neural traveling waves or a standalone consciousness mechanism."

dasZabehErmentroutJacobsSource : WaveSource
dasZabehErmentroutJacobsSource =
  waveSource
    "Anup Das; Erfan Zabeh; Bard Ermentrout; Joshua Jacobs"
    "Planar, spiral, and concentric traveling waves distinguish behavioral states in human memory"
    "Nature Communications"
    2026
    "10.1038/s41467-026-71386-z"
    travelingWaveGeometryRole
    "Motivates separating planar, rotational/spiral, source/sink, and complex propagation geometry rather than treating all waves as circular or toroidal."
    "The finite DASHI div/curl witnesses are not claimed to reconstruct the authors' cortical measurements or classifier."

mullerBuschDavisReynoldsSource : WaveSource
mullerBuschDavisReynoldsSource =
  waveSource
    "Lyle Muller; Alexandra N. Busch; Zachary W. Davis; John H. Reynolds"
    "Neural traveling waves in cortex: Network mechanisms and potential roles in neural computation"
    "Neuron"
    2026
    "10.1016/j.neuron.2026.06.019"
    travelingWaveMechanismReviewRole
    "Motivates spatiotemporal computation by traveling waves and keeps circuit-generated mechanisms distinct from any single field-level mechanism."
    "Traveling-wave computation is not collapsed to ephaptic coupling, one frequency band, or one cortical geometry."

flamantLeBihanChainaisSource : WaveSource
flamantLeBihanChainaisSource =
  waveSource
    "Julien Flamant; Nicolas Le Bihan; Pierre Chainais"
    "Time-frequency analysis of bivariate signals"
    "Applied and Computational Harmonic Analysis"
    2019
    "10.1016/j.acha.2017.05.007"
    quaternionTimeFrequencyRole
    "Motivates using quaternion-valued coefficients to retain time-frequency structure together with geometry/polarization information."
    "Quaternion orientation is not substituted for Fourier or representation-mode extraction."

bardonEtAlSource : WaveSource
bardonEtAlSource =
  waveSource
    "Alexandra G. Bardon; Jesus J. Ballesteros; Scott L. Brincat; Jefferson E. Roy; Meredith K. Mahnke; Yumiko Ishizawa; Emery N. Brown; Earl K. Miller"
    "Convergent effects of different anesthetics on changes in phase alignment of cortical oscillations"
    "Cell Reports"
    2025
    "10.1016/j.celrep.2025.115685"
    anesthesiaPhaseAlignmentRole
    "Motivates phase-organization perturbation as an empirical discriminator across anesthetics with different molecular actions."
    "Phase alignment is not promoted as a unique or sufficient consciousness biomarker."

canonicalWaveSources : List WaveSource
canonicalWaveSources =
  millerBrincatRoySource
  ∷ pinotsisMillerSource
  ∷ dasZabehErmentroutJacobsSource
  ∷ mullerBuschDavisReynoldsSource
  ∷ flamantLeBihanChainaisSource
  ∷ bardonEtAlSource
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalWaveSourceCount : Nat
canonicalWaveSourceCount = listCount canonicalWaveSources

canonicalWaveSourceCountIsSix : canonicalWaveSourceCount ≡ 6
canonicalWaveSourceCountIsSix = refl
