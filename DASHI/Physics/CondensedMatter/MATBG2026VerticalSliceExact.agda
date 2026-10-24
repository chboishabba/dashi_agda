module DASHI.Physics.CondensedMatter.MATBG2026VerticalSliceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using ([]; _∷_)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact as Twistronics

------------------------------------------------------------------------
-- 2026 MATBG VERTICAL SLICE
--
-- Source-bounded physical facts are separated from DASHI carrier structure.
-- In particular the QTM and entropy experiments are different devices/samples;
-- common MATBG material class does not create a same-sample receipt.
------------------------------------------------------------------------

xiao2026QTMSource : Attribution.AttributedSource
xiao2026QTMSource =
  Attribution.mkDOISource
    "J. Xiao, A. Inbar, J. Birkbeck et al."
    "Imaging the flat bands of magic-angle graphene reshaped by interactions"
    "Nature 653, 68-75"
    "2026"
    "10.1038/s41586-026-10378-x"
    "https://doi.org/10.1038/s41586-026-10378-x"
    Attribution.academicArticleSource
    "source for QTM momentum/energy-resolved MATBG bands, the reported 1.10 degree local twist, time-reversal-related K/K' spectral superposition in the reported setup, interaction-driven magic-angle band reconstruction, light/heavy momentum sectors, and the reported best-fit BM wavefunction matrix-element ratio w0/w1 = 0.6; does not establish a DASHI C3 codec or an entropy experiment on the same sample"
    Attribution.publicAttribution

zhang2026EntropySource : Attribution.AttributedSource
zhang2026EntropySource =
  Attribution.mkDOISource
    "Zhenyuan Zhang, Shuang Wu, Dumitru Calugaru et al."
    "Entropy plateaus, combinatorial degeneracy, local moments, and heavy-fermion mass renormalization in magic-angle graphene"
    "Nature Communications 17, 9785"
    "2026"
    "10.1038/s41467-026-76179-y"
    "https://doi.org/10.1038/s41467-026-76179-y"
    Attribution.academicArticleSource
    "source for planar-tunnelling inverse-compressibility/entropy spectroscopy, 4-fold and 8-fold plateau degeneracies, mass renormalization, and the source interpretation that the 8-to-4 reduction is consistent with strain-mediated symmetry breaking; not the QTM sample"
    Attribution.publicAttribution

carrasco2026TwistrainSource : Attribution.AttributedSource
carrasco2026TwistrainSource =
  Attribution.mkDOISource
    "Roberto Carrasco, Federico Escudero, Zhen Zhan et al."
    "Twist and Strain in Square Moire Patterns of Stacked Graphene Layers"
    "Physical Review Letters 136, 196102"
    "2026"
    "10.1103/kzfc-39kv"
    "https://doi.org/10.1103/kzfc-39kv"
    Attribution.academicArticleSource
    "source for controlled strain-induced trigonal-to-square moire reconstruction and correlated narrow-band spectroscopy in stacked graphene; it supports twist-plus-strain as a real geometry control but is not the same MATBG sample as either QTM or entropy spectroscopy"
    Attribution.publicAttribution

matbg2026SourceAtlas : Attribution.AttributedSourceAtlas
matbg2026SourceAtlas =
  Attribution.mkSourceAtlas
    "MATBG 2026 source-bounded vertical slice"
    "DASHI.Physics.CondensedMatter.MATBG2026VerticalSliceExact"
    (Twistronics.bistritzerMacDonald2011 ∷
     xiao2026QTMSource ∷
     zhang2026EntropySource ∷
     carrasco2026TwistrainSource ∷ [])
    "Bistritzer-MacDonald supplies the continuum-model theory role; Xiao et al. supply QTM band-imaging and matrix-element-comparison facts; Zhang et al. supply entropy/compressibility facts; Carrasco et al. supply controlled twist-strain geometry facts. DASHI owns the typed composition and non-collapse boundaries."

------------------------------------------------------------------------
-- Literal internal carrier.
------------------------------------------------------------------------

data Valley : Set where
  K KPrime : Valley

data Layer : Set where
  topLayer bottomLayer : Layer

data Sublattice : Set where
  sublatticeA sublatticeB : Sublattice

data Spin : Set where
  spinUp spinDown : Spin

record MATBGBasisState : Set where
  constructor matbg-basis-state
  field
    valley : Valley
    layer : Layer
    sublattice : Sublattice
    spin : Spin

open MATBGBasisState public

timeReverseValley : Valley → Valley
timeReverseValley K = KPrime
timeReverseValley KPrime = K

timeReverseValleyInvolutive :
  (v : Valley) → timeReverseValley (timeReverseValley v) ≡ v
timeReverseValleyInvolutive K = refl
timeReverseValleyInvolutive KPrime = refl

------------------------------------------------------------------------
-- Candidate valley-only C3 chart.
------------------------------------------------------------------------

candidateValleyPhase : Valley → C3.C3Phase
candidateValleyPhase K = C3.phase1
candidateValleyPhase KPrime = C3.phase2

timeReversalConjugatesCandidateValleyPhase :
  (v : Valley) →
  candidateValleyPhase (timeReverseValley v)
    ≡ C3.conjugatePhase (candidateValleyPhase v)
timeReversalConjugatesCandidateValleyPhase K = refl
timeReversalConjugatesCandidateValleyPhase KPrime = refl

record ValleyC3RepresentationBoundary : Set where
  constructor valley-c3-representation-boundary
  field
    literalValleyCarrierPresent : Bool
    exactC3CarrierPresent : Bool
    timeReversalConjugationFixturePresent : Bool
    valleyOnlyPhaseChartIsFullBMBasisRepresentation : Bool
    sublatticeRepresentationConventionPaid : Bool
    layerRepresentationConventionPaid : Bool
    sameObjectPhysicalC3IdentificationPaid : Bool

open ValleyC3RepresentationBoundary public

canonicalValleyC3RepresentationBoundary : ValleyC3RepresentationBoundary
canonicalValleyC3RepresentationBoundary =
  valley-c3-representation-boundary
    true true true false false false false

------------------------------------------------------------------------
-- Source-bounded 2026 observations.
------------------------------------------------------------------------

record QTMObservation : Set where
  constructor qtm-observation
  field
    qtmMagicAngleHundredths : Nat
    qtmMagicAngleUncertaintyHundredths : Nat
    qtmBestFitW0W1Hundredths : Nat
    interactionReshapedMagicAngleBands : Bool
    lightAndHeavyMomentumSectors : Bool
    singleParticleAgreementAwayFromMagicAngle : Bool
    timeReversalValleySuperposition : Bool
    tunnellingMatrixElementModelComparisonReported : Bool
    observationReference : String

open QTMObservation public

xiao2026QTMObservation : QTMObservation
xiao2026QTMObservation =
  qtm-observation
    110
    2
    60
    true
    true
    true
    true
    true
    "Xiao et al. Nature 653 (2026), DOI 10.1038/s41586-026-10378-x; local QTM region reported at 1.10 +/- 0.02 degrees and wavefunction matrix-element comparison reported best agreement for w0/w1 = 0.6"

record EntropyObservation : Set where
  constructor entropy-observation
  field
    entropySampleTwistHundredths : Nat
    entropySampleTwistUncertaintyHundredths : Nat
    lowPlateauTemperatureKelvin : Nat
    highPlateauTemperatureKelvin : Nat
    lowTemperatureDegeneracy : Nat
    highTemperatureDegeneracy : Nat
    inverseCompressibilityMeasured : Bool
    entropyExtractedFromTemperatureDependentChemicalPotential : Bool
    massRenormalizationReported : Bool
    strainMediatedSymmetryBreakingInterpretation : Bool
    observationReference : String

open EntropyObservation public

zhang2026EntropyObservation : EntropyObservation
zhang2026EntropyObservation =
  entropy-observation
    106
    2
    10
    20
    4
    8
    true
    true
    true
    true
    "Zhang et al. Nature Communications 17, 9785 (2026), DOI 10.1038/s41467-026-76179-y"

record BMContinuumContract : Set where
  constructor bm-continuum-contract
  field
    theoryReference : String
    layerSublatticeContinuumBasisRequired : Bool
    valleyResolvedContinuumModelRequired : Bool
    twistAngleIsControlParameter : Bool
    tunnellingParametersRequired : Bool
    singleParticleTheoryRole : Bool
    interactingSelfEnergyIncludedByOriginalBMModel : Bool

open BMContinuumContract public

canonicalBMContinuumContract : BMContinuumContract
canonicalBMContinuumContract =
  bm-continuum-contract
    "Bistritzer and MacDonald 2011, DOI 10.1073/pnas.1108174108"
    true true true true true false

record MATBG2026VerticalSlice : Set where
  constructor matbg-2026-vertical-slice
  field
    bmContract : BMContinuumContract
    qtmObservation : QTMObservation
    entropyObservation : EntropyObservation
    sameMaterialClassPaid : Bool
    sameSampleQTMEntropyPaid : Bool
    bmSingleParticleExplainsInteractingMagicAngleSpectrum : Bool
    valleyC3SameObjectRepresentationPaid : Bool
    quantumMetricSameObjectPaid : Bool
    entropyToUsefulCaloricCyclePaid : Bool

open MATBG2026VerticalSlice public

canonicalMATBG2026VerticalSlice : MATBG2026VerticalSlice
canonicalMATBG2026VerticalSlice =
  matbg-2026-vertical-slice
    canonicalBMContinuumContract
    xiao2026QTMObservation
    zhang2026EntropyObservation
    true
    false
    false
    false
    false
    false

record MATBG2026VerticalBoundary : Set where
  constructor matbg-2026-vertical-boundary
  field
    sourceClassCompositionDoesNotCreateSameSample : Bool
    qtmValleySuperpositionDoesNotEraseLiteralValleyCarrier : Bool
    interactingQTMDoesNotRetroactivelyUpgradeBM2011 : Bool
    w0W1RatioFitDoesNotPayAbsoluteTunnellingScale : Bool
    entropyPlateauDoesNotByItselfProveRefrigeration : Bool
    strainInterpretationDoesNotIdentifyAllMicroscopicMechanisms : Bool
    squareMoireSourceDoesNotBecomeMATBGSameSampleEvidence : Bool

open MATBG2026VerticalBoundary public

canonicalMATBG2026VerticalBoundary : MATBG2026VerticalBoundary
canonicalMATBG2026VerticalBoundary =
  matbg-2026-vertical-boundary true true true true true true true
