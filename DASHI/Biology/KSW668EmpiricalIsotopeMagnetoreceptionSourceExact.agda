module DASHI.Biology.KSW668EmpiricalIsotopeMagnetoreceptionSourceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AvianMagnetoreceptionSourceRegistry as AvianSource
import DASHI.Biology.AvianHepaticMacrophageMagnetoreception as Hepatic
import DASHI.Physics.Plasma.KSW668FiniteDiscriminatorsExact as Finite

------------------------------------------------------------------------
-- KSW 668 new empirical acquisition — SOURCE-BOUNDED typed consumer.
-- Source identities:
--   Lisowski et al., Science 392, 985-991 (2026),
--   DOI 10.1126/science.ady2486; ENA PRJEB98986.
--   Hua et al., Radiocarbon 64, 723-745 (2022),
--   DOI 10.1017/RDC.2021.95; rintcal git blob
--   22ef8d05b8ca09d71f5b1582206a4c92304674e6.
--   Kattnig (2026), DOI 10.1098/rsif.2026.0332:
--   competing theoretical information bound, not an experiment.
--
-- Original author reports are kept distinct from secondary extraction,
-- model evaluation, physical mechanism and medical/isotope causality.
------------------------------------------------------------------------

data EvidenceRole : Set where
  originalPublishedInterventionSummary
  publicOriginalArchiveRegistration
  independentReanalysisOfPublishedNumbers
  physicalModelCounterexample
  notAcquired : EvidenceRole

record PublishedHomingGroup : Set where
  constructor published-homing-group
  field
    source : String
    context : String
    numberPigeons : Nat
    numberHomedSameDay : Nat
    evidenceRole : EvidenceRole

open PublishedHomingGroup public

pigeonControl : PublishedHomingGroup
pigeonControl = published-homing-group
  "Lisowski et al. Science 2026 DOI 10.1126/science.ady2486"
  "19 km pigeon release, complete overcast, control liposomes"
  16 16 originalPublishedInterventionSummary

pigeonDepleted : PublishedHomingGroup
pigeonDepleted = published-homing-group
  "Lisowski et al. Science 2026 DOI 10.1126/science.ady2486"
  "19 km pigeon release, complete overcast, clodronate-treated"
  18 0 originalPublishedInterventionSummary

publishedOvercastTotal :
  numberPigeons pigeonControl + numberPigeons pigeonDepleted ≡ 34
publishedOvercastTotal = refl

publishedControlHomed :
  numberHomedSameDay pigeonControl ≡ 16
publishedControlHomed = refl

publishedDepletedHomed :
  numberHomedSameDay pigeonDepleted ≡ 0
publishedDepletedHomed = refl

-- Reuse the existing source owner rather than retyping its published claims.
originalAvianMacrophageSource : AvianSource.AvianMagnetoreceptionSource
originalAvianMacrophageSource = AvianSource.lisowskiEtAl2026

originalAvianMacrophageStage :
  Hepatic.HepaticMacrophageMagnetoreceptionReceipt
originalAvianMacrophageStage =
  Hepatic.canonicalHepaticMacrophageMagnetoreceptionReceipt

record BiologicalArchiveAcquisition : Set where
  constructor biological-archive-acquisition
  field
    sourceName sourceDOI accession sourceGitBlob : String
    sourceRole : EvidenceRole
    originalRawSampleBytesImported : Bool
    sameHumanEmotionInterventionAvailable : Bool
    sameSpecimenCarbon14NuclearFluxAvailable : Bool

originalPigeonTranscriptomeRegistration : BiologicalArchiveAcquisition
originalPigeonTranscriptomeRegistration = biological-archive-acquisition
  "Lisowski et al. liver MHCII+ 3-prime mRNA pigeon experiment"
  "10.1126/science.ady2486"
  "PRJEB98986 / NCBI BioProject 1489155 / one SRA experiment"
  "not applicable to ENA registration"
  publicOriginalArchiveRegistration false false false

originalSouthernPostbombAcquisition : BiologicalArchiveAcquisition
originalSouthernPostbombAcquisition = biological-archive-acquisition
  "Hua et al. 1950-2019 annual Southern Hemisphere zones 1–2 14C"
  "10.1017/RDC.2021.95"
  "Maarten14C/rintcal:inst/extdata/postbomb_SH1-2.14C"
  "22ef8d05b8ca09d71f5b1582206a4c92304674e6"
  publicOriginalArchiveRegistration false false false

------------------------------------------------------------------------
-- Finite identifiability counterexample reused, not an empirical human
-- causal-exclusion theorem.  Neither the pigeon homing counts nor
-- atmospheric 14C curve is a within-person nuclear intervention.
------------------------------------------------------------------------

sameIsotopeObservationCannotSelectNuclearCause :
  (classifier : Finite.IsotopeTrace → Finite.Mechanism) →
  classifier (Finite.trace Finite.redistributionWorld)
    ≡ Finite.metabolicRedistribution →
  classifier (Finite.trace Finite.nuclearWorld)
    ≡ Finite.nuclearConversion →
  Finite.⊥
sameIsotopeObservationCannotSelectNuclearCause =
  Finite.emotionIsotopeCausalIdentificationNoGo
