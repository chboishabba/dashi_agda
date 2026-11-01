module Ontology.DNA.ChemistrySheetCodecCompletionRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

open import Ontology.DNA.NonDegenerateChemistrySheetTower using
  (ChemistryLevel; block256; analyse; summaryAt256; reconstructs)
open import Ontology.DNA.SantaLucia1998Thermodynamics using
  (WatsonCrickStack; AA-TT; GC-CG; unified1998; negativeScaled;
   ThermodynamicTriple)
open import Ontology.DNA.ChemistryAdaptiveReferenceCodec using
  (trit-channel-roundtrip; tritRateExactlyTwoBases)
open import Ontology.DNA.ChemistryTernaryQuantizer using (minus; neutral; plus)
open import Ontology.DNA.PublishedChemistryAssayReceipts using
  (ExternalEvidenceBoundary; externalEvidenceBoundary)
open import Ontology.DNA.FixedPointTernaryAndTetration using
  (tetrate; four-height-two)

AA-TT-regression :
  ThermodynamicTriple.deltaG37-kcal-times100 (unified1998 AA-TT) ≡ negativeScaled 100
AA-TT-regression = refl

GC-CG-regression :
  ThermodynamicTriple.deltaG37-kcal-times100 (unified1998 GC-CG) ≡ negativeScaled 224
GC-CG-regression = refl

minus-roundtrip-regression = trit-channel-roundtrip minus
neutral-roundtrip-regression = trit-channel-roundtrip neutral
plus-roundtrip-regression = trit-channel-roundtrip plus

minus-rate-regression = tritRateExactlyTwoBases minus

aggregate-evidence-present :
  ExternalEvidenceBoundary.aggregateReceiptsPresent externalEvidenceBoundary ≡ true
aggregate-evidence-present = refl

sequence-level-reanalysis-not-claimed :
  ExternalEvidenceBoundary.sequenceLevelSufficiencyReanalysed externalEvidenceBoundary ≡ false
sequence-level-reanalysis-not-claimed = refl

tetration-4-height-2-regression : tetrate 4 (suc (suc zero)) ≡ 256
tetration-4-height-2-regression = four-height-two
