module DASHI.Biology.IBSHistamineH1InterventionUpdateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

decraecker2024Source : Source.AttributedSource
decraecker2024Source = Source.mkDOISource
  "Lisse Decraecker; Danny De Looze; David P Hirsch; Heiko De Schepper; Joris Arts; Philip Caenepeel; Albert J Bredenoord; Jeroen Kolkman; Koen Bellens; Kim Van Beek; Fedrica Pia; Willy Peetermans; Tim Vanuytsel; Alexandre Denadai-Souza; Ann Belmans; Guy Boeckxstaens"
  "Treatment of non-constipated irritable bowel syndrome with the histamine 1 receptor antagonist ebastine: a randomised, double-blind, placebo-controlled trial"
  "Gut 73(3):459-469" "2024"
  "10.1136/gutjnl-2023-331634" "https://doi.org/10.1136/gutjnl-2023-331634"
  Source.academicArticleSource
  "Pays a multicentre randomized placebo-controlled phase-2 H1-antagonist intervention in non-constipated IBS. The composite GRS+API responder endpoint favored ebastine; the individual GRS and API responder endpoints did not reach conventional statistical significance."
  Source.publicAttribution

pia2026Source : Source.AttributedSource
pia2026Source = Source.mkDOISource
  "Fedrica Pia; Lisse Decraecker; Danny De Looze; David Hirsch; Heiko De Schepper; Joris Arts; Philip Caenepeel; Albert J Bredenoord; Tim Vanuytsel; Ann Belmans; Guy E Boeckxstaens"
  "Dose-Dependent Effect of the Histamine 1 Receptor Antagonist Ebastine in Patients With Non-Constipated Irritable Bowel Syndrome"
  "Neurogastroenterology & Motility 38(1):e70242" "2026"
  "10.1111/nmo.70242" "https://doi.org/10.1111/nmo.70242"
  Source.academicArticleSource
  "Pays an open-label comparison of ebastine 40 mg versus 20 mg reporting more abdominal-pain responders and reduced diarrhea severity at the higher dose. It is not a randomized placebo-controlled dose trial."
  Source.publicAttribution

data InterventionDesign : Set where
  randomizedDoubleBlindPlaceboControlled : InterventionDesign
  openLabelDoseComparison : InterventionDesign

record H1InterventionReceipt : Set where
  constructor h1-intervention-receipt
  field source : Source.AttributedSource
        design : InterventionDesign
        nonConstipatedIBSPopulation : Bool
        H1AntagonistIntervention : Bool
        painOrGlobalSymptomEndpoint : Bool
        placeboCausalContrastPaid : Bool
        doseComparisonPaid : Bool
        boundary : String

decraecker2024Receipt : H1InterventionReceipt
decraecker2024Receipt = h1-intervention-receipt
  decraecker2024Source randomizedDoubleBlindPlaceboControlled
  true true true true false
  "The randomized placebo contrast is retained at the specified dose/population/endpoints. The composite endpoint result is not rewritten as significance of each component endpoint."

pia2026Receipt : H1InterventionReceipt
pia2026Receipt = h1-intervention-receipt
  pia2026Source openLabelDoseComparison
  true true true false true
  "The 40-vs-20 mg dose association is retained as open-label comparative evidence; it does not manufacture a placebo-controlled causal dose-response theorem."

data OpenLabelEqualsRandomizedPlaceboContrastPermission : Set where
openLabelDoesNotEqualRandomizedPlaceboContrast :
  OpenLabelEqualsRandomizedPlaceboContrastPermission → ⊥
openLabelDoesNotEqualRandomizedPlaceboContrast ()

data H1BenefitIdentifiesAllIBSAsHistamineDrivenPermission : Set where
h1BenefitDoesNotIdentifyAllIBSAsHistamineDriven :
  H1BenefitIdentifiesAllIBSAsHistamineDrivenPermission → ⊥
h1BenefitDoesNotIdentifyAllIBSAsHistamineDriven ()

record IBSHistamineH1InterventionBoundary : Set where
  constructor ibs-histamine-h1-intervention-boundary
  field randomizedH1InterventionEvidenceAcquired : Bool
        randomizedH1InterventionEvidenceAcquiredIsTrue : randomizedH1InterventionEvidenceAcquired ≡ true
        openLabelDoseEvidenceAcquired : Bool
        openLabelDoseEvidenceAcquiredIsTrue : openLabelDoseEvidenceAcquired ≡ true
        designsCollapsed : Bool
        designsCollapsedIsFalse : designsCollapsed ≡ false
        allIBSHistamineDrivenClaimed : Bool
        allIBSHistamineDrivenClaimedIsFalse : allIBSHistamineDrivenClaimed ≡ false
        quailEfficacyPaidByTheseTrials : Bool
        quailEfficacyPaidByTheseTrialsIsFalse : quailEfficacyPaidByTheseTrials ≡ false

canonicalIBSHistamineH1InterventionBoundary : IBSHistamineH1InterventionBoundary
canonicalIBSHistamineH1InterventionBoundary = ibs-histamine-h1-intervention-boundary
  true refl true refl false refl false refl false refl
