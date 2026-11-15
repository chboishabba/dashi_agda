module DASHI.Biology.QuailEggHumanOralTransferExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

benichou2014Source : Source.AttributedSource
benichou2014Source = Source.mkDOISource
  "Annie-Claude Benichou; Marion Armanet; Anthony Bussière; Nathalie Chevreau; Jean-Michel Cardot; Jan Tétard"
  "A proprietary blend of quail egg for the attenuation of nasal provocation with a standardized allergenic challenge: a randomized, double-blind, placebo-controlled study"
  "Food Science & Nutrition 2(6):655-663" "2014"
  "10.1002/fsn3.147" "https://doi.org/10.1002/fsn3.147"
  Source.academicArticleSource
  "Pays randomized double-blind crossover human oral exposure to a proprietary quail-egg blend in an allergen-provocation/rhinitis paradigm. It does not pay IBS efficacy, mast-cell target engagement in gut, or equivalence to raw/whole quail egg."
  Source.publicAttribution

andaloro2023Source : Source.AttributedSource
andaloro2023Source = Source.mkDOISource
  "Claudio Andaloro; A M Saibene; Ignazio La Mantia"
  "Quail egg homogenate with zinc as adjunctive therapy in seasonal allergic rhinitis: a randomised, controlled trial"
  "Journal of Laryngology & Otology 137(4):432-437" "2023"
  "10.1017/S0022215122001219" "https://doi.org/10.1017/S0022215122001219"
  Source.academicArticleSource
  "Pays a randomized human seasonal-allergic-rhinitis adjunctive-therapy result for mometasone plus oral quail-egg-and-zinc tablets versus mometasone alone. Combination treatment prevents isolating a quail-only effect."
  Source.publicAttribution

data HumanOralQuailContext : Set where
  acuteAllergenProvocation : HumanOralQuailContext
  seasonalAllergicRhinitisAdjunctive : HumanOralQuailContext

data ProductIdentity : Set where
  proprietaryQuailBlend : ProductIdentity
  quailEggPlusZincCombination : ProductIdentity

record HumanOralQuailEvidenceReceipt : Set where
  constructor human-oral-quail-evidence-receipt
  field source : Source.AttributedSource
        context : HumanOralQuailContext
        product : ProductIdentity
        randomizedHumanExposure : Bool
        oralExposurePaid : Bool
        gutTargetEngagementPaid : Bool
        ibsEndpointPaid : Bool
        componentIsolationPaid : Bool
        boundary : String

benichou2014Receipt : HumanOralQuailEvidenceReceipt
benichou2014Receipt = human-oral-quail-evidence-receipt
  benichou2014Source acuteAllergenProvocation proprietaryQuailBlend
  true true false false false
  "Human oral exposure and rhinitis/allergen-challenge outcome are paid; IBS, intestinal histamine/DAO, gut mast-cell target engagement and whole-food equivalence remain unpaid."

andaloro2023Receipt : HumanOralQuailEvidenceReceipt
andaloro2023Receipt = human-oral-quail-evidence-receipt
  andaloro2023Source seasonalAllergicRhinitisAdjunctive quailEggPlusZincCombination
  true true false false false
  "Adjunctive human rhinitis evidence is paid, but zinc and mometasone co-treatment block attribution of the incremental effect uniquely to quail egg."

data RhinitisEvidencePaysIBSPermission : Set where
rhinitisEvidenceDoesNotPayIBS : RhinitisEvidencePaysIBSPermission → ⊥
rhinitisEvidenceDoesNotPayIBS ()

data QuailPlusZincIdentifiesQuailEffectPermission : Set where
combinationDoesNotIdentifyQuailEffect : QuailPlusZincIdentifiesQuailEffectPermission → ⊥
combinationDoesNotIdentifyQuailEffect ()

data OralExposureEqualsGutTargetEngagementPermission : Set where
oralExposureDoesNotEqualGutTargetEngagement : OralExposureEqualsGutTargetEngagementPermission → ⊥
oralExposureDoesNotEqualGutTargetEngagement ()

record QuailHumanOralTransferBoundary : Set where
  constructor quail-human-oral-transfer-boundary
  field humanOralExposureNowPaid : Bool
        humanOralExposureNowPaidIsTrue : humanOralExposureNowPaid ≡ true
        humanRhinitisOutcomeNowPaid : Bool
        humanRhinitisOutcomeNowPaidIsTrue : humanRhinitisOutcomeNowPaid ≡ true
        humanIBSEfficacyPaid : Bool
        humanIBSEfficacyPaidIsFalse : humanIBSEfficacyPaid ≡ false
        gutMechanisticTargetEngagementPaid : Bool
        gutMechanisticTargetEngagementPaidIsFalse : gutMechanisticTargetEngagementPaid ≡ false
        combinationTherapyIdentifiesQuailOnlyEffect : Bool
        combinationTherapyIdentifiesQuailOnlyEffectIsFalse : combinationTherapyIdentifiesQuailOnlyEffect ≡ false

canonicalQuailHumanOralTransferBoundary : QuailHumanOralTransferBoundary
canonicalQuailHumanOralTransferBoundary = quail-human-oral-transfer-boundary
  true refl true refl false refl false refl false refl
