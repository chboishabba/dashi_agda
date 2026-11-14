module DASHI.Education.DigitalESDEfSPedagogicalReciprocityRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
import DASHI.Education.DigitalESDEfSPedagogicalReciprocityExact as E
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as D

sourceIdentityRegression : E.EfSSource.exactLocator E.vikaneHoydalsvik ≡
  "https://doi.org/10.1080/13504622.2023.2273785"
sourceIdentityRegression = refl

practitionerRoleRegression : E.EfSSource.sourceRole E.elliottEfS ≡ E.practitionerTheoretical
practitionerRoleRegression = refl

systemsBridgeRegression : E.ReciprocalPedagogicalBridge.digitalPrinciple E.systemsCustodianship ≡
  D.contextualCustodianship
systemsBridgeRegression = refl

systemsEfSRegression : E.ReciprocalPedagogicalBridge.efsOrientation E.systemsCustodianship ≡
  E.systemsRelationships
systemsEfSRegression = refl

personalisationCollectiveTensionRegression :
  E.ReciprocalPedagogicalBridge.status E.localChoiceCollectiveTension ≡ E.productiveTension
personalisationCollectiveTensionRegression = refl

allCandidatesUnpromotedRegression :
  E.ReciprocalPedagogicalBridge.promotion E.collectiveAgency ≡ E.candidate
allCandidatesUnpromotedRegression = refl

noEffectPromotionRegression : E.TheoreticalAlignmentProvesEffect → ⊥
noEffectPromotionRegression = E.alignmentIsNotEffect
