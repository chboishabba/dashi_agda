module DASHI.Governance.CubaSanctionsDomesticInstitutionMechanismExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.SiegePressureDomesticDivergenceHypothesisExact as Siege

------------------------------------------------------------------------
-- CUBA: SANCTIONS x DOMESTIC-INSTITUTION MECHANISM
------------------------------------------------------------------------

gelosoMartinez2026 : Source.AttributedSource
gelosoMartinez2026 = Source.mkDOISource
  "Vincent Geloso, Carlos Luis Martinez"
  "Sanctions: The Case of Cuba"
  "Oxford Research Encyclopedia of Military History"
  "2026"
  "10.1093/9780197852705.003.0152"
  "https://academic.oup.com/edited-volume/63143/chapter-abstract/568209186"
  Source.academicChapterSource
  "2026 review: the U.S. embargo imposed measurable living-standard costs, but these were smaller than long-run costs associated with autocratic institutions; sanctions failed at regime change and likely strengthened blame externalisation"
  Source.publicAttribution

record CubaPressureMechanism : Set where
  constructor cuba-pressure-mechanism
  field
    source : Source.AttributedSource
    embargoCostPaid : Bool
    embargoCostPaidIsTrue : embargoCostPaid ≡ true
    domesticInstitutionCostPaid : Bool
    domesticInstitutionCostPaidIsTrue :
      domesticInstitutionCostPaid ≡ true
    interactionRatherThanSingleCause : Bool
    interactionRatherThanSingleCauseIsTrue :
      interactionRatherThanSingleCause ≡ true
    blameExternalisationSupported : Bool
    blameExternalisationSupportedIsTrue :
      blameExternalisationSupported ≡ true
    embargoSoleCause : Bool
    embargoSoleCauseIsFalse : embargoSoleCause ≡ false
    domesticInstitutionsSoleCause : Bool
    domesticInstitutionsSoleCauseIsFalse :
      domesticInstitutionsSoleCause ≡ false
    repressionNecessityPaid : Bool
    repressionNecessityPaidIsFalse :
      repressionNecessityPaid ≡ false

open CubaPressureMechanism public

canonicalCubaPressureMechanism : CubaPressureMechanism
canonicalCubaPressureMechanism =
  cuba-pressure-mechanism
    gelosoMartinez2026
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

existingHypothesis : Siege.MechanismHypothesis
existingHypothesis = Siege.cubaSiegeHypothesis

data EmbargoCostMeansEmbargoSoleCause : Set where
data DomesticInstitutionCostMeansEmbargoIrrelevant : Set where
data BlameExternalisationMeansAllGovernmentClaimsFalse : Set where
data EconomicMechanismMeansRepressionMechanism : Set where

embargoCostDoesNotCreateSoleCause :
  EmbargoCostMeansEmbargoSoleCause → ⊥
embargoCostDoesNotCreateSoleCause ()

domesticCostsDoNotEraseEmbargoCost :
  DomesticInstitutionCostMeansEmbargoIrrelevant → ⊥
domesticCostsDoNotEraseEmbargoCost ()

blameExternalisationDoesNotFalsifyEveryClaim :
  BlameExternalisationMeansAllGovernmentClaimsFalse → ⊥
blameExternalisationDoesNotFalsifyEveryClaim ()

economicMechanismDoesNotCreateRepressionMechanism :
  EconomicMechanismMeansRepressionMechanism → ⊥
economicMechanismDoesNotCreateRepressionMechanism ()

sourceSnowball :
  Snowball.SourceRoleSnowballReceipt gelosoMartinez2026
sourceSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt gelosoMartinez2026
