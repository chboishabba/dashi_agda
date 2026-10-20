module DASHI.Cognition.OracleEllisonCausalElectoralEvidenceExact where

------------------------------------------------------------------------
-- SOURCE-BACKED CAUSAL ELECTORAL EVIDENCE
--
-- Berrebi & Klor (APSR 2008) provide a real causal-identification design for
-- a narrower adjacent proposition: terror exposure can affect Israeli voting
-- preferences. Their paper uses spatial and temporal variation, a treated vs
-- control difference-in-differences strategy, locality fixed effects / controls,
-- and a falsification analysis for reverse-causality concerns.
--
-- This is genuine causal evidence, not mere chronology. It still does not pay
-- the transcript's stronger same-object claim that Netanyahu intentionally
-- maintains threats in order to secure his own political survival.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Evidence
import DASHI.Biology.CausalIdentificationFamiliesExact as Identification

------------------------------------------------------------------------
-- Source coordinate and study-design receipt.
------------------------------------------------------------------------

berrebiKlorCitation : String
berrebiKlorCitation =
  "Claude Berrebi and Esteban F. Klor, Are Voters Sensitive to Terrorism? Direct Evidence from the Israeli Electorate, APSR 102(3):279-301 (2008), DOI 10.1017/S0003055408080246"

berrebiKlorStudyDesign : Evidence.StudyDesignReceipt
berrebiKlorStudyDesign =
  Evidence.studyDesignReceipt
    "berrebi-klor-2008-israeli-electorate"
    Evidence.quasiExperiment
    "Israeli localities observed across consecutive elections"
    "spatial and temporal variation in terror fatalities; treated localities versus localities without attacks"
    "changes in electoral results of non-attacked localities"
    "official/locality electoral outcomes and terror-fatality data as specified in the paper"
    "panel/locality continuity; not a participant attrition design"
    "locality fixed effects plus political, socioeconomic and demographic controls; countrywide terror fatalities separately represented"
    "historical natural exposure rather than implemented intervention fidelity"
    "multiple empirical specifications and falsification analysis reported"
    "local causal effect of terror fatalities on right-bloc vote share"
    "clustered/locality-level inferential treatment and reported robustness specifications"
    "Israeli electorate/locality/election scope; no automatic transport to a named politician's survival"
    Evidence.measuredSubject
    Evidence.validityStrong
    Evidence.validityLimited
    berrebiKlorCitation

publishedDesignAffordsCausalQuestion :
  Evidence.DesignAffords Evidence.quasiExperiment Evidence.causalQuestion
publishedDesignAffordsCausalQuestion = Evidence.quasiCanAddressCausal

------------------------------------------------------------------------
-- What the source actually pays.
------------------------------------------------------------------------

terrorExposureElectoralPreferenceCausalSurfacePaid : Bool
terrorExposureElectoralPreferenceCausalSurfacePaid = true

reportedLocalAttackWindowThreeMonths : Bool
reportedLocalAttackWindowThreeMonths = true

reportedRightBlocIncrease135BasisPoints : Bool
reportedRightBlocIncrease135BasisPoints = true

differenceInDifferencesTreatedControlDesignPaid : Bool
differenceInDifferencesTreatedControlDesignPaid = true

reverseCausalityFalsificationPaid : Bool
reverseCausalityFalsificationPaid = true

localityFixedEffectsAndControlsPaid : Bool
localityFixedEffectsAndControlsPaid = true

spilloverBeyondAttackLocalityReported : Bool
spilloverBeyondAttackLocalityReported = true

------------------------------------------------------------------------
-- Cross-pollination with generic causal-identification machinery.
--
-- The repository previously lacked an explicit natural-variation/instrument
-- family. The generic family now exists, but this owner does not fabricate a
-- full IdentificationEvidenceGate: source-to-obligation admission remains a
-- separate typed payment.
------------------------------------------------------------------------

instrumentalNaturalExperimentFamilyAvailable : Bool
instrumentalNaturalExperimentFamilyAvailable = true

genericInstrumentFamily : Identification.CausalIdentificationFamily
genericInstrumentFamily = Identification.instrumentalNaturalExperiment

fullGenericIdentificationGateInstalledForTranscriptClaim : Bool
fullGenericIdentificationGateInstalledForTranscriptClaim = false

------------------------------------------------------------------------
-- Non-promotions.
------------------------------------------------------------------------

netanyahuThreatMaintenancePoliticalSurvivalPaid : Bool
netanyahuThreatMaintenancePoliticalSurvivalPaid = false

terrorExposureEffectIdentifiesWhoCreatedOrMaintainedThreat : Bool
terrorExposureEffectIdentifiesWhoCreatedOrMaintainedThreat = false

rightBlocEffectIdentifiesNetanyahuIndividualSurvival : Bool
rightBlocEffectIdentifiesNetanyahuIndividualSurvival = false

causalElectoralEffectPaysMotive : Bool
causalElectoralEffectPaysMotive = false

historicalElectoralEffectAutomaticallyTransportsTo2026 : Bool
historicalElectoralEffectAutomaticallyTransportsTo2026 = false

record CausalElectoralEvidenceBoundary : Set where
  constructor causal-electoral-evidence-boundary
  field
    publishedQuasiExperimentCanPayBoundedCausalSurface : Bool
    terrorExposureEqualsIntentionalThreatMaintenance : Bool
    blocPreferenceEqualsNamedPoliticianSurvival : Bool
    causalEffectEqualsMotive : Bool
    historicalEffectAutomaticallyTransports : Bool
    exactTranscriptPromotionStillRequiresSameObjectGate : Bool

canonicalCausalElectoralEvidenceBoundary : CausalElectoralEvidenceBoundary
canonicalCausalElectoralEvidenceBoundary =
  causal-electoral-evidence-boundary true false false false false true
