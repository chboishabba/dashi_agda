module DASHI.Culture.FoucaultDerridaFourfoldRetreatAxisCrossPollinationExact where

------------------------------------------------------------------------
-- FOUCAULT / DERRIDA x FOURFOLD-RETREAT AXIS CROSS-POLLINATION
--
-- This module compares source-backed axis evidence without turning either
-- thinker into a proxy for poststructuralism as a whole.
--
-- Source proposition
-- != axis evidence status
-- != complete thinker profile
-- != school-wide classification.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Culture.FoucaultFourfoldRetreatPrimarySourceBoundaryExact as Foucault
import DASHI.Culture.DerridaFourfoldRetreatPrimarySourceBoundaryExact as Derrida
import DASHI.Culture.RockhillFosterFourfoldRetreatSourceBoundaryExact as RF
import DASHI.Culture.PoststructuralismFourfoldRetreatCrossPollinationExact as PS
import DASHI.Culture.PhilosophyClaimProvenanceHistoryBidiExact as Philosophy

------------------------------------------------------------------------
-- Appraisal states encode evidence status, not metaphysical truth values.
------------------------------------------------------------------------

data AxisAppraisal : Set where
  retreatSupportedBySelectedPrimarySources
  retreatCounterevidencePresent
  criticalMovePresentButRetreatOpen
  insufficientPrimaryCorpus
  : AxisAppraisal

data Thinker : Set where foucault derrida : Thinker
data Axis : Set where class imperialism materialismScience reason : Axis

axisAppraisal : Thinker → Axis → AxisAppraisal
axisAppraisal foucault class = insufficientPrimaryCorpus
axisAppraisal foucault imperialism = insufficientPrimaryCorpus
axisAppraisal foucault materialismScience = retreatCounterevidencePresent
axisAppraisal foucault reason = criticalMovePresentButRetreatOpen
axisAppraisal derrida class = insufficientPrimaryCorpus
axisAppraisal derrida imperialism = insufficientPrimaryCorpus
axisAppraisal derrida materialismScience = insufficientPrimaryCorpus
axisAppraisal derrida reason = retreatCounterevidencePresent

------------------------------------------------------------------------
-- Exact finite distinctions.
------------------------------------------------------------------------

foucaultMaterialismNotSimplyOpen :
  axisAppraisal foucault materialismScience ≡ insufficientPrimaryCorpus → ⊥
foucaultMaterialismNotSimplyOpen ()

derridaReasonNotSimplyOpen :
  axisAppraisal derrida reason ≡ insufficientPrimaryCorpus → ⊥
derridaReasonNotSimplyOpen ()

foucaultReasonNotDerridaReasonAppraisal :
  axisAppraisal foucault reason ≡ axisAppraisal derrida reason → ⊥
foucaultReasonNotDerridaReasonAppraisal ()

------------------------------------------------------------------------
-- The source-backed asymmetry is the useful result:
--
-- Foucault selected primary texts provide material/institutional counterevidence
-- to a simple discourse-only retreat reading, while the reason axis remains
-- open because critique of truth/power does not itself decide irrationalism.
--
-- Derrida selected primary texts directly counter the simple irrationalism
-- reading on the reason axis, while materialism/class/imperialism remain open
-- pending broader primary-source construction.
------------------------------------------------------------------------

record NamedThinkerAxisWeld : Set where
  constructor named-thinker-axis-weld
  field
    rockhillFosterBoundary : RF.FourfoldRetreatSourceBoundary
    poststructuralismBoundary : PS.FourfoldRetreatCrossPollinationWeld
    philosophyAttributionBoundary : Philosophy.PhilosophyClaimProvenanceHistoryBoundary
    foucaultBoundary : Foucault.FoucaultFourfoldSourceBoundary
    derridaBoundary : Derrida.DerridaFourfoldSourceBoundary
    thinkerProfilesAreNotSchoolProfile : Bool
    selectedSourcePresenceIsNotWholeDoctrine : Bool
    sourceCounterevidenceIsNotAxisNegationTheorem : Bool
    missingEvidenceIsNotPositiveRetreatEvidence : Bool
    sameSchoolLabelDoesNotEqualSameAxisAppraisal : Bool
    strongerClassificationRequiresPrimarySourceExpansion : Bool

canonicalNamedThinkerAxisWeld : NamedThinkerAxisWeld
canonicalNamedThinkerAxisWeld =
  named-thinker-axis-weld
    RF.canonicalFourfoldRetreatSourceBoundary
    PS.canonicalFourfoldRetreatCrossPollinationWeld
    Philosophy.canonicalPhilosophyClaimProvenanceHistoryBoundary
    Foucault.canonicalFoucaultFourfoldSourceBoundary
    Derrida.canonicalDerridaFourfoldSourceBoundary
    true true true true true true

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data FoucaultMaterialCounterevidenceMeansNoMaterialRetreatEver : Set where
data DerridaReasonCounterevidenceMeansNoReasonRetreatEver : Set where
data TwoThinkersDeterminePoststructuralism : Set where
data MissingClassEvidenceMeansClassRetreat : Set where
data MissingImperialismEvidenceMeansImperialismRetreat : Set where
data RockhillFosterCritiqueOverridesPrimaryThinkerSource : Set where

foucaultCounterevidenceDoesNotCloseWholeAxisHistorically :
  FoucaultMaterialCounterevidenceMeansNoMaterialRetreatEver → ⊥
foucaultCounterevidenceDoesNotCloseWholeAxisHistorically ()

derridaCounterevidenceDoesNotCloseWholeAxisHistorically :
  DerridaReasonCounterevidenceMeansNoReasonRetreatEver → ⊥
derridaCounterevidenceDoesNotCloseWholeAxisHistorically ()

twoThinkersDoNotDeterminePoststructuralism :
  TwoThinkersDeterminePoststructuralism → ⊥
twoThinkersDoNotDeterminePoststructuralism ()

missingClassEvidenceDoesNotMeanClassRetreat :
  MissingClassEvidenceMeansClassRetreat → ⊥
missingClassEvidenceDoesNotMeanClassRetreat ()

missingImperialismEvidenceDoesNotMeanImperialismRetreat :
  MissingImperialismEvidenceMeansImperialismRetreat → ⊥
missingImperialismEvidenceDoesNotMeanImperialismRetreat ()

rockhillFosterCritiqueDoesNotOverridePrimaryThinkerSource :
  RockhillFosterCritiqueOverridesPrimaryThinkerSource → ⊥
rockhillFosterCritiqueDoesNotOverridePrimaryThinkerSource ()

------------------------------------------------------------------------
-- Current source frontier.
------------------------------------------------------------------------

record NamedThinkerFourfoldFrontier : Set where
  constructor named-thinker-fourfold-frontier
  field
    foucaultClassNeedsExpansion : Bool
    foucaultImperialismNeedsExpansion : Bool
    foucaultMaterialCounterevidencePresent : Bool
    foucaultReasonNeedsDiscrimination : Bool
    derridaClassNeedsExpansion : Bool
    derridaImperialismNeedsExpansion : Bool
    derridaMaterialismNeedsExpansion : Bool
    derridaReasonCounterevidencePresent : Bool

canonicalNamedThinkerFourfoldFrontier : NamedThinkerFourfoldFrontier
canonicalNamedThinkerFourfoldFrontier =
  named-thinker-fourfold-frontier
    true true true true true true true true
