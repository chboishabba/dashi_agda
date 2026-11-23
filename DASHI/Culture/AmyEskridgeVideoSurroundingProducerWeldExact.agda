module DASHI.Culture.AmyEskridgeVideoSurroundingProducerWeldExact where

-- DASHI extension. Exact imported source producer identity, not restated
-- or imported scientific validity. This module is the video-facing adapter
-- for source material first published in external patents, peer-reviewed
-- papers, NASA/DIA reports, archived interviews, 2018 HAL5 slides, and the
-- repository's independent measurement/contract diligence owners.
--
-- Source authors/identifiers live in:
-- DASHI.Culture.AmyEskridgeVideoSurroundingSourceAtlasExact
-- DASHI.Culture.AmyEskridgeVideoHAL5AllSlidesExact
-- DASHI.Culture.AmyEskridgeVideoDIAFullInventoryExact
-- See Docs/SourceAttributionPolicy.md.
-- Repeated sources do not count as corroborating independent witnesses.
-- Everything not paid by an exact original-source proposition remains OPEN.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Culture.AmyEskridgeVideoClaimAttributionLedgerExact as Video
import DASHI.Culture.AmyEskridgeVideoSurroundingSourceAtlasExact as Atlas
import DASHI.Culture.AmyEskridgeVideoHAL5AllSlidesExact as Slides
import DASHI.Culture.AmyEskridgeVideoDIAFullInventoryExact as DIA
import DASHI.Culture.AmyEskridgeHAL5PrimaryLiteratureSnowballExact as Papers
import DASHI.Culture.NingLiArmyTexasAuditPrimaryInspectionExact as Texas
import DASHI.Physics.ExoticGravity.NingLiArmyOtherTransactionSourceDiligenceExact as Army
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentalConstraintRegistryExact as Constraints

data ExactProducer : Set where
  sourceEntry : Atlas.LinkedSource → ExactProducer
  originalPaper : Papers.AmyPrimaryLiteratureSnowballAtom → ExactProducer
  historicalSlide : Slides.HAL5Slide → ExactProducer
  dirdIndex : DIA.DIRDInventoryEntry → ExactProducer
  experimentalProducer : Constraints.ExperimentalConstraint → ExactProducer
  texasAudit : Texas.TexasAuditAppearance → ExactProducer
  originalArmy : Army.ArmyOtherTransactionSourceState → ExactProducer

data SourceRole : Set where
  mediaRoster : SourceRole
  sourceContext : SourceRole
  originalDocument : SourceRole
  patentRecord : SourceRole
  experimentalConstraint : SourceRole
  correctivePrimary : SourceRole
  historicalChronology : SourceRole
  historicalMention : SourceRole
  controlledPhysics : SourceRole
  unpaidFinding : SourceRole
  historicalPaperRole : SourceRole
  governmentExperiment : SourceRole
  uninspectedPrimary : SourceRole
  secondaryReport : SourceRole
  authorClaim : SourceRole
  causalControl : SourceRole
  contemporaneousReport : SourceRole
  governmentInventory : SourceRole
  reportFullText : SourceRole
  firstPersonSpeech : SourceRole
  theoryContext : SourceRole
  disputedScientificClaim : SourceRole

record SourceScopedClaimWeld : Set where
  constructor source-scoped-weld
  field
    claimedInEditedVideo : Video.RawAttributedClaim
    originalAndExistingProducers : List ExactProducer
    relationship : SourceRole
    unpaidSameObjectOrMechanism : String
open SourceScopedClaimWeld public

weld004 : SourceScopedClaimWeld
weld004 = source-scoped-weld
  Video.claim004
  ((sourceEntry Atlas.fox2026) ∷ (sourceEntry Atlas.house2026) ∷ [])
  mediaRoster
  "Fox named eleven is media enumeration; House official inquiry is at least ten unconfirmed reports"

weld009 : SourceScopedClaimWeld
weld009 = source-scoped-weld
  Video.claim009
  ((sourceEntry Atlas.amyZoom) ∷ (historicalSlide Slides.deck04) ∷ [])
  sourceContext
  "HAL5 role and family event identity are distinct from causal death hypothesis"

weld015 : SourceScopedClaimWeld
weld015 = source-scoped-weld
  Video.claim015
  ((historicalSlide Slides.deck01) ∷ (historicalSlide Slides.deck35) ∷ [])
  originalDocument
  "Original HAL5 talk and slides directly pay original historical presentation"

weld022 : SourceScopedClaimWeld
weld022 = source-scoped-weld
  Video.claim022
  ((sourceEntry Atlas.brown1960) ∷ (sourceEntry Atlas.brown1967) ∷ [])
  patentRecord
  "Brown high-voltage patents cannot independently pay vacuum-effect reports"

weld023 : SourceScopedClaimWeld
weld023 = source-scoped-weld
  Video.claim023
  ((sourceEntry Atlas.brown1960) ∷ (sourceEntry Atlas.brown1967) ∷ [])
  experimentalConstraint
  "Ion/electrohydrodynamic forces are serious controls for alleged vacuum tests"

weld025 : SourceScopedClaimWeld
weld025 = source-scoped-weld
  Video.claim025
  ((sourceEntry Atlas.teslaIncorrect) ∷ (sourceEntry Atlas.teslaAerial) ∷ (historicalSlide Slides.deck12) ∷ [])
  correctivePrimary
  "US1655144A names Hallgarth/Chandler; original HAL5 slide repeated wrong attribution"

weld028 : SourceScopedClaimWeld
weld028 = source-scoped-weld
  Video.claim028
  ((sourceEntry Atlas.grfInstitution) ∷ (sourceEntry Atlas.grfScholarship) ∷ (historicalSlide Slides.deck13) ∷ [])
  historicalChronology
  "Official 1949 organising meeting vs 1948 historical founding accounts require event-time distinction"

weld029 : SourceScopedClaimWeld
weld029 = source-scoped-weld
  Video.claim029
  ((sourceEntry Atlas.grfScholarship) ∷ (sourceEntry Atlas.dewittHistory) ∷ (historicalSlide Slides.deck14) ∷ [])
  historicalChronology
  "Original prize winners/DeWitt essay and exact later Nobel count must be sourced separately"

weld030 : SourceScopedClaimWeld
weld030 = source-scoped-weld
  Video.claim030
  ((historicalSlide Slides.deck16) ∷ [])
  historicalMention
  "John Searl claim only; apparatus and independent electrical-mechanical accounting open"

weld031 : SourceScopedClaimWeld
weld031 = source-scoped-weld
  Video.claim031
  ((sourceEntry Atlas.dean) ∷ (historicalSlide Slides.deck17) ∷ [])
  patentRecord
  "Norman Dean patented a rotary drive; patent not reactionless free-space thrust"

weld033 : SourceScopedClaimWeld
weld033 = source-scoped-weld
  Video.claim033
  ((sourceEntry Atlas.wallace605) ∷ (sourceEntry Atlas.wallace606) ∷ (historicalSlide Slides.deck18) ∷ [])
  patentRecord
  "Two exact Wallace patents not independent physics validation"

weld034 : SourceScopedClaimWeld
weld034 = source-scoped-weld
  Video.claim034
  ((sourceEntry Atlas.royalInstitution) ∷ (sourceEntry Atlas.cambridgeGyro) ∷ (historicalSlide Slides.deck19) ∷ [])
  controlledPhysics
  "Laithwaite demo contextualised by classical gyroscope physics"

weld035 : SourceScopedClaimWeld
weld035 = source-scoped-weld
  Video.claim035
  ((sourceEntry Atlas.royalInstitution) ∷ [])
  unpaidFinding
  "Royal Institution history does not independently confirm removal from fellowship"

weld036 : SourceScopedClaimWeld
weld036 = source-scoped-weld
  Video.claim036
  ((sourceEntry Atlas.liTorr1991) ∷ (sourceEntry Atlas.liTorr1992) ∷ (originalPaper Papers.liTorr1991Atom) ∷ (originalPaper Papers.liTorr1992Atom) ∷ (historicalSlide Slides.deck24) ∷ [])
  historicalPaperRole
  "1991/1992 papers are theoretical mechanisms, not demonstrated gravitomagnetic spacecraft"

weld037 : SourceScopedClaimWeld
weld037 = source-scoped-weld
  Video.claim037
  ((sourceEntry Atlas.nasaGrant) ∷ (sourceEntry Atlas.li1997) ∷ (experimentalProducer Constraints.nasaStaticYBCO) ∷ [])
  governmentExperiment
  "NASA and UAH work had static null constraints and incomplete all-up test; no Army same-object weld"

weld039 : SourceScopedClaimWeld
weld039 = source-scoped-weld
  Video.claim039
  ((sourceEntry Atlas.armyOriginalLocator) ∷ (originalArmy Army.currentArmySourceState) ∷ (texasAudit Texas.texasFY2005LockheedAppearance) ∷ (texasAudit Texas.texasFY2006LockheedAppearance) ∷ [])
  uninspectedPrimary
  "Reported DAAH01-01-9-R001 number plus Texas audit recurrence does not prove AC Gravity award/Lockheed relationship"

weld041 : SourceScopedClaimWeld
weld041 = source-scoped-weld
  Video.claim041
  ((sourceEntry Atlas.fox2026) ∷ [])
  secondaryReport
  "2014 accident and 2021 death chronology require independent underlying event records"

weld043 : SourceScopedClaimWeld
weld043 = source-scoped-weld
  Video.claim043
  ((sourceEntry Atlas.podk1992) ∷ (sourceEntry Atlas.podk1997) ∷ (sourceEntry Atlas.hathaway2003) ∷ (originalPaper Papers.podkletnov1992Atom) ∷ (experimentalProducer Constraints.podkletnovNieminen1992ReportedSignal) ∷ (experimentalProducer Constraints.hathawayReplication) ∷ [])
  experimentalConstraint
  "1992 0.05–0.3% vs later 1.9–2.1% and 2003 null down to 0.001% in nonidentical rpm regimes"

weld047 : SourceScopedClaimWeld
weld047 = source-scoped-weld
  Video.claim047
  ((sourceEntry Atlas.poher2020) ∷ [])
  authorClaim
  "Poher's own speculative 2020 theory is not a measured replication of Podkletnov"

weld048 : SourceScopedClaimWeld
weld048 = source-scoped-weld
  Video.claim048
  ((sourceEntry Atlas.poher2020) ∷ [])
  unpaidFinding
  "No authenticated 2015 NASA test result located; author paper cannot be substituted"

weld049 : SourceScopedClaimWeld
weld049 = source-scoped-weld
  Video.claim049
  ((sourceEntry Atlas.gao1969) ∷ (historicalSlide Slides.deck21) ∷ [])
  correctivePrimary
  "Original 1969 Mansfield funding rule does not mandate classification"

weld050 : SourceScopedClaimWeld
weld050 = source-scoped-weld
  Video.claim050
  ((sourceEntry Atlas.gao1969) ∷ [])
  causalControl
  "Military relevance criterion cannot be promoted to covert research budget flow"

weld051 : SourceScopedClaimWeld
weld051 = source-scoped-weld
  Video.claim051
  ((sourceEntry Atlas.woodward1992) ∷ (originalPaper Papers.woodward1992Atom) ∷ (historicalSlide Slides.deck23) ∷ [])
  historicalPaperRole
  "Woodward 1992 original model distinguished from independent Mach-effect thrust"

weld053 : SourceScopedClaimWeld
weld053 = source-scoped-weld
  Video.claim053
  ((sourceEntry Atlas.jane2002) ∷ [])
  contemporaneousReport
  "2002 reporting predates narrator's 2014 first acknowledgment and does not prove successful hardware"

weld054 : SourceScopedClaimWeld
weld054 = source-scoped-weld
  Video.claim054
  ((sourceEntry Atlas.jane2002) ∷ [])
  contemporaneousReport
  "Boeing interest and third-party reporting distinct from a certified GRASP technical result"

weld056 : SourceScopedClaimWeld
weld056 = source-scoped-weld
  Video.claim056
  ((sourceEntry Atlas.diaFOIA2022) ∷ (dirdIndex DIA.dird01) ∷ [])
  governmentInventory
  "DIA research programme paperwork not actual anti-gravity device programme"

weld057 : SourceScopedClaimWeld
weld057 = source-scoped-weld
  Video.claim057
  ((sourceEntry Atlas.diaFOIA2022) ∷ (dirdIndex DIA.dird14) ∷ (dirdIndex DIA.dird24) ∷ (dirdIndex DIA.dird29) ∷ (dirdIndex DIA.dird36) ∷ [])
  governmentInventory
  "Original 37-report 1,473-page DIA inventory; separate 38-title circulation remains unreconciled"

weld058 : SourceScopedClaimWeld
weld058 = source-scoped-weld
  Video.claim058
  ((dirdIndex DIA.dird18) ∷ [])
  reportFullText
  "DIRD wormholes paper theoretical and future laboratory demonstration"

weld059 : SourceScopedClaimWeld
weld059 = source-scoped-weld
  Video.claim059
  ((dirdIndex DIA.dird13) ∷ [])
  reportFullText
  "DIRD extra dimensions speculative proposal"

weld060 : SourceScopedClaimWeld
weld060 = source-scoped-weld
  Video.claim060
  ((dirdIndex DIA.dird19) ∷ [])
  reportFullText
  "DIRD anti-gravity challenges, no working generator"

weld061 : SourceScopedClaimWeld
weld061 = source-scoped-weld
  Video.claim061
  ((dirdIndex DIA.dird15) ∷ [])
  reportFullText
  "DIRD metric engineering assumes presently unavailable physical source"

weld063 : SourceScopedClaimWeld
weld063 = source-scoped-weld
  Video.claim063
  ((sourceEntry Atlas.house2026) ∷ (sourceEntry Atlas.fox2026) ∷ [])
  causalControl
  "An unconfirmed media roster does not prove suppression or common cause"

weld064 : SourceScopedClaimWeld
weld064 = source-scoped-weld
  Video.claim064
  ((sourceEntry Atlas.burisch2007) ∷ [])
  firstPersonSpeech
  "2007 Burisch original timeline allegation not a government programme document"

weld066 : SourceScopedClaimWeld
weld066 = source-scoped-weld
  Video.claim066
  ((sourceEntry Atlas.dick1977) ∷ [])
  firstPersonSpeech
  "1977 speculative speech not physics evidence"

weld067 : SourceScopedClaimWeld
weld067 = source-scoped-weld
  Video.claim067
  ((sourceEntry Atlas.deutsch1995) ∷ (sourceEntry Atlas.deutsch2002) ∷ [])
  theoryContext
  "1995 TV quotation and 2002 mathematics are distinct from a working future-viewing device"

weld070 : SourceScopedClaimWeld
weld070 = source-scoped-weld
  Video.claim070
  ((sourceEntry Atlas.bem2011) ∷ (sourceEntry Atlas.cornellBem2010) ∷ (sourceEntry Atlas.radin2004) ∷ (sourceEntry Atlas.bemMeta2015) ∷ [])
  disputedScientificClaim
  "Cornell's contemporary Bem explanation, 2011 psychological paper, and Radin physiological protocol are different sources"

weld072 : SourceScopedClaimWeld
weld072 = source-scoped-weld
  Video.claim072
  ((sourceEntry Atlas.burisch2007) ∷ [])
  firstPersonSpeech
  "Repeated interview quotations not independent operational testimony"

weld079 : SourceScopedClaimWeld
weld079 = source-scoped-weld
  Video.claim079
  ((sourceEntry Atlas.burisch2007) ∷ [])
  firstPersonSpeech
  "Earth magnetic anomalies do not establish physical traversable wormholes"

weld085 : SourceScopedClaimWeld
weld085 = source-scoped-weld
  Video.claim085
  ((sourceEntry Atlas.burisch2007) ∷ [])
  firstPersonSpeech
  "EU/UN/NATO component allocation requires agency inventories and verifiable custody"

highAlphaOriginalProducerWelds : List SourceScopedClaimWeld
highAlphaOriginalProducerWelds =
  weld004 ∷
  weld009 ∷
  weld015 ∷
  weld022 ∷
  weld023 ∷
  weld025 ∷
  weld028 ∷
  weld029 ∷
  weld030 ∷
  weld031 ∷
  weld033 ∷
  weld034 ∷
  weld035 ∷
  weld036 ∷
  weld037 ∷
  weld039 ∷
  weld041 ∷
  weld043 ∷
  weld047 ∷
  weld048 ∷
  weld049 ∷
  weld050 ∷
  weld051 ∷
  weld053 ∷
  weld054 ∷
  weld056 ∷
  weld057 ∷
  weld058 ∷
  weld059 ∷
  weld060 ∷
  weld061 ∷
  weld063 ∷
  weld064 ∷
  weld066 ∷
  weld067 ∷
  weld070 ∷
  weld072 ∷
  weld079 ∷
  weld085 ∷ []

countWelds : List SourceScopedClaimWeld → Nat
countWelds [] = zero
countWelds (_ ∷ xs) = suc (countWelds xs)

exactSourceScopedWeldCount : countWelds highAlphaOriginalProducerWelds ≡ 39
exactSourceScopedWeldCount = refl

-- The 86-row ledger remains the unique claim universe; this file supplies
-- *additional evidence producers* for the high-alpha subset, not a replacement.
data SourceMembershipImpliesExperimentSuccess : Set where
data MultipleClaimsOnOneSourceImplyMultipleIndependentSources : Set where
data TexasAgreementNumberProvesACGravityContract : Set where

noSourceToExperimentShortcut : SourceMembershipImpliesExperimentSuccess → ⊥
noSourceToExperimentShortcut ()
noDuplicateIndependence : MultipleClaimsOnOneSourceImplyMultipleIndependentSources → ⊥
noDuplicateIndependence ()
noIdentifierCollisionPromotion : TexasAgreementNumberProvesACGravityContract → ⊥
noIdentifierCollisionPromotion ()
