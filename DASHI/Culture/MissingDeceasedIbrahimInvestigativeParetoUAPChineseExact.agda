module DASHI.Culture.MissingDeceasedIbrahimInvestigativeParetoUAPChineseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Culture.MissingDeceasedIbrahimInvestigativeParetoExact as Base
import DASHI.Culture.ChineseStrategicScientistRosterSnowballExact as China
import DASHI.Culture.MissingDeceasedUAPAdversarialClaimDiscriminatorExact as UAP
import DASHI.Culture.MissingDeceasedGameTheoryParetoProofSearchCrossPollinationExact as Search

------------------------------------------------------------------------
-- EXTENSION ONLY: keep the canonical U.S. person-specific Pareto unchanged.
-- These two lanes join it as non-scalarised acquisition targets.
------------------------------------------------------------------------

chineseStrategicScientistAcquisitionPareto : Base.InvestigativeParetoTarget
chineseStrategicScientistAcquisitionPareto = Base.investigative-pareto-target
  Base.secondFront
  "Chinese strategic scientist acquisition"
  "media roster -> work identity -> primary institutional/publication object -> event identity -> technical succession -> cross-national comparison"
  "for each of the nine currently named people, recover the primary event/death object and same-person weld to the already followed technical work; prioritise unresolved Yan Hong primary NPU work page and Liu Donghao event/work identity weld"
  "primary work already located for Chen Shuming, Feng Yanghe, Zhou Guangyuan, Liu Donghao candidate, Zhang Xiaoxin, Zhang Daibing, Li Minyong and Fang Daining; Yan Hong remains primary-work unpaid; Fang now has an explicit active-mechanical-metamaterial source; Feng has primary wargame/Bayesian/noisy-label sources"
  "person/event same-object identity; event cause; publication/project corpus; technical succession; matched-control denominator; whether apparent strategic-field concentration survives primary reconstruction"
  "Feng ISBN 978-7-5673-0533-5 and 978-7-5673-0611-0; Zhou DOI 10.1016/j.cej.2023.147642; Zhang Daibing DOI 10.11887/j.cn.201801023, 10.13700/j.bh.1001-5965.2016.0679 and 10.13973/j.cnki.robot.2017.0160; remaining stable identifiers retained per roster owner"
  "person QIDs unresolved unless independently verified"
  "006.3 AI / 519.5 Statistics / 620.11 Materials / 629 Aerospace / 005.8 Data security traversal only"
  "primary university/institute/publisher/publication objects plus primary event/death carriers"
  false true false
  "The media roster is not the evidence object.  Science/work reconstruction may proceed out of dependency order, but cross-national/common-cause payment waits for person-event-work welds and matched controls.  Do not manufacture a tenth identity from reports saying 'at least ten'."

uapAdversarialDiscriminatorPareto : Base.InvestigativeParetoTarget
uapAdversarialDiscriminatorPareto = Base.investigative-pareto-target
  Base.secondFront
  "UAP/adversarial discriminator"
  "speculative claim -> paid scientific kernel -> missing causal bridge -> adversarial prediction -> ordinary/control prediction -> discriminating acquisition"
  "run the zero-point-suppression, Mondaloy/S4, Maiwald-NHI, personnel-cleanup and inquiry-cover hypotheses only against acquisitions that distinguish them from ordinary/control explanations"
  "typed antigravity/vacuum-thrust machinery; Amy mechanism reverse-search; Reza alloy owner; Maiwald action spectroscopy; Fang active mechanical metamaterials; time-indexed role-capability fibre; ternary observer fibre"
  "mechanism/provenance same-object bridge; classified deployment/programme carrier; pre-public tasking chronology; role-capability overlap; matched controls; narrative self-sealing detection"
  "existing science owner paths and public programme identifiers; no Area-51/S4 same-object identifier paid"
  "Area 51 / S4 / NHI QID coordinates intentionally not used as evidence authority"
  "001 Knowledge / 355 Military science / 629 Aerospace / 303.49 social-process traversal only"
  "primary programme, contract, custody, deployment, personnel-tasking, chronology and same-object records"
  false true false
  "High value is pruning: a broad narrative that explains disappearance, death, survival and contrary testimony equally well has no discriminating observable and should lose Pareto priority.  Strategic/game-theory plausibility may choose a search but cannot become statistical or historical evidence."

record ExtendedParetoBoundary : Set where
  constructor extended-pareto-boundary
  field
    chineseMediaRosterCreatesEvidenceAuthority : Bool
    uapNarrativeCreatesEvidenceAuthority : Bool
    gameTheoryCreatesHistoricalTruth : Bool
    proofSearchMayPrioritiseDiscriminatingPrimaryObjects : Bool
    existingUSFirstFrontRemainsIndependent : Bool

canonicalExtendedParetoBoundary : ExtendedParetoBoundary
canonicalExtendedParetoBoundary = extended-pareto-boundary
  false false false true true
