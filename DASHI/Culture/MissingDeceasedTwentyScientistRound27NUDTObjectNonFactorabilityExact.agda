module DASHI.Culture.MissingDeceasedTwentyScientistRound27NUDTObjectNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- ROUND 27: NUDT EXACT-OBJECT DISCRIMINATOR
--
-- Search has now resolved concrete source-backed object families for the three
-- retained NUDT scientists, but the acquired surfaces do not co-name another
-- retained NUDT scientist on the same task/object.  The empirical receipts are
-- therefore kept separate from the generic information-theoretic result below:
-- institution identity alone is too coarse to answer an exact-shared-task
-- query.  The finite witness is DASHI synthesis; it is not evidence that an
-- unobserved shared task exists.
------------------------------------------------------------------------

record NUDTObjectReceipt : Set where
  constructor nudt-object-receipt
  field
    person : String
    source : Attribution.AttributedSource
    exactObject : String
    sameInstitutionPaid : Bool
    exactObjectPaid : Bool
    namesAnotherRetainedScientist : Bool
    pays : String
    doesNotPay : String

open NUDTObjectReceipt public

chenSource : Attribution.AttributedSource
chenSource = Attribution.mkNoDOISource
  "National University of Defense Technology"
  "学校奋进一流突出贡献单位风采（2）丨‘芯’火相传 逐光而行"
  "NUDT official research history"
  "2026"
  "https://www.nudt.edu.cn/kxyj/kydt/31f6bbf5056c4be5b5483d9690f38dd1.htm"
  Attribution.institutionalSource
  "primary institutional history naming Chen Shuming as a 1999 Galaxy/Feiteng team backbone on the military-chip/DSP lineage"
  Attribution.publicAttribution

chenSnowball : Snowball.SourceRoleSnowballReceipt chenSource
chenSnowball = Snowball.canonicalSourceRoleSnowballReceipt chenSource

chenReceipt : NUDTObjectReceipt
chenReceipt = nudt-object-receipt
  "Chen Shuming"
  chenSource
  "1999 Galaxy/Feiteng domestic replacement effort -> military DSP/CPU lineage"
  true true false
  "Chen-side exact team/object family and NUDT institutional membership"
  "Feng Yanghe or Zhang Daibing participation on that exact task, a shared retained-person object, H2, or targeting"

fengSource : Attribution.AttributedSource
fengSource = Attribution.mkNoDOISource
  "Feng Yanghe; Cheng Guangquan; Shi Wei; Huang Kuihua; Huang Jincai; Liu Zhong"
  "基于深度强化学习的多机协同空战规划方法及系统"
  "Chinese invention patent CN112861442B; assignee National University of Defense Technology"
  "2021"
  "https://patents.google.com/patent/CN112861442B/zh"
  Attribution.governmentSource
  "patent surface naming Feng Yanghe on a concrete NUDT deep-reinforcement-learning multi-aircraft collaborative air-combat planning object"
  Attribution.publicAttribution

fengSnowball : Snowball.SourceRoleSnowballReceipt fengSource
fengSnowball = Snowball.canonicalSourceRoleSnowballReceipt fengSource

fengReceipt : NUDTObjectReceipt
fengReceipt = nudt-object-receipt
  "Feng Yanghe"
  fengSource
  "CN112861442B deep-RL multi-aircraft collaborative air-combat planning method/system"
  true true false
  "Feng-side exact patent/object identity and NUDT assignee"
  "Chen Shuming or Zhang Daibing participation on this patent/object, an exact retained-person shared task, H2, or targeting"

zhangSource : Attribution.AttributedSource
zhangSource = Attribution.mkDOISource
  "Zhang Daibing; Wang Xun; Zhong Zhiwei; Yan Chengping; Xiang Shaohua; Xi Yexun"
  "融合地面多传感器信息引导无人机着陆"
  "Journal of National University of Defense Technology 40(1)"
  "2018"
  "10.11887/j.cn.201801023"
  "https://doi.org/10.11887/j.cn.201801023"
  Attribution.academicArticleSource
  "article surface naming Zhang Daibing on a concrete multi-sensor autonomous-UAV-landing guidance object"
  Attribution.publicAttribution

zhangSnowball : Snowball.SourceRoleSnowballReceipt zhangSource
zhangSnowball = Snowball.canonicalSourceRoleSnowballReceipt zhangSource

zhangReceipt : NUDTObjectReceipt
zhangReceipt = nudt-object-receipt
  "Zhang Daibing"
  zhangSource
  "ground multi-sensor fusion guidance for autonomous UAV landing"
  true true false
  "Zhang-side exact publication/object identity and NUDT affiliation"
  "Chen Shuming or Feng Yanghe participation on this exact object, an exact retained-person shared task, H2, or targeting"

round27NUDTObjects : List NUDTObjectReceipt
round27NUDTObjects = chenReceipt ∷ fengReceipt ∷ zhangReceipt ∷ []

round27NUDTObjectCount : Nat
round27NUDTObjectCount = 3

chenObjectPaid : Bool
chenObjectPaid = true

fengObjectPaid : Bool
fengObjectPaid = true

zhangObjectPaid : Bool
zhangObjectPaid = true

chenFengSharedTaskPaid : Bool
chenFengSharedTaskPaid = false

chenZhangSharedTaskPaid : Bool
chenZhangSharedTaskPaid = false

fengZhangSharedTaskPaid : Bool
fengZhangSharedTaskPaid = false

------------------------------------------------------------------------
-- Query-indexed non-factorability witness.
--
-- Two logically possible worlds expose the same institution surface but differ
-- on the H2-relevant exact-shared-task answer.  Therefore the exact-task query
-- cannot factor through institution identity alone.  This is a structural
-- no-go, not an empirical assertion that either world is the actual history.
------------------------------------------------------------------------

data NUDTPairWorld : Set where
  sharedTaskWorld distinctTaskWorld : NUDTPairWorld

data NUDTInstitutionObservation : Set where
  nudtInstitution : NUDTInstitutionObservation

data NUDTBridgeQuery : Set where
  retainedPairSharesExactTask : NUDTBridgeQuery

data NUDTBridgeAnswer : Set where
  sharedExactTask distinctExactTasks : NUDTBridgeAnswer

projectInstitution : NUDTPairWorld → NUDTInstitutionObservation
projectInstitution _ = nudtInstitution

answerBridgeQuery : NUDTBridgeQuery → NUDTPairWorld → NUDTBridgeAnswer
answerBridgeQuery retainedPairSharesExactTask sharedTaskWorld = sharedExactTask
answerBridgeQuery retainedPairSharesExactTask distinctTaskWorld = distinctExactTasks

nudtSemantics : Query.QuerySemantics NUDTPairWorld NUDTBridgeQuery NUDTBridgeAnswer
nudtSemantics = Query.querySemantics answerBridgeQuery

nudtInstitutionQueryDefect :
  Query.QueryAdequacyDefect
    projectInstitution
    nudtSemantics
    retainedPairSharesExactTask
nudtInstitutionQueryDefect =
  Query.queryAdequacyDefect
    sharedTaskWorld
    distinctTaskWorld
    refl
    (λ ())

institutionOnlyCannotDetermineExactSharedTask :
  Query.AdequateFor
    projectInstitution
    nudtSemantics
    retainedPairSharesExactTask →
  ⊥
institutionOnlyCannotDetermineExactSharedTask =
  Query.queryAdequacyDefectBlocksFactorisation nudtInstitutionQueryDefect

sameInstitutionIsTooCoarseForH2Query : Bool
sameInstitutionIsTooCoarseForH2Query = true

exactObjectsDoNotComposeWithoutSameObjectReceipt : Bool
exactObjectsDoNotComposeWithoutSameObjectReceipt = true

syntheticCollisionDoesNotAssertHiddenSharedTask : Bool
syntheticCollisionDoesNotAssertHiddenSharedTask = true

round27H2PaidCount : Nat
round27H2PaidCount = 0

round27H3PaidCount : Nat
round27H3PaidCount = 0

round27Pareto : String
round27Pareto = "The NUDT institutional cluster has now decomposed into three concrete object families: Chen/Galaxy-Feiteng military DSP, Feng/CN112861442B collaborative air-combat planning, and Zhang/multi-sensor autonomous UAV landing. Search next for an exact task, project, laboratory, codebase, grant, patent, paper, procurement or roster that literally co-names at least two retained NUDT scientists. Institution identity alone is formally inadequate for that query."