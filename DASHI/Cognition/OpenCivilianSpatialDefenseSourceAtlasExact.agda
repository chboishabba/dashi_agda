module DASHI.Cognition.OpenCivilianSpatialDefenseSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- OPEN CIVILIAN SPATIAL DEFENCE: SOURCE ATLAS
--
-- Attribution discipline:
--   * vendor first-party pages pay only vendor-described product/policy claims;
--   * ICRC sources pay only the ICRC's stated humanitarian/legal position;
--   * inherited RF academic/government sources remain owned by the existing
--     Physics source atlas and are not re-authored here;
--   * DASHI reconstruction/theorems are not attributed back to any source.
------------------------------------------------------------------------

bostonDynamicsFAQ : Source.AttributedSource
bostonDynamicsFAQ = Source.mkNoDOISource
  "Boston Dynamics"
  "Frequently Asked Questions"
  "Boston Dynamics first-party website"
  "accessed 2026-10-16"
  "https://bostondynamics.com/faq/"
  (Source.namedSourceKind "vendor first-party")
  "first-party source for the bounded claims that Spot is a general-purpose robot, that military use includes non-weaponized inspection/rescue/logistics examples, and that Boston Dynamics states it prohibits weaponization; not independent validation of every deployment or a universal industry/legal constraint"
  Source.publicAttribution

bostonDynamicsAntiWeaponizationLetter : Source.AttributedSource
bostonDynamicsAntiWeaponizationLetter = Source.mkNoDOISource
  "Boston Dynamics and co-signatory robotics companies"
  "General Purpose Robots Should Not Be Weaponized"
  "industry open letter hosted by Boston Dynamics"
  "2022 / accessed 2026-10-16"
  "https://bostondynamics.com/news/general-purpose-robots-should-not-be-weaponized/"
  (Source.namedSourceKind "industry policy statement")
  "first-party industry-policy source for signatories' stated opposition to weaponizing general-purpose advanced-mobility robots; does not establish binding international law, universal compliance, or the status of any particular third-party robot"
  Source.publicAttribution

icrcAWSFAQ20261008 : Source.AttributedSource
icrcAWSFAQ20261008 = Source.mkNoDOISource
  "International Committee of the Red Cross"
  "Frequently asked questions: Autonomous weapon systems"
  "ICRC"
  "2026-10-08"
  "https://www.icrc.org/en/article/faq-autonomous-weapon-systems"
  Source.institutionalSource
  "ICRC source for its current definition of autonomous weapon systems as systems that, once activated, can select and apply force without further human intervention, and for the ICRC's stated humanitarian/legal/ethical concern about loss of human control; source authority is the ICRC position, not a DASHI theorem or universal adjudication"
  Source.publicAttribution

icrcAWSIHL20260303 : Source.AttributedSource
icrcAWSIHL20260303 = Source.mkNoDOISource
  "International Committee of the Red Cross"
  "Autonomous Weapon Systems and International Humanitarian Law: Selected Issues"
  "ICRC briefing paper"
  "2026-03-03"
  "https://www.icrc.org/en/article/autonomous-weapon-systems-and-international-humanitarian-law-selected-issues"
  Source.institutionalSource
  "ICRC source for its analysis that AWS raise civilian-protection and human-control concerns under IHL and for its call for new legally binding prohibitions/restrictions; does not itself create enacted treaty law or determine legality of a particular system"
  Source.publicAttribution

icrcUNJointAppeal20260825 : Source.AttributedSource
icrcUNJointAppeal20260825 = Source.mkNoDOISource
  "United Nations Secretary-General and International Committee of the Red Cross President"
  "Renewed call to adopt rules on autonomous weapon systems"
  "joint public statement hosted by ICRC"
  "2026-08-25"
  "https://www.icrc.org/en/statement/renewed-call-un-secretary-general-and-icrc-president-adopt-rules-autonomous-weapons"
  Source.institutionalSource
  "source for the joint normative warning that autonomous targeting of humans by machines approaches a moral red line and for the renewed call for international rules; normative statement does not itself establish a new binding rule"
  Source.publicAttribution

openCivilianSpatialDefenseAtlas : Source.AttributedSourceAtlas
openCivilianSpatialDefenseAtlas = Source.mkSourceAtlas
  "open civilian spatial defence / robot dual-use bounded source atlas"
  "DASHI.Cognition.OpenCivilianSpatialDefenseSourceAtlasExact"
  (bostonDynamicsFAQ ∷
   bostonDynamicsAntiWeaponizationLetter ∷
   icrcAWSFAQ20261008 ∷
   icrcAWSIHL20260303 ∷
   icrcUNJointAppeal20260825 ∷ [])
  "vendor claims remain vendor claims; institutional humanitarian/legal positions remain attributed positions; no source creates operational authority, hostile attribution, exact system identity, technical performance validation, or a DASHI proof"
