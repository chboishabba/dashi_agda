module DASHI.Law.ZionismGlobalJewryExternalitySourceReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Externalities on Jews globally must be source-attributed without making Jews
-- collectively responsible for Israeli state policy or Zionist ideology.
------------------------------------------------------------------------

data JewrySourceRole : Set where
  diasporaJewishLeadershipStatement
  jewishAntiZionistOrganizationStatement
  unSpecialRapporteurFinding
  governmentAntisemitismReport
  scholarlyHistory
  dashiExternalityBridge : JewrySourceRole

data JewryProposition : Set where
  netanyahuGovernmentPoliciesEndangerGlobalJewryWarning
  israelPoliciesFuelAntisemitismWarning
  zionismNotInherentJewishCharacteristic
  antiZionismNotAutomaticallyAntisemitism
  israeliStateActionsMakeJewsCollectivelyResponsible
  everyJewBearsZionistPoliticalResponsibility : JewryProposition

record JewryReceipt : Set where
  constructor jewryReceipt
  field
    proposition : JewryProposition
    sourceRole : JewrySourceRole
    sourceReference : String
    boundedDescription : String

open JewryReceipt public

globalJewishLeadersWarningReceipt : JewryReceipt
globalJewishLeadersWarningReceipt = jewryReceipt
  netanyahuGovernmentPoliciesEndangerGlobalJewryWarning diasporaJewishLeadershipStatement
  "Letter by Jewish community leaders from 18 countries to Benjamin Netanyahu, reported 2025-2026"
  "Signatories warned that Israeli government policies and rhetoric were endangering the strength, security and sustainability of Israel and global Jewry. This is an attributed political/community warning, not a causal epidemiological finding."

antisemitismFuelWarningReceipt : JewryReceipt
antisemitismFuelWarningReceipt = jewryReceipt
  israelPoliciesFuelAntisemitismWarning diasporaJewishLeadershipStatement
  "Global Jewish leaders letter to Netanyahu"
  "The signatories warned that current government policies were fuelling antisemitism worldwide; responsibility for antisemitic acts remains with perpetrators, and the warning does not transfer collective blame to Jews."

unSpecialRapporteurDistinctionReceipt : JewryReceipt
unSpecialRapporteurDistinctionReceipt = jewryReceipt
  zionismNotInherentJewishCharacteristic unSpecialRapporteurFinding
  "A/79/319, UN Special Rapporteur on freedom of opinion and expression, Irene Khan, 2024"
  "The report states that Zionism is not an inherent characteristic of an individual or group and that it is wrong to equate anti-Zionism with antisemitism; contextual analysis is required where 'Zionist' is used as a proxy for hatred of Jews."

antiZionismBoundaryReceipt : JewryReceipt
antiZionismBoundaryReceipt = jewryReceipt
  antiZionismNotAutomaticallyAntisemitism scholarlyHistory
  "Historical scholarship on Jewish anti-Zionism, including Thomas Kolsky; Shaul Magid and Zev Mishell"
  "Jewish anti-Zionist and non-Zionist traditions demonstrate that Jewish identity and Zionist political ideology are not extensionally identical."

record GlobalJewryBoundary : Set where
  constructor globalJewryBoundary
  field
    israelPolicyMakesJewsCollectivelyResponsible : Bool
    israelPolicyMakesJewsCollectivelyResponsibleIsFalse : israelPolicyMakesJewsCollectivelyResponsible ≡ false
    zionistPoliticalResponsibilityInheritedByAllJews : Bool
    zionistPoliticalResponsibilityInheritedByAllJewsIsFalse : zionistPoliticalResponsibilityInheritedByAllJews ≡ false
    warningThatPolicyFuelsAntisemitismExcusesAntisemitism : Bool
    warningThatPolicyFuelsAntisemitismExcusesAntisemitismIsFalse : warningThatPolicyFuelsAntisemitismExcusesAntisemitism ≡ false
    criticismOfZionismAutomaticallyTargetsJews : Bool
    criticismOfZionismAutomaticallyTargetsJewsIsFalse : criticismOfZionismAutomaticallyTargetsJews ≡ false

canonicalGlobalJewryBoundary : GlobalJewryBoundary
canonicalGlobalJewryBoundary =
  globalJewryBoundary false refl false refl false refl false refl
