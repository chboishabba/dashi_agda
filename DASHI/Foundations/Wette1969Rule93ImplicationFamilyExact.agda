module DASHI.Foundations.Wette1969Rule93ImplicationFamilyExact where

------------------------------------------------------------------------
-- WETTE 1969: THE FINITE 9.3 IMPLICATION-RULE SEARCH CARRIER
--
-- Direct inspection of printed p.145 and Wette's discussion in 1.61 fixes the
-- implication-rule family as exactly 9.3.1--30.  This module recovers the
-- source-stable finite address carrier without pretending that all thirty dense
-- historical rule bodies have already been transcribed.
--
-- Primary source:
-- Eduard Wette, 1969, DOI 10.1007/978-3-642-86745-3_9,
-- printed p.145 (rule table) and p.150, section 1.61 ("30 Implikationsregeln
-- 9.3").
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Fin as Fin

import DASHI.Foundations.Wette1969RuleRevisionExact as Revision

ImplicationRule93 : Set
ImplicationRule93 = Fin.Fin 30

rule93Address : ImplicationRule93 → Revision.HistoricalRuleAddress
rule93Address candidate =
  Revision.historicalRuleAddress 9 3 (suc (Fin.toℕ candidate))

firstRule93Address : Revision.HistoricalRuleAddress
firstRule93Address = Revision.historicalRuleAddress 9 3 1

lastRule93Address : Revision.HistoricalRuleAddress
lastRule93Address = Revision.historicalRuleAddress 9 3 30

implicationRule93Count : Nat
implicationRule93Count = 30

printedRuleTablePage : Nat
printedRuleTablePage = 145

section161PrintedPage : Nat
section161PrintedPage = 150

record Wette1969Rule93ImplicationFamilyBoundary : Set where
  constructor wette1969Rule93ImplicationFamilyBoundary
  field
    sourceCalls93TheThirtyImplicationRules : Bool
    sourceCalls93TheThirtyImplicationRulesIsTrue :
      sourceCalls93TheThirtyImplicationRules ≡ true

    finiteCarrierHasThirtyAddresses : Bool
    finiteCarrierHasThirtyAddressesIsTrue :
      finiteCarrierHasThirtyAddresses ≡ true

    carrierRunsFrom931Through9330 : Bool
    carrierRunsFrom931Through9330IsTrue :
      carrierRunsFrom931Through9330 ≡ true

    allThirtyDenseRuleBodiesAlreadyTranscribed : Bool
    allThirtyDenseRuleBodiesAlreadyTranscribedIsFalse :
      allThirtyDenseRuleBodiesAlreadyTranscribed ≡ false

    finiteAddressRecoveryAlreadyDecidesPremise18 : Bool
    finiteAddressRecoveryAlreadyDecidesPremise18IsFalse :
      finiteAddressRecoveryAlreadyDecidesPremise18 ≡ false

canonicalWette1969Rule93ImplicationFamilyBoundary :
  Wette1969Rule93ImplicationFamilyBoundary
canonicalWette1969Rule93ImplicationFamilyBoundary =
  wette1969Rule93ImplicationFamilyBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
