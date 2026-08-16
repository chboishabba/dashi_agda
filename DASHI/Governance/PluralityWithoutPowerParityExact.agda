module DASHI.Governance.PluralityWithoutPowerParityExact where

------------------------------------------------------------------------
-- PLURALITY WITHOUT POWER PARITY
--
-- Nominal eligibility/plurality can coexist with highly unequal institutional
-- realization.  Legal correction can also leave material institutional
-- structure substantially intact.  These are separate propositions.
--
-- Sources / bounded roles:
--
-- Renae Barker,
-- "A Critical Analysis of Religious Aspects of the Australian Chaplaincy
-- Cases", Oxford Journal of Law and Religion 4(1):26-53 (2015),
-- DOI 10.1093/ojlr/rwv002.
-- Source role: historical/legal analysis of the Australian school chaplaincy
-- program and both Williams proceedings; not proof that every chaplaincy
-- arrangement is coercive.
--
-- High Court of Australia, Williams v Commonwealth [2012] HCA 23,
-- 20 June 2012; no DOI asserted.
-- High Court of Australia, Williams v Commonwealth [2014] HCA 23,
-- 19 June 2014; no DOI asserted.
-- Source role: exact constitutional holdings on Commonwealth funding/executive
-- power.  Section 116 did not supply the successful ground of decision.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record InstitutionalPlurality : Set where
  constructor institutionalPlurality
  field
    nominalEligibleGroups : Nat
    realisedDominantGroups : Nat
    legalChallengeSucceeded : Bool
    institutionalProgramContinued : Bool

chaplaincyWitness : InstitutionalPlurality
chaplaincyWitness = institutionalPlurality 5 1 true true

data NominalPluralityPromotesPowerParity : Set where

data LegalVictoryPromotesInstitutionalDislodgement : Set where

data DominantRealisationPromotesCoercion : Set where

nominalPluralityDoesNotPromotePowerParity : NominalPluralityPromotesPowerParity → ⊥
nominalPluralityDoesNotPromotePowerParity ()

legalVictoryDoesNotPromoteInstitutionalDislodgement :
  LegalVictoryPromotesInstitutionalDislodgement → ⊥
legalVictoryDoesNotPromoteInstitutionalDislodgement ()

dominantRealisationDoesNotPromoteCoercion : DominantRealisationPromotesCoercion → ⊥
dominantRealisationDoesNotPromoteCoercion ()

record PluralityWithoutPowerParityBoundary : Set where
  constructor pluralityWithoutPowerParityBoundary
  field
    nominalPluralityEqualsInstitutionalParity : Bool
    legalCorrectionEqualsMaterialDislodgement : Bool
    dominantInstitutionalRealisationCanPersistAfterLegalCorrection : Bool
    religiousDominanceEqualsCoercion : Bool
    legalHoldingAndReligiousMeritsRemainDistinct : Bool

canonicalPluralityWithoutPowerParityBoundary : PluralityWithoutPowerParityBoundary
canonicalPluralityWithoutPowerParityBoundary =
  pluralityWithoutPowerParityBoundary false false true false true
