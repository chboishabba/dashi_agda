module DASHI.Wikimedia.Base369NumberTheoryNumerologyWrongTypeSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimJMathematicsNumberOEISSecondOrderQidSnowballExact as Qid
import DASHI.Wikimedia.Base369OEISWikidataTeslaSnowballExact as Base369
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- Q12479 NUMBER THEORY <> Q140732 NUMEROLOGY WRONGTYPE GATE
--
-- Wikidata explicitly records number theory as different-from numerology.
-- This does not ban cultural/history-of-ideas analysis of numerological claims;
-- it prevents such claims from paying mathematical proof or number-theoretic
-- source obligations merely because they share integers with formal results.
------------------------------------------------------------------------

data PropositionRole : Set where
  exactArithmetic theoremOrProof oeisSequenceIdentity formalCarrierMorphism
  empiricalObservation historicalAttribution culturalMotif numerologicalClaim
  unresolvedRole : PropositionRole

record TypedNumericProposition : Set where
  constructor typed-numeric-proposition
  field
    propositionReference : String
    role : PropositionRole
    subjectIdentity : String
    sourceIdentity : String
    numberTheoryAdmissible : Bool
    culturalAnalysisAdmissible : Bool
    createsTheoremAuthority : Bool
open TypedNumericProposition public

base369PowerIdentity : TypedNumericProposition
base369PowerIdentity = typed-numeric-proposition
  "3^3=27 / 3^9=19683"
  exactArithmetic
  "Base369 finite carriers"
  "repo-native arithmetic plus separately retained OEIS identities"
  true true false

tesla369Attribution : TypedNumericProposition
tesla369Attribution = typed-numeric-proposition
  "popular Tesla 3-6-9 attribution"
  historicalAttribution
  "Nikola Tesla/Q9036"
  "attribution source lane; primary quote source unresolved"
  false true false

numerologyConcept : TypedNumericProposition
numerologyConcept = typed-numeric-proposition
  "numerology as an external concept"
  numerologicalClaim
  "numerology/Q140732"
  "Wikidata identity only; not mathematical authority"
  false true false

numberTheoryConcept : TypedNumericProposition
numberTheoryConcept = typed-numeric-proposition
  "number theory external discipline identity"
  theoremOrProof
  "number theory/Q12479"
  "Wikidata identity plus separately attributed mathematical sources"
  true true false

record WrongTypeGateReceipt : Set where
  constructor wrongtype-gate-receipt
  field
    left : String
    right : String
    allPairsEligible : Bool
    exactWikidataDifferentFromCoordinate : Bool
    sharedNumeralsEnoughForNumberTheoryPromotion : Bool
    culturalComparisonStillAllowed : Bool
    proofPromotionRequiresIndependentReceipt : Bool
    failedFactorisationMaySnowballRoleAxis : Bool
open WrongTypeGateReceipt public

numberTheoryNumerologyGate : WrongTypeGateReceipt
numberTheoryNumerologyGate = wrongtype-gate-receipt
  "Q12479 number theory"
  "Q140732 numerology"
  true true false true true true

base369NumerologyInspectionGate : WrongTypeGateReceipt
base369NumerologyInspectionGate = wrongtype-gate-receipt
  "Base369 exact 3/6/9/27 arithmetic/carriers"
  "numerological/cultural 3-6-9 motifs"
  true true false true true true

------------------------------------------------------------------------
-- A failed FactorsThrough on the numeral alone is productive: it proposes the
-- role/source/carrier axis instead of suppressing the pair or promoting it.
------------------------------------------------------------------------

record NumericFactorsThroughAudit : Set where
  constructor numeric-factors-through-audit
  field
    observedNumeral : String
    leftContext : String
    rightContext : String
    numeralAloneSufficient : Bool
    roleAxisRequired : Bool
    sourceAxisRequired : Bool
    carrierAxisRequired : Bool
    snowballRepairScheduled : Bool
open NumericFactorsThroughAudit public

threeSixNineRoleCollision : NumericFactorsThroughAudit
threeSixNineRoleCollision = numeric-factors-through-audit
  "3/6/9"
  "formal cyclic/finite carrier and exact arithmetic"
  "historical/cultural/numerological motif"
  false true true true true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NumerologyPaysNumberTheoryProof : Set where
data SharedNumeralCreatesSameRole : Set where
data DifferentFromForbidsCulturalComparison : Set where
data CulturalAttributionCreatesArithmeticFalsehood : Set where

numerologyDoesNotPayProof : NumerologyPaysNumberTheoryProof → ⊥
numerologyDoesNotPayProof ()

sharedNumeralDoesNotCreateRole : SharedNumeralCreatesSameRole → ⊥
sharedNumeralDoesNotCreateRole ()

differentFromDoesNotBanComparison : DifferentFromForbidsCulturalComparison → ⊥
differentFromDoesNotBanComparison ()

culturalAttributionDoesNotNegateArithmetic : CulturalAttributionCreatesArithmeticFalsehood → ⊥
culturalAttributionDoesNotNegateArithmetic ()

record Base369NumberTheoryNumerologyBoundary : Set where
  constructor base369-number-theory-numerology-boundary
  field
    q12479AndQ140732Retained : Bool
    wikidataDifferentFromRetained : Bool
    allPairsEligibilityRetained : Bool
    mathematicalPromotionFirewalled : Bool
    culturalHistoryLaneRetained : Bool
    roleSourceCarrierAxesSnowball : Bool
open Base369NumberTheoryNumerologyBoundary public

canonicalBase369NumberTheoryNumerologyBoundary : Base369NumberTheoryNumerologyBoundary
canonicalBase369NumberTheoryNumerologyBoundary =
  base369-number-theory-numerology-boundary true true true true true true

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
