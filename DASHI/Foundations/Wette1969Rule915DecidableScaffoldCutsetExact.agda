module DASHI.Foundations.Wette1969Rule915DecidableScaffoldCutsetExact where

------------------------------------------------------------------------
-- WETTE 1969: 20 L-CAUSED PREMISES = 18 SYNTACTIC SCAFFOLD + 2 L PROOFS
--
-- Section 1.632 says twenty premises of 9.1.5 are caused by L and singles out
-- premise 18 and premise 27 as the two decisive proof conditions.  The other
-- eighteen slots use the syntactic relators for mark formation, J, variable
-- tuples, juxtaposition result, abbreviation and II.
--
-- Section 1.4 separately says that the subcalculus left after deleting 9.1--3
-- is decidable.  This makes the architectural cut especially important:
-- source-level syntactic side-condition decidability and the two L proof
-- obligations should not be conflated.
--
-- We record that historical claim as a source receipt, not as a newly proved
-- decision procedure for the Agda reconstruction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical


data LPremiseRole : Set where
  decidableSyntacticScaffold : LPremiseRole
  majorImplicationProof : LPremiseRole

lPremiseRole : Critical.Premise915 → LPremiseRole
lPremiseRole Critical.p08 = decidableSyntacticScaffold
lPremiseRole Critical.p09 = decidableSyntacticScaffold
lPremiseRole Critical.p10 = decidableSyntacticScaffold
lPremiseRole Critical.p11 = decidableSyntacticScaffold
lPremiseRole Critical.p12 = decidableSyntacticScaffold
lPremiseRole Critical.p13 = decidableSyntacticScaffold
lPremiseRole Critical.p14 = decidableSyntacticScaffold
lPremiseRole Critical.p15 = decidableSyntacticScaffold
lPremiseRole Critical.p16 = decidableSyntacticScaffold
lPremiseRole Critical.p17 = decidableSyntacticScaffold
lPremiseRole Critical.p18 = majorImplicationProof
lPremiseRole Critical.p19 = decidableSyntacticScaffold
lPremiseRole Critical.p20 = decidableSyntacticScaffold
lPremiseRole Critical.p21 = decidableSyntacticScaffold
lPremiseRole Critical.p22 = decidableSyntacticScaffold
lPremiseRole Critical.p23 = decidableSyntacticScaffold
lPremiseRole Critical.p24 = decidableSyntacticScaffold
lPremiseRole Critical.p25 = decidableSyntacticScaffold
lPremiseRole Critical.p26 = decidableSyntacticScaffold
lPremiseRole Critical.p27 = majorImplicationProof
-- First seven are outside the §1.632 twenty-premise L block; their value here
-- is intentionally irrelevant to the L-block classifier.
lPremiseRole Critical.p01 = decidableSyntacticScaffold
lPremiseRole Critical.p02 = decidableSyntacticScaffold
lPremiseRole Critical.p03 = decidableSyntacticScaffold
lPremiseRole Critical.p04 = decidableSyntacticScaffold
lPremiseRole Critical.p05 = decidableSyntacticScaffold
lPremiseRole Critical.p06 = decidableSyntacticScaffold
lPremiseRole Critical.p07 = decidableSyntacticScaffold

premise18IsMajorProof : lPremiseRole Critical.p18 ≡ majorImplicationProof
premise18IsMajorProof = refl

premise27IsMajorProof : lPremiseRole Critical.p27 ≡ majorImplicationProof
premise27IsMajorProof = refl

premise10IsSharedSyntacticScaffold :
  lPremiseRole Critical.p10 ≡ decidableSyntacticScaffold
premise10IsSharedSyntacticScaffold = refl

-- Source-count receipt: the §1.632 L block has twenty positions; eighteen are
-- scaffold slots and two are the decisive L-proof sockets.
lBlockCountDecomposition : 20 ≡ 18 + 2
lBlockCountDecomposition = refl

record HistoricalDecidabilityReceipt : Set where
  constructor historicalDecidabilityReceipt
  field
    sourceSaysSubcalculusWithout9IsDecidable : Bool
    sourceSaysSubcalculusWithout9IsDecidableIsTrue :
      sourceSaysSubcalculusWithout9IsDecidable ≡ true
    agdaDecisionProcedureForWholeSubcalculusNowImplemented : Bool
    agdaDecisionProcedureForWholeSubcalculusNowImplementedIsFalse :
      agdaDecisionProcedureForWholeSubcalculusNowImplemented ≡ false

canonicalHistoricalDecidabilityReceipt : HistoricalDecidabilityReceipt
canonicalHistoricalDecidabilityReceipt =
  historicalDecidabilityReceipt true refl false refl

record Wette1969Rule915DecidableScaffoldCutsetBoundary : Set where
  constructor wette1969Rule915DecidableScaffoldCutsetBoundary
  field
    twentyLCausedPremisesFactorAsEighteenScaffoldPlusTwoProofs : Bool
    twentyLCausedPremisesFactorAsEighteenScaffoldPlusTwoProofsIsTrue :
      twentyLCausedPremisesFactorAsEighteenScaffoldPlusTwoProofs ≡ true
    premise18And27AreOnlyMajorProofSlotsInLBlock : Bool
    premise18And27AreOnlyMajorProofSlotsInLBlockIsTrue :
      premise18And27AreOnlyMajorProofSlotsInLBlock ≡ true
    sourceDecidabilityClaimAlreadyEqualsImplementedAgdaDecider : Bool
    sourceDecidabilityClaimAlreadyEqualsImplementedAgdaDeciderIsFalse :
      sourceDecidabilityClaimAlreadyEqualsImplementedAgdaDecider ≡ false

canonicalWette1969Rule915DecidableScaffoldCutsetBoundary :
  Wette1969Rule915DecidableScaffoldCutsetBoundary
canonicalWette1969Rule915DecidableScaffoldCutsetBoundary =
  wette1969Rule915DecidableScaffoldCutsetBoundary
    true refl true refl false refl
