module DASHI.Foundations.Wette1969Rule915ZeroArityFalsumMajorsExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969Rule915TwoProofCutsetExact as Cutset
import DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact as Source
import DASHI.Foundations.Wette1969Rule915IndependentMajorTraceJoinExact as Join
import DASHI.Foundations.Wette1969Rule915ZeroArityFalsumInstanceExact as I
import DASHI.Foundations.Wette1969Rule915ZeroArityFalsumScaffoldExact as Scaffold
import DASHI.Foundations.Wette1969ZeroArityWitnessRulesExact as R
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

start : Context
start = Source.sourceExactScaffoldTarget Scaffold.canonicalScaffold

scaffoldEvidence :
  Cutset.Rule915SyntacticScaffoldEvidence start I.canonicalFirstSeven I.canonicalLater
scaffoldEvidence = Source.scaffoldEvidenceAtSourceExactTarget
  I.canonicalFirstSeven I.canonicalLater Scaffold.canonicalScaffold

------------------------------------------------------------------------
-- D18: build A Phi18, then Wette 9.3.11 (ex falso).
------------------------------------------------------------------------

d18Trace : PCRA.CertifiedRuleTrace historicalSystem start
d18Trace =
  PCRA.choose sAT
    (PCRA.choose sPQ
      (PCRA.choose s61
        (PCRA.choose sAQ
          (PCRA.choose sTQ
            (PCRA.choose sU2
              (PCRA.choose sU2Q
                (PCRA.choose sU3
                  (PCRA.choose sFQ
                    (PCRA.choose sPhi (PCRA.choose sEx PCRA.done))))))))))
  where
    af0 = Cutset.p07 scaffoldEvidence
    noPredT0 = Cutset.p06 scaffoldEvidence
    mark0 = Cutset.p08 scaffoldEvidence

    sAT = R.select1 start (R.rule920 I.trueAssertion) _ refl noPredT0
    c1 = PCRA.applySelected historicalSystem sAT
    at1 = Closure.certifiedConclusionAvailable start sAT
    af1 = Closure.certifiedStepPreservesPriorFormula start sAT _ af0
    mark1 = Closure.certifiedStepPreservesPriorFormula start sAT _ mark0

    sPQ = R.select1 c1 (R.rule914 I.zeroWord I.mark0) _ refl mark1
    c2 = PCRA.applySelected historicalSystem sPQ
    pq2 = Closure.certifiedConclusionAvailable c1 sPQ
    at2 = Closure.certifiedStepPreservesPriorFormula c1 sPQ _ at1
    af2 = Closure.certifiedStepPreservesPriorFormula c1 sPQ _ af1

    s61 = R.select0 c2 R.rule61 refl
    c3 = PCRA.applySelected historicalSystem s61
    tuple3 = Closure.certifiedConclusionAvailable c2 s61
    pq3 = Closure.certifiedStepPreservesPriorFormula c2 s61 _ pq2
    at3 = Closure.certifiedStepPreservesPriorFormula c2 s61 _ at2
    af3 = Closure.certifiedStepPreservesPriorFormula c2 s61 _ af2

    sAQ = R.select2 c3 (R.rule921 I.zeroWord I.emptyWord I.mark0)
      _ _ refl tuple3 pq3
    c4 = PCRA.applySelected historicalSystem sAQ
    aq4 = Closure.certifiedConclusionAvailable c3 sAQ
    at4 = Closure.certifiedStepPreservesPriorFormula c3 sAQ _ at3
    af4 = Closure.certifiedStepPreservesPriorFormula c3 sAQ _ af3

    sTQ = R.select2 c4 (R.rule922 I.trueAssertion I.markAssertion)
      _ _ refl at4 aq4
    c5 = PCRA.applySelected historicalSystem sTQ
    atq5 = Closure.certifiedConclusionAvailable c4 sTQ
    aq5 = Closure.certifiedStepPreservesPriorFormula c4 sTQ _ aq4
    af5 = Closure.certifiedStepPreservesPriorFormula c4 sTQ _ af4

    sU2 = R.select2 c5 (R.rule922 I.falseAssertion
      (I.implication I.trueAssertion I.markAssertion))
      _ _ refl af5 atq5
    c6 = PCRA.applySelected historicalSystem sU2
    au2 = Closure.certifiedConclusionAvailable c5 sU2
    aq6 = Closure.certifiedStepPreservesPriorFormula c5 sU2 _ aq5
    af6 = Closure.certifiedStepPreservesPriorFormula c5 sU2 _ af5

    sU2Q = R.select2 c6 (R.rule922 I.body16 I.markAssertion)
      _ _ refl au2 aq6
    c7 = PCRA.applySelected historicalSystem sU2Q
    au2q = Closure.certifiedConclusionAvailable c6 sU2Q
    aq7 = Closure.certifiedStepPreservesPriorFormula c6 sU2Q _ aq6
    af7 = Closure.certifiedStepPreservesPriorFormula c6 sU2Q _ af6

    sU3 = R.select2 c7 (R.rule922 I.falseAssertion
      (I.implication I.body16 I.markAssertion))
      _ _ refl af7 au2q
    c8 = PCRA.applySelected historicalSystem sU3
    au3 = Closure.certifiedConclusionAvailable c7 sU3
    aq8 = Closure.certifiedStepPreservesPriorFormula c7 sU3 _ aq7
    af8 = Closure.certifiedStepPreservesPriorFormula c7 sU3 _ af7

    sFQ = R.select2 c8 (R.rule922 I.falseAssertion I.markAssertion)
      _ _ refl af8 aq8
    c9 = PCRA.applySelected historicalSystem sFQ
    afq = Closure.certifiedConclusionAvailable c8 sFQ
    au3' = Closure.certifiedStepPreservesPriorFormula c8 sFQ _ au3

    sPhi = R.select2 c9 (R.rule922 I.body17
      (I.implication I.falseAssertion I.markAssertion))
      _ _ refl au3' afq
    c10 = PCRA.applySelected historicalSystem sPhi
    aPhi = Closure.certifiedConclusionAvailable c9 sPhi

    sEx = R.select1 c10 (R.rule9311 I.premise18Consequent) _ refl aPhi

d18 : Join.CertifiedMajorTrace start
  (DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact.premise18 I.canonicalLater)
d18 = Join.certifiedMajorTrace d18Trace Finite.here

------------------------------------------------------------------------
-- D27: the same false antecedent closes the independence consequent.
------------------------------------------------------------------------

d27Trace : PCRA.CertifiedRuleTrace historicalSystem start
d27Trace =
  PCRA.choose sAT
    (PCRA.choose sTT
      (PCRA.choose sPair
        (PCRA.choose sTPair
          (PCRA.choose sU6
            (PCRA.choose sU6Pair
              (PCRA.choose sPhi (PCRA.choose sEx PCRA.done)))))))
  where
    af0 = Cutset.p07 scaffoldEvidence
    noPredT0 = Cutset.p06 scaffoldEvidence

    sAT = R.select1 start (R.rule920 I.trueAssertion) _ refl noPredT0
    c1 = PCRA.applySelected historicalSystem sAT
    at1 = Closure.certifiedConclusionAvailable start sAT
    af1 = Closure.certifiedStepPreservesPriorFormula start sAT _ af0

    sTT = R.select2 c1 (R.rule922 I.trueAssertion I.trueAssertion)
      _ _ refl at1 at1
    c2 = PCRA.applySelected historicalSystem sTT
    att = Closure.certifiedConclusionAvailable c1 sTT
    at2 = Closure.certifiedStepPreservesPriorFormula c1 sTT _ at1
    af2 = Closure.certifiedStepPreservesPriorFormula c1 sTT _ af1

    sPair = R.select2 c2 (R.rule923 I.sameDirection I.sameDirection)
      _ _ refl att att
    c3 = PCRA.applySelected historicalSystem sPair
    apair = Closure.certifiedConclusionAvailable c2 sPair
    at3 = Closure.certifiedStepPreservesPriorFormula c2 sPair _ at2
    af3 = Closure.certifiedStepPreservesPriorFormula c2 sPair _ af2

    sTPair = R.select2 c3 (R.rule922 I.trueAssertion I.directionPair)
      _ _ refl at3 apair
    c4 = PCRA.applySelected historicalSystem sTPair
    atpair = Closure.certifiedConclusionAvailable c3 sTPair
    apair4 = Closure.certifiedStepPreservesPriorFormula c3 sTPair _ apair
    af4 = Closure.certifiedStepPreservesPriorFormula c3 sTPair _ af3

    sU6 = R.select2 c4 (R.rule922 I.falseAssertion
      (I.implication I.trueAssertion I.directionPair))
      _ _ refl af4 atpair
    c5 = PCRA.applySelected historicalSystem sU6
    au6 = Closure.certifiedConclusionAvailable c4 sU6
    apair5 = Closure.certifiedStepPreservesPriorFormula c4 sU6 _ apair4
    af5 = Closure.certifiedStepPreservesPriorFormula c4 sU6 _ af4

    sU6Pair = R.select2 c5 (R.rule922 I.body26 I.directionPair)
      _ _ refl au6 apair5
    c6 = PCRA.applySelected historicalSystem sU6Pair
    au6pair = Closure.certifiedConclusionAvailable c5 sU6Pair
    af6 = Closure.certifiedStepPreservesPriorFormula c5 sU6Pair _ af5

    sPhi = R.select2 c6 (R.rule922 I.falseAssertion
      (I.implication I.body26 I.directionPair))
      _ _ refl af6 au6pair
    c7 = PCRA.applySelected historicalSystem sPhi
    aPhi = Closure.certifiedConclusionAvailable c6 sPhi

    sEx = R.select1 c7 (R.rule9311 I.premise27Consequent) _ refl aPhi

d27 : Join.CertifiedMajorTrace start
  (DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact.premise27 I.canonicalLater)
d27 = Join.certifiedMajorTrace d27Trace Finite.here

independentMajors :
  Join.IndependentMajorTraceInputs
    I.canonicalFirstSeven I.canonicalLater Scaffold.canonicalScaffold
independentMajors = Join.independentMajorTraceInputs d18 d27

joinedTrace : PCRA.CertifiedRuleTrace historicalSystem start
joinedTrace = Join.joinedMajorTrace independentMajors

record Wette1969Rule915ZeroArityFalsumMajorsBoundary : Set where
  constructor wette1969Rule915ZeroArityFalsumMajorsBoundary
  field
    d18IsActualCertifiedHistoricalTrace : Bool
    d18IsActualCertifiedHistoricalTraceIsTrue : d18IsActualCertifiedHistoricalTrace ≡ true
    d27IsActualIndependentCertifiedHistoricalTrace : Bool
    d27IsActualIndependentCertifiedHistoricalTraceIsTrue : d27IsActualIndependentCertifiedHistoricalTrace ≡ true
    bothMajorProofsUseSourceDeclaredRule9311ExFalso : Bool
    bothMajorProofsUseSourceDeclaredRule9311ExFalsoIsTrue : bothMajorProofsUseSourceDeclaredRule9311ExFalso ≡ true
    existingIndependentReplayJoinConsumesBothTraces : Bool
    existingIndependentReplayJoinConsumesBothTracesIsTrue : existingIndependentReplayJoinConsumesBothTraces ≡ true

canonicalWette1969Rule915ZeroArityFalsumMajorsBoundary :
  Wette1969Rule915ZeroArityFalsumMajorsBoundary
canonicalWette1969Rule915ZeroArityFalsumMajorsBoundary =
  wette1969Rule915ZeroArityFalsumMajorsBoundary true refl true refl true refl true refl
