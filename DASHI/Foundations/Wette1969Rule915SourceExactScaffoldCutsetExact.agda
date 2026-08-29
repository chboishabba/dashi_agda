module DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: SOURCE-EXACT GENERATED SCAFFOLD -> TWO PROOFS
--
-- Every non-major premise is required to be an actual historical rule
-- conclusion.  The four producer blocks are sequentially state-indexed, and
-- monotonic finite-context transport moves every produced formula to one final
-- context.  Exactly premises 18 and 27 remain as substantive proof sockets.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969Rule915TwoProofCutsetExact as Cutset
import DASHI.Foundations.Wette1969Rule915FormationProducerExact as Formation
import DASHI.Foundations.Wette1969Rule915Shared1015ProducerExact as Shared
import DASHI.Foundations.Wette1969Rule915InductionScaffoldProducerExact as Induction
import DASHI.Foundations.Wette1969Rule915IndependenceScaffoldProducerExact as Independence
import DASHI.Foundations.Wette1969Rule915SeparatedMajorProofsExact as Major
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Signature.WordTerm
Formula = Signature.Formula
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record SourceExactScaffoldInputs
    (initial : Context)
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters) : Set₁ where
  constructor sourceExactScaffoldInputs
  field
    formation : Formation.FormationProducerChain initial firstSeven later
    shared1015 : Shared.Shared1015ProducerChain (Formation.formationTarget formation) firstSeven later
    inductionScaffold : Induction.InductionScaffoldProducerChain (Shared.sharedTarget shared1015) later
    independenceScaffold : Independence.IndependenceScaffoldProducerChain (Induction.inductionScaffoldTarget inductionScaffold) later
open SourceExactScaffoldInputs public

sourceExactScaffoldTarget :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  SourceExactScaffoldInputs initial firstSeven later → Context
sourceExactScaffoldTarget inputs = Independence.independenceScaffoldTarget (independenceScaffold inputs)

liftFromInduction :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (inputs : SourceExactScaffoldInputs initial firstSeven later) →
  (formula : Formula) →
  formula Finite.∈Context (Induction.inductionScaffoldTarget (inductionScaffold inputs)) →
  formula Finite.∈Context (sourceExactScaffoldTarget inputs)
liftFromInduction inputs formula evidence =
  Independence.independenceScaffoldPreservesPriorFormula
    (independenceScaffold inputs) formula evidence

liftFromShared :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (inputs : SourceExactScaffoldInputs initial firstSeven later) →
  (formula : Formula) →
  formula Finite.∈Context (Shared.sharedTarget (shared1015 inputs)) →
  formula Finite.∈Context (sourceExactScaffoldTarget inputs)
liftFromShared inputs formula evidence =
  liftFromInduction inputs formula
    (Induction.inductionScaffoldPreservesPriorFormula
      (inductionScaffold inputs) formula evidence)

liftFromFormation :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (inputs : SourceExactScaffoldInputs initial firstSeven later) →
  (formula : Formula) →
  formula Finite.∈Context (Formation.formationTarget (formation inputs)) →
  formula Finite.∈Context (sourceExactScaffoldTarget inputs)
liftFromFormation inputs formula evidence =
  liftFromShared inputs formula
    (Shared.sharedPreservesPriorFormula (shared1015 inputs) formula evidence)

shared1015AtSourceExactTarget :
  {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (inputs : SourceExactScaffoldInputs initial firstSeven later) →
  Obligations.Shared1015Evidence
    (sourceExactScaffoldTarget inputs)
    (Later.completeTypedTranscription firstSeven later)
shared1015AtSourceExactTarget inputs =
  Obligations.shared1015Evidence
    (liftFromShared inputs _ (Obligations.e10 shared))
    (liftFromShared inputs _ (Obligations.e11 shared))
    (liftFromShared inputs _ (Obligations.e12 shared))
    (liftFromShared inputs _ (Obligations.e13 shared))
    (liftFromShared inputs _ (Obligations.e14 shared))
    (liftFromShared inputs _ (Obligations.e15 shared))
  where
    shared = Shared.sharedEvidenceAtTarget (shared1015 inputs)

scaffoldEvidenceAtSourceExactTarget :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (inputs : SourceExactScaffoldInputs initial firstSeven later) →
  Cutset.Rule915SyntacticScaffoldEvidence
    (sourceExactScaffoldTarget inputs) firstSeven later
scaffoldEvidenceAtSourceExactTarget firstSeven later inputs =
  Cutset.rule915SyntacticScaffoldEvidence
    (liftFromFormation inputs _ (Obligations.e01 formationEvidence))
    (liftFromFormation inputs _ (Obligations.e02 formationEvidence))
    (liftFromFormation inputs _ (Obligations.e03 formationEvidence))
    (liftFromFormation inputs _ (Obligations.e04 formationEvidence))
    (liftFromFormation inputs _ (Obligations.e05 formationEvidence))
    (liftFromFormation inputs _ (Obligations.e06 formationEvidence))
    (liftFromFormation inputs _ (Obligations.e07 formationEvidence))
    (liftFromInduction inputs _ (Induction.p08AtTarget inductionEvidence))
    (liftFromInduction inputs _ (Induction.p09AtTarget inductionEvidence))
    (Obligations.e10 sharedFinal) (Obligations.e11 sharedFinal)
    (Obligations.e12 sharedFinal) (Obligations.e13 sharedFinal)
    (Obligations.e14 sharedFinal) (Obligations.e15 sharedFinal)
    (liftFromInduction inputs _ (Induction.p16AtTarget inductionEvidence))
    (liftFromInduction inputs _ (Induction.p17AtTarget inductionEvidence))
    (Independence.p19AtTarget independenceEvidence)
    (Independence.p20AtTarget independenceEvidence)
    (Independence.p21AtTarget independenceEvidence)
    (Independence.p22AtTarget independenceEvidence)
    (Independence.p23AtTarget independenceEvidence)
    (Independence.p24AtTarget independenceEvidence)
    (Independence.p25AtTarget independenceEvidence)
    (Independence.p26AtTarget independenceEvidence)
  where
    formationEvidence = Formation.formationEvidenceAtTarget (formation inputs)
    inductionEvidence = inductionScaffold inputs
    independenceEvidence = independenceScaffold inputs
    sharedFinal = shared1015AtSourceExactTarget inputs

record SourceExactTwoMajorProofs
    {initial : Context}
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters)
    (inputs : SourceExactScaffoldInputs initial firstSeven later) : Set where
  constructor sourceExactTwoMajorProofs
  field
    induction : Major.PredecessorInductionDischarge
      (sourceExactScaffoldTarget inputs) firstSeven later
      (shared1015AtSourceExactTarget inputs)
    independence : Major.DefiniensIndependenceDischarge
      (sourceExactScaffoldTarget inputs) firstSeven later
      (shared1015AtSourceExactTarget inputs)
open SourceExactTwoMajorProofs public

majorDischarges :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (inputs : SourceExactScaffoldInputs initial firstSeven later) →
  SourceExactTwoMajorProofs firstSeven later inputs →
  Major.SharedMajorDischarges (sourceExactScaffoldTarget inputs) firstSeven later
majorDischarges firstSeven later inputs proofs =
  Major.sharedMajorDischarges
    (shared1015AtSourceExactTarget inputs)
    (induction proofs)
    (independence proofs)

selectRule915SourceExactCutset :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (recursivePredicate : WordTerm) →
  (inputs : SourceExactScaffoldInputs initial firstSeven later) →
  SourceExactTwoMajorProofs firstSeven later inputs →
  PCRA.SelectedRuleApplication historicalSystem (sourceExactScaffoldTarget inputs)
selectRule915SourceExactCutset firstSeven later recursivePredicate inputs proofs =
  Cutset.selectRule915FromTwoProofCutset
    firstSeven later recursivePredicate
    (scaffoldEvidenceAtSourceExactTarget firstSeven later inputs)
    (Major.asTwoProofEvidence (majorDischarges firstSeven later inputs proofs))

record Wette1969Rule915SourceExactScaffoldCutsetBoundary : Set where
  constructor wette1969Rule915SourceExactScaffoldCutsetBoundary
  field
    premise9CorrectionIsBuiltIntoGeneratedScaffold : Bool
    premise9CorrectionIsBuiltIntoGeneratedScaffoldIsTrue : premise9CorrectionIsBuiltIntoGeneratedScaffold ≡ true
    everyNonMajorSlot1To27MustBeActualHistoricalConclusion : Bool
    everyNonMajorSlot1To27MustBeActualHistoricalConclusionIsTrue : everyNonMajorSlot1To27MustBeActualHistoricalConclusion ≡ true
    shared1015IsOneObjectConsumedByBothMajorBranches : Bool
    shared1015IsOneObjectConsumedByBothMajorBranchesIsTrue : shared1015IsOneObjectConsumedByBothMajorBranches ≡ true
    exactRemainingMajorCutsetIs18And27 : Bool
    exactRemainingMajorCutsetIs18And27IsTrue : exactRemainingMajorCutsetIs18And27 ≡ true
    syntacticProductionUniversallyDischarges18Or27 : Bool
    syntacticProductionUniversallyDischarges18Or27IsFalse : syntacticProductionUniversallyDischarges18Or27 ≡ false

canonicalWette1969Rule915SourceExactScaffoldCutsetBoundary : Wette1969Rule915SourceExactScaffoldCutsetBoundary
canonicalWette1969Rule915SourceExactScaffoldCutsetBoundary =
  wette1969Rule915SourceExactScaffoldCutsetBoundary true refl true refl true refl true refl false refl
