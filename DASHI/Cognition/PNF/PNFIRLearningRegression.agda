module DASHI.Cognition.PNF.PNFIRLearningRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)

import DASHI.Cognition.Utterance.LayeredMeaningCore as U
import DASHI.Interop.SensibLawResidualLattice as R
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.OperationalIR as IR
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.BraidLearningTransport as Braid

surface : U.SourceSurface
surface = U.sourceSurface "text" "tenant" ("tenant may arrange repairs" ∷ []) U.observedSurface

atom : U.TextAtom surface
atom = U.textAtom "tenant may arrange repairs"

speaker : U.TypedReferent
speaker =
  U.typedReferent "tenant" "local:tenant" "legal-person-role"
    U.liveHuman "actor" (U.unknownRupture ∷ [])

frame : U.DerivedCandidate surface
frame = U.derivedCandidate "permission reading" (atom ∷ []) U.explicitGrammar true refl

qualifiers : U.QualifierState
qualifiers = U.qualifierState "permission" "candidate" "present" "positive"

wrapper : U.WrapperState
wrapper = U.wrapperState U.observedSurface U.candidateDemoted U.symbolicAdmissible false refl

utterance : U.PredicatePNF surface
utterance = U.predicatePNF "arrange-repair" speaker surface frame [] qualifiers wrapper

algebraicAtom : R.PredicatePNF
algebraicAtom =
  R.predicatePNF
    "arrange-repair"
    R.sig-agent-goal
    (R.opaqueArg "tenant")
    (R.opaqueArg "repair")
    (R.opaqueArg "premises")
    R.modal
    R.directEvidence
    "doc:0-26"

span : PNF.SpanReceipt
span = PNF.spanReceipt "doc" 0 26 0 4 PNF.ruleProducer "explicitGrammar"

observation : PNF.ParserObservation
observation = PNF.parserObservation PNF.ruleProducer "legal-rule-parser" "en" span "permission" 100

event : PNF.EventPNF
event =
  PNF.eventPNF surface utterance algebraicAtom
    (PNF.actorRole ∷ PNF.actionRole ∷ PNF.modalityRole ∷ [])
    (observation ∷ [])
    "event-time" "publication-time" "observation-time" "ingestion-time"
    "tenancy" "Queensland" 0 "root"

candidate : PNF.CandidatePNF
candidate = PNF.candidatePNF event PNF.admissible "candidate-1" true refl

admitted : PNF.AdmissiblePNF
admitted = PNF.admissiblePNF candidate refl

resolved : PNF.ResolvedPNF
resolved = PNF.resolvedPNF admitted [] R.exact "resolver-1" "selector-1"

legalIR : IR.DomainIR
legalIR =
  IR.legalProjection resolved "tenant" "arrange repair" "repair"
    "permission" "lessor fails to act" "none" "Queensland"

memory : Memory.MemoryFibre
memory = Memory.memoryFibre event 1 3 2 0 1 "contextual retrieval" "observe" "memory-1"

revaluedContentStable :
  Memory.rememberedEvent (Memory.revalue memory 7) ≡ event
revaluedContentStable = refl

habituatedContentStable :
  Memory.rememberedEvent (Memory.habituate memory) ≡ event
habituatedContentStable = refl

reinforcementIncreasesWeight :
  Memory.actionWeight (Memory.reinforce memory) ≡ 2
reinforcementIncreasesWeight = refl

revaluationKindClosed :
  Learning.learningKind (Learning.revaluationReceipt memory 7)
    ≡ Learning.revaluationLearning
revaluationKindClosed = refl

braidOrderRetainsResidualDifference :
  Braid.comparison Braid.canonicalNonCommutingBraid
    ≡ Braid.residuallyDifferent
braidOrderRetainsResidualDifference = refl

legalIRIsOperationallyValid :
  IR.validationState legalIR ≡ IR.operationallyValid
legalIRIsOperationallyValid = refl
