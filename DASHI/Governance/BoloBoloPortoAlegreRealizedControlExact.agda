module DASHI.Governance.BoloBoloPortoAlegreRealizedControlExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry
import DASHI.Governance.BoloBoloPortoAlegreCurrentProcessEvidenceExact as Current

------------------------------------------------------------------------
-- PORTO ALEGRE CURRENT REALISED-CONTROL COMPARATOR EVIDENCE
--
-- These are official municipal accounts of particular 2025/2026 OP events.
-- They pay bounded observations about who proposed, voted, questioned,
-- presented needs and responded.  They are not independent audits of equal
-- influence, hidden power, non-domination or causal effectiveness.
------------------------------------------------------------------------

porto20250121DecisionSource : Registry.SourceReference
porto20250121DecisionSource = Registry.source-reference
  "Prefeitura de Porto Alegre / SMGOV"
  "Conselho do Orçamento Participativo define valores e prazo para demandas de 2025"
  "official municipal event report, 2025-01-22"
  2025
  "https://prefeitura.poa.br/smgov/noticias/conselho-do-orcamento-participativo-define-valores-e-prazo-para-demandas-de-2025"
  "official current OP decision-flow source"
  "reports an extraordinary COP meeting where a deadline proposed by COP coordination was put to a vote and approved unanimously by councillors present; also reports a subsequent agenda item and named coordination/government participants; does not state full attendance"

porto20250204QuestionSource : Registry.SourceReference
porto20250204QuestionSource = Registry.source-reference
  "Prefeitura de Porto Alegre"
  "Orçamento Participativo faz sua primeira reunião ordinária do ano"
  "official municipal event report, 2025-02-05"
  2025
  "https://prefeitura.poa.br/gp/noticias/orcamento-participativo-faz-sua-primeira-reuniao-ordinaria-do-ano"
  "official current OP question/response-flow source"
  "reports a three-hour COP meeting in which government representatives and councillors discussed budgets/demands; councillors took turns questioning unexecuted demands and requested meetings with secretariats"

porto20250805AssemblySource : Registry.SourceReference
porto20250805AssemblySource = Registry.source-reference
  "Prefeitura de Porto Alegre / SMGOV"
  "Região Centro-Sul escolhe educação como prioridade de investimentos no OP"
  "official municipal assembly report, 2025-08-06"
  2025
  "https://prefeitura.poa.br/smgov/noticias/regiao-centro-sul-escolhe-educacao-como-prioridade-de-investimentos-no-op"
  "official current OP assembly voice/election source"
  "reports 586 registered participants choosing delegates, councillors and priorities; ten community speeches registered through the regional forum; current councillors on the working table; mayor/secretaries listened and responded"

porto20251122ElectionSource : Registry.SourceReference
porto20251122ElectionSource = Registry.source-reference
  "Prefeitura de Porto Alegre / SMGOV"
  "Prefeitura empossa novos conselheiros do Orçamento Participativo para a gestão 2025/2026"
  "official municipal inauguration report, 2025-11-22"
  2025
  "https://prefeitura.poa.br/gp/noticias/prefeitura-empossa-novos-conselheiros-do-orcamento-participativo-para-gestao-20252026"
  "official current OP representation source"
  "reports 92 representatives, 46 titulares and 46 suplentes, from 17 regions and six thematic streams for the 2025/2026 mandate"

porto20260317NeedsSource : Registry.SourceReference
porto20260317NeedsSource = Registry.source-reference
  "Prefeitura de Porto Alegre"
  "Prefeitura e Conselho do OP alinham demandas em reunião no Teatro Renascença"
  "official municipal event report, 2026-03-18"
  2026
  "https://prefeitura.poa.br/gp/noticias/prefeitura-e-conselho-do-op-alinham-demandas-em-reuniao-no-teatro-renascenca"
  "official current OP representative-to-government source"
  "reports regional/thematic representatives presenting needs, criticisms and suggestions to the mayor, secretariat and technical staff across multiple policy areas"

record PortoRealizedControlEvidence : Set where
  constructor porto-realized-control-evidence
  field
    coordinationProposalPutToVote : Bool
    unanimousAmongPresentReported : Bool
    fullAttendanceCountReported : Bool
    councillorsRotateQuestions : Bool
    governmentResponseSurface : Bool
    communitySpeechSlotsReported : Nat
    assemblyRegisteredParticipants : Nat
    assemblyElectsDelegatesAndCouncillors : Bool
    representativesPresentNeedsCriticismSuggestions : Bool
    titularCouncillorCount2025_2026 : Nat
    suplenteCouncillorCount2025_2026 : Nat

open PortoRealizedControlEvidence public

canonicalPortoRealizedControlEvidence : PortoRealizedControlEvidence
canonicalPortoRealizedControlEvidence =
  porto-realized-control-evidence
    true true false
    true true
    10 586 true true
    46 46

currentProcessAnchor : Current.PortoCurrentProcessBoundary
currentProcessAnchor = Current.canonicalPortoCurrentProcessBoundary

record PortoRealizedControlBoundary : Set where
  constructor porto-realized-control-boundary
  field
    officialCOPDecisionFlowObserved : Bool
    councillorQuestionGovernmentResponseObserved : Bool
    communitySpeechAndGovernmentResponseObserved : Bool
    delegateCouncillorElectionSurfaceObserved : Bool
    representativeNeedsCriticismSuggestionFlowObserved : Bool

    unanimousPresentVoteProvesAllCouncillorsPresent : Bool
    officialProcessAccountProvesEqualInfluence : Bool
    officialProcessAccountProvesNonDomination : Bool
    questionTurnTakingProvesAgendaEquality : Bool
    tenSpeechSlotsProvePopulationVoiceEquality : Bool
    electedRepresentationProvesEffectiveRecallContestability : Bool
    officialProcessEvidenceIdentifiesCausalGovernanceEffect : Bool
    comparatorObservationTransfersToTargetBolo : Bool

open PortoRealizedControlBoundary public

canonicalPortoRealizedControlBoundary : PortoRealizedControlBoundary
canonicalPortoRealizedControlBoundary =
  porto-realized-control-boundary
    true true true true true
    false false false false false false false false

canonicalPortoRealizedControlReceipt : GenericReceipt.GenericReceipt
canonicalPortoRealizedControlReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Porto Alegre current realised-control comparator evidence"
    "DASHI.Governance.BoloBoloPortoAlegreRealizedControlExact"
    "canonicalPortoRealizedControlEvidence / canonicalPortoRealizedControlBoundary"
    "retains official 2025/2026 event observations of COP proposal/vote flow, rotating councillor questions and government responses, community speech slots, delegate/councillor election, representative-to-government needs/criticism/suggestion flow and titular/suplente representation"
    "official municipal process reporting is not an independent non-domination audit; unanimity among those present does not pay full attendance; turn-taking/elections/speech slots do not establish equal influence, effective recall or causal effect; comparator evidence does not become target-bolo evidence"
    "agda -i . DASHI/Governance/BoloBoloPortoAlegreRealizedControlRegression.agda"
