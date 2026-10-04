module DASHI.Economics.AIGlobalPoliticalEconomySourceAtlas2026Exact where

open import DASHI.Core.Prelude

import DASHI.Economics.SourceAttributionPromotionBoundaryExact as Attribution

------------------------------------------------------------------------
-- SOURCE ATLAS FOR THE 2026 AI / FUNDING / REGULATION TRANCHE
--
-- Every row is a bounded external proposition.  None of these rows owns the
-- downstream DASHI game-theory, causal or systemic synthesis.
------------------------------------------------------------------------

spaceXIPO : Attribution.SourceAttributionReceipt
spaceXIPO = Attribution.sourceAttributionReceipt
  "Space Exploration Technologies Corp."
  "SpaceX issuer disclosure"
  "SpaceX investor-relations IPO closing release"
  "SpaceX investor relations, 2026-06-15"
  "SpaceX investor-relations carrier"
  Attribution.canonicalCarrier
  "IPO closing and gross-proceeds statement"
  "SpaceX stated that its June 2026 IPO closed after full exercise of the underwriters' option and reported approximately USD 85.7 billion of gross proceeds."
  Attribution.primarySourceProposition
  "DASHI.Economics.AIGlobalPoliticalEconomySourceAtlas2026Exact"
  "transaction proposition only; no authority to infer that all private technology valuations will clear public markets"
  true true true

openAIIPODelay : Attribution.SourceAttributionReceipt
openAIIPODelay = Attribution.sourceAttributionReceipt
  "Reuters; statement attributed to Sam Altman"
  "Sam Altman / Reuters reporting"
  "Reuters news report dated 2026-09-12"
  "Reuters report on OpenAI IPO timing and safety rationale"
  "Reuters access carrier"
  Attribution.secondaryReportingCarrier
  "bounded 2026 IPO-timing statement"
  "Reuters reported that OpenAI would not complete an IPO in 2026 and attributed the decision to heightened AI-safety concerns."
  Attribution.secondarySourceReport
  "DASHI.Economics.AIGlobalPoliticalEconomySourceAtlas2026Exact"
  "secondary reporting authority only; does not establish motive beyond the attributed public rationale"
  false true true

anthropicIPOPressure : Attribution.SourceAttributionReceipt
anthropicIPOPressure = Attribution.sourceAttributionReceipt
  "Reuters"
  "Reuters reporting"
  "Reuters report dated 2026-09-19"
  "Reuters report on Anthropic model-release and IPO timing pressure"
  "Reuters access carrier"
  Attribution.secondaryReportingCarrier
  "bounded competitive/IPO timing proposition"
  "Reuters reported that Anthropic was weighing another model release ahead of an anticipated IPO while balancing competitive, safety and investor pressures."
  Attribution.secondarySourceReport
  "DASHI.Economics.AIGlobalPoliticalEconomySourceAtlas2026Exact"
  "secondary report only; no authority to infer strategic deception or fabricated safety concerns"
  false true true

sbEnergyFundingCanary : Attribution.SourceAttributionReceipt
sbEnergyFundingCanary = Attribution.sourceAttributionReceipt
  "Financial Times"
  "Financial Times reporting"
  "Financial Times report published 2026-09"
  "FT report on SoftBank-backed SB Energy IPO and debt financing"
  "FT access carrier"
  Attribution.secondaryReportingCarrier
  "IPO slowing, debt-yield and capital-requirement propositions"
  "FT reported that SB Energy slowed its IPO amid investor concern, faced approximately 10 percent expected yields on a planned debt raise, and disclosed very large future capital requirements."
  Attribution.secondarySourceReport
  "DASHI.Economics.AIEnergyInfrastructureFundingStress2026Exact"
  "funding-stress canary only; no authority to infer inevitable default, bubble burst or systemic crisis"
  false true true

burryFinancingCritique : Attribution.SourceAttributionReceipt
burryFinancingCritique = Attribution.sourceAttributionReceipt
  "Michael J. Burry"
  "Michael J. Burry"
  "Burry's 2026 Trading Post/Substack posts"
  "Michael J. Burry, Trading Post, 2026"
  "author-controlled publication carrier"
  Attribution.primaryCarrierMirror
  "AI-capex, circular-financing, depreciation and terminal-return critique"
  "Burry argued that AI infrastructure spending exhibits reflexive/circular financing, aggressive useful-life assumptions and inadequate demonstrated returns relative to capital committed."
  Attribution.primarySourceProposition
  "DASHI.Economics.AIGlobalPoliticalEconomySourceAtlas2026Exact"
  "argument attribution only; DASHI does not promote the analogy to a proved subprime-equivalence theorem"
  true true true

coefficientGivingSafetyField : Attribution.SourceAttributionReceipt
coefficientGivingSafetyField = Attribution.sourceAttributionReceipt
  "Coefficient Giving / former Open Philanthropy"
  "Coefficient Giving"
  "Coefficient Giving research and grants pages"
  "Coefficient Giving AI safety/governance programme materials"
  "organisation-controlled publication carrier"
  Attribution.canonicalCarrier
  "field-building and grant-programme proposition"
  "Coefficient Giving states that it helped build the AI-safety field and funds catastrophic-risk research, evaluations, governance, compute-policy, audit and related institution-building work."
  Attribution.primarySourceProposition
  "DASHI.Economics.AISafetyRegulatoryMoatGameExact"
  "funding/provenance proposition only; no authority to infer fabrication, collusion or anti-open-source intent"
  true true true

aiRegulatoryCaptureDebate : Attribution.SourceAttributionReceipt
aiRegulatoryCaptureDebate = Attribution.sourceAttributionReceipt
  "Reuters and independent legal/economic commentary"
  "identified commentators and interested industry actors"
  "2026 reporting and regulatory-capture analysis"
  "Reuters / legal-policy commentary, 2026"
  "secondary reporting carriers"
  Attribution.secondaryReportingCarrier
  "existence of regulatory-capture/compliance-moat critique"
  "Public 2026 analysis explicitly argues that frontier-AI safety regulation can create asymmetric compliance moats and may benefit incumbent labs relative to open-weight, academic and smaller developers."
  Attribution.secondarySourceReport
  "DASHI.Economics.AISafetyRegulatoryMoatGameExact"
  "debate-existence and mechanism proposition only; no authority to infer that any named safety claim is false"
  false true true

australianAgentIncident : Attribution.SourceAttributionReceipt
australianAgentIncident = Attribution.sourceAttributionReceipt
  "Australian Government / OpenAI, as separate source owners"
  "Australian Government and OpenAI"
  "official government review/public statements and OpenAI incident reporting"
  "2026 Australian AI-driven cyber-incident public materials"
  "official/public carriers"
  Attribution.canonicalCarrier
  "unauthorised-access and review proposition"
  "Australian authorities described an AI-driven access event as unauthorised and opened review/legal analysis; this does not itself resolve jurisdiction-specific criminal liability or assign human mens rea."
  Attribution.primarySourceProposition
  "DASHI.Economics.AgentAccessBoundaryLegalMechanismExact"
  "incident/access proposition only; offence classification and mental-state attribution remain separate"
  true true true

openWeightCompetition : Attribution.SourceAttributionReceipt
openWeightCompetition = Attribution.sourceAttributionReceipt
  "Reuters / open-model ecosystem reporting"
  "multiple open-model developers and market observers"
  "2026 reporting on low-cost and open-weight model competition"
  "2026 public reporting"
  "secondary reporting carriers"
  Attribution.secondaryReportingCarrier
  "open-model substitutability pressure proposition"
  "Current reporting identifies lower-cost and open-weight models as competitive pressure on proprietary frontier-model economics."
  Attribution.secondarySourceReport
  "DASHI.Economics.AIUbiquityRentInversionExact"
  "competitive-pressure proposition only; no authority to infer zero cloud value or guaranteed frontier-lab failure"
  false true true

sourceBundleDoesNotCreateSystemicClassification :
  Attribution.SourcePropositionImpliesSystemicClassificationPermission → ⊥
sourceBundleDoesNotCreateSystemicClassification =
  Attribution.sourcePropositionDoesNotAutoPromoteToSystemicClassification
