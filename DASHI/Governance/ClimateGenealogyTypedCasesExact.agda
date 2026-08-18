module DASHI.Governance.ClimateGenealogyTypedCasesExact where

------------------------------------------------------------------------
-- TWO-AXIS CLIMATE / TOBACCO WORKED CASE
--
-- Source rows here mirror the supplied typed-edge research manifest.  Relation
-- kind and evidence quality remain independent.
--
-- Primary / institutional sources represented below:
--
-- Frederick Seitz, interview by FRONTLINE / PBS, "Hot Politics: Interview --
-- Frederick Seitz" (2006).  No DOI asserted.  Bounded role: first-person
-- testimony concerning R.J. Reynolds research funding and Seitz's George C.
-- Marshall Institute chairmanship; memory testimony is not an internal RJR
-- accounting record.
--
-- Brown & Williamson Tobacco Corporation,
-- "Smoking and Health Proposal" (1969), Bates 690010951--690010959,
-- UCSF Industry Documents Library.  No DOI asserted.
--
-- American Petroleum Institute / Global Climate Science Communications Team,
-- "Global Climate Science Communications Action Plan" (1998).
-- Archived primary planning document; no DOI asserted.
--
-- Naomi Oreskes; Erik M. Conway,
-- "Defeating the merchants of doubt", Nature 465:686--687 (2010),
-- DOI 10.1038/465686a.
-- Bounded role: historical corroboration and search map, not a replacement for
-- the primary endpoint documents.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.TypedGenealogyEdgeExact as Typed

seitzPBS : Typed.SourceReceipt
seitzPBS = Typed.sourceReceipt
  "Frederick Seitz; FRONTLINE / PBS"
  "Hot Politics: Interview -- Frederick Seitz"
  "2006"
  "PBS FRONTLINE interview; no DOI asserted"
  "first-person testimony concerning R.J. Reynolds research-funding relationship and George C. Marshall Institute chairmanship"

bw1969 : Typed.SourceReceipt
bw1969 = Typed.sourceReceipt
  "Brown & Williamson Tobacco Corporation"
  "Smoking and Health Proposal"
  "1969"
  "Bates 690010951--690010959; UCSF Industry Documents Library; no DOI asserted"
  "primary tobacco document establishing the stated doubt/controversy communication objective"

api1998 : Typed.SourceReceipt
api1998 = Typed.sourceReceipt
  "American Petroleum Institute / Global Climate Science Communications Team"
  "Global Climate Science Communications Action Plan"
  "1998"
  "archived primary planning document; no DOI asserted"
  "primary climate-communications plan naming the George C. Marshall Institute and stating uncertainty-oriented public-policy objectives"

oreskesConwayNature : Typed.SourceReceipt
oreskesConwayNature = Typed.sourceReceipt
  "Naomi Oreskes; Erik M. Conway"
  "Defeating the merchants of doubt"
  "2010"
  "Nature 465:686--687; DOI 10.1038/465686a"
  "historical corroboration/search map; not by itself a primary transfer document"

------------------------------------------------------------------------
-- E1--E3: composed institutional path.  These edges deliberately assert
-- funding/personnel/organisation relations, not method transfer.
------------------------------------------------------------------------

rjrToSeitz : Typed.TypedGenealogyEdge
rjrToSeitz = Typed.typedGenealogyEdge
  "E1" "R.J. Reynolds Tobacco Co." "Frederick Seitz"
  Typed.funding Typed.corroborated
  (seitzPBS ∷ [])
  "RJR-to-Seitz funding relationship is supported by Seitz's first-person account; direct RJR financial records would strengthen documentary corroboration"

seitzToMarshall : Typed.TypedGenealogyEdge
seitzToMarshall = Typed.typedGenealogyEdge
  "E2" "Frederick Seitz" "George C. Marshall Institute"
  Typed.personnelContinuity Typed.corroborated
  (seitzPBS ∷ [])
  "Seitz identifies himself as chairman emeritus; this is personnel continuity, not proof that a tobacco method was transferred"

marshallInAPIPlan : Typed.TypedGenealogyEdge
marshallInAPIPlan = Typed.typedGenealogyEdge
  "E3" "George C. Marshall Institute" "1998 API climate communications plan"
  Typed.organisationalContinuity Typed.primary
  (api1998 ∷ [])
  "the Marshall Institute is textually present in the primary plan as a participating/potential allocation organization; no inferred method-transfer claim is needed"

------------------------------------------------------------------------
-- E4/E4b: SAME endpoint documents, TWO propositions.
--
-- E4: method recurrence is primary-source strong.
-- E4b: historical transfer remains pending because no intervening transmission
-- witness has been installed.
------------------------------------------------------------------------

bwToAPIRecurrence : Typed.TypedGenealogyEdge
bwToAPIRecurrence = Typed.typedGenealogyEdge
  "E4" "1969 B&W Smoking and Health Proposal" "1998 API climate communications plan"
  Typed.methodRecurrence Typed.primary
  (bw1969 ∷ api1998 ∷ [])
  "two primary documents support a tightly comparable uncertainty/controversy communication pattern; this edge asserts recurrence, not transmission"

bwToAPIHistoricalTransferPending : Typed.TypedGenealogyEdge
bwToAPIHistoricalTransferPending = Typed.typedGenealogyEdge
  "E4b" "1969 B&W Smoking and Health Proposal" "1998 API climate communications plan"
  Typed.historicalTransfer Typed.pendingBridge
  (bw1969 ∷ api1998 ∷ oreskesConwayNature ∷ [])
  "historical-transfer hypothesis remains open pending a personnel, citation, consulting, document-flow, or equivalent transmission bridge"

recurrenceCannotBePromotedByPrimaryQualityAlone :
  Typed.StrongHistoricalTransfer bwToAPIRecurrence → ⊥
recurrenceCannotBePromotedByPrimaryQualityAlone transfer =
  Typed.methodRecurrenceIsNotTransferRelation
    (Typed.relationIsTransfer transfer)

pendingHistoricalTransferIsNotStrongYet :
  Typed.StrongHistoricalTransfer bwToAPIHistoricalTransferPending → ⊥
pendingHistoricalTransferIsNotStrongYet transfer =
  Typed.pendingBridgeIsNotStrong
    (Typed.evidenceIsStrong transfer)

------------------------------------------------------------------------
-- E5--E7: institutional continuity and explicitly unresolved candidates.
------------------------------------------------------------------------

hillKnowltonContinuity : Typed.TypedGenealogyEdge
hillKnowltonContinuity = Typed.typedGenealogyEdge
  "E5" "Hill & Knowlton tobacco-era PR" "Hill+Knowlton fossil-fuel-era client work"
  Typed.organisationalContinuity Typed.corroborated
  []
  "same-firm/institutional-continuity proposition; a source-specific client/lineage receipt should be attached before stronger method claims are made"

hillKnowltonMethodTransferCandidate : Typed.TypedGenealogyEdge
hillKnowltonMethodTransferCandidate = Typed.typedGenealogyEdge
  "E6" "Hill & Knowlton tobacco-era methods" "later climate/fossil-fuel communications"
  Typed.specificMethodTransfer Typed.candidateUnresolved
  []
  "specific method transmission is not installed; seek named personnel, internal memo, consulting record, or equivalent transmission evidence"

singerTobaccoContinuityCandidate : Typed.TypedGenealogyEdge
singerTobaccoContinuityCandidate = Typed.typedGenealogyEdge
  "E7" "S. Fred Singer" "tobacco funding/direction"
  Typed.personnelContinuity Typed.candidateUnresolved
  []
  "repeated secondary assertion is retained as an unresolved search candidate; no primary funding/direction receipt is installed here"

singerCandidateIsNotStrong :
  Typed.StrongEvidence (Typed.evidenceStrength singerTobaccoContinuityCandidate) → ⊥
singerCandidateIsNotStrong = Typed.candidateUnresolvedIsNotStrong

record ClimateTypedCaseBoundary : Set where
  constructor climateTypedCaseBoundary
  field
    composedInstitutionalPathInstalled : Bool
    methodRecurrencePrimary : Bool
    recurrencePromotedToTransfer : Bool
    historicalTransferBridgeInstalled : Bool
    singerPrimaryReceiptInstalled : Bool
    unresolvedSingerTreatedAsRefuted : Bool

canonicalClimateTypedCaseBoundary : ClimateTypedCaseBoundary
canonicalClimateTypedCaseBoundary =
  climateTypedCaseBoundary true true false false false false
