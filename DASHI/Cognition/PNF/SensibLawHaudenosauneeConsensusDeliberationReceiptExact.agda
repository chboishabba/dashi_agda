module DASHI.Cognition.PNF.SensibLawHaudenosauneeConsensusDeliberationReceiptExact where

------------------------------------------------------------------------
-- HAUDENOSAUNEE CONSENSUS / DELIBERATION RECEIPT
--
-- Nation-specific empirical fixture. This file must NOT be generalized to all
-- Indigenous, Native American, First Nations, Aboriginal, or Torres Strait
-- Islander legal orders.
--
-- Primary institutional sources / stable identifiers:
--   * Haudenosaunee Confederacy, "Government",
--     https://www.haudenosauneeconfederacy.com/government/
--     Describes the Grand Council sequence: Elder/Younger Brothers deliberate,
--     decisions pass across the fire, Onondaga may object for inconsistency with
--     the Great Law, and ceremonial leaders confirm the reached decision.
--   * Haudenosaunee Development Institute, "Haudenosaunee Development Institute
--     Policy on Consultation and Accommodation" (4 October 2011),
--     https://www.haudenosauneeconfederacy.com/wp-content/uploads/2018/03/HDI-POLICY-Final-HEH-Oct-4-2011.pdf
--     States that consultation has no specific timeframe and that consensus
--     building takes time; government-to-government agreements require adoption
--     by the Council of Chiefs.
--   * Onondaga Nation, "Government",
--     https://www.onondaganation.org/government/
--     Describes disagreement returning for further discussion until the council
--     is of one mind / reaches consensus.
--   * Onondaga Nation, Sid Hill declaration concerning Onondaga government,
--     https://www.onondaganation.org/mediafiles/pdfs/lgl_alrtssiddecl.pdf
--     Paras 8-9 describe consensus at successive stages and state that Council
--     of Chiefs decisions are by consensus and that the process is deliberate
--     and essential to Haudenosaunee law.
--
-- No DOI is asserted for these institutional/legal sources. URLs and the named
-- institutional documents are the recoverable stable identifiers available.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawReopenableRelationalAuthorityExact as Rel

haudenosauneeGovernmentSource : Edge.SourceIdentity
haudenosauneeGovernmentSource = Edge.source-identity
  "Haudenosaunee Confederacy"
  "Government"
  "https://www.haudenosauneeconfederacy.com/government/"
  Edge.empiricalSource

hdiConsultationSource : Edge.SourceIdentity
hdiConsultationSource = Edge.source-identity
  "Haudenosaunee Development Institute"
  "Haudenosaunee Development Institute Policy on Consultation and Accommodation"
  "2011-10-04; https://www.haudenosauneeconfederacy.com/wp-content/uploads/2018/03/HDI-POLICY-Final-HEH-Oct-4-2011.pdf"
  Edge.empiricalSource

onondagaGovernmentSource : Edge.SourceIdentity
onondagaGovernmentSource = Edge.source-identity
  "Onondaga Nation"
  "Government"
  "https://www.onondaganation.org/government/"
  Edge.empiricalSource

haudenosauneeCouncilReceipt : Rel.NationSpecificDeliberationReceipt
haudenosauneeCouncilReceipt = Rel.nation-specific-deliberation-receipt
  "Haudenosaunee Confederacy Grand Council"
  "sequential nation/clan deliberation across the council fire with reconsideration when agreement is absent"
  "consensus / being of one mind, with further deliberation when the decision is not agreed"
  "Haudenosaunee Confederacy; Onondaga Nation"
  "Government"
  "https://www.haudenosauneeconfederacy.com/government/ ; https://www.onondaganation.org/government/"
  true
  false refl

hdiTimeReceipt : Rel.NationSpecificDeliberationReceipt
hdiTimeReceipt = Rel.nation-specific-deliberation-receipt
  "Haudenosaunee Confederacy consultation process"
  "consultation duration varies with the discussion and cultural/spiritual obligations; consensus building is expressly described as taking time"
  "Council of Chiefs adoption closes a government-to-government agreement"
  "Haudenosaunee Development Institute"
  "Haudenosaunee Development Institute Policy on Consultation and Accommodation"
  "2011-10-04; https://www.haudenosauneeconfederacy.com/wp-content/uploads/2018/03/HDI-POLICY-Final-HEH-Oct-4-2011.pdf"
  true
  false refl

haudenosauneeProcedure : Rel.DecisionProcedure
haudenosauneeProcedure = Rel.decision-procedure
  "haudenosaunee-grand-council-consensus"
  Rel.consensusSeeking
  Rel.consensusClosure
  true
  true
  true
  haudenosauneeGovernmentSource
  true

------------------------------------------------------------------------
-- Concrete source-backed x-pollination into the generic reopenable kernel.
------------------------------------------------------------------------

haudenosauneeIsEmpiricalInstantiation :
  Rel.empiricalInstantiation haudenosauneeProcedure ≡ true
haudenosauneeIsEmpiricalInstantiation = refl

haudenosauneeUsesConsensusClosure :
  Rel.closure haudenosauneeProcedure ≡ Rel.consensusClosure
haudenosauneeUsesConsensusClosure = refl

haudenosauneeReceiptDoesNotGeneralizePanIndigenous :
  Rel.generalizedToAllIndigenousPeoples haudenosauneeCouncilReceipt ≡ false
haudenosauneeReceiptDoesNotGeneralizePanIndigenous = refl

------------------------------------------------------------------------
-- The source supports extended/reiterated deliberation and lack of a fixed
-- consultation timeframe. It does NOT support a universal numeric claim such as
-- "elders always deliberate for N days". Duration remains source- and matter-
-- specific rather than fabricated as a constant.
------------------------------------------------------------------------

data SourceSaysEveryImportantMatterTakesFixedNumberOfDays : Set where

noFixedDurationGeneralization : SourceSaysEveryImportantMatterTakesFixedNumberOfDays → ⊥
noFixedDurationGeneralization ()
