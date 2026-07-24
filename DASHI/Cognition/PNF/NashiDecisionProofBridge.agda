module DASHI.Cognition.PNF.NashiDecisionProofBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.OperationalIR as IR
import DASHI.Interop.PNFTechSystemicStressBridge as Existing

record TextMarketJoinReceipt : Set where
  constructor textMarketJoinReceipt
  field
    sourcePNF : PNF.EventPNF
    sourceBinding eventTimeAlignment revisionCompleteness : Bool
    entityResolution noLookahead mechanismLink regimeCompatibility : Bool
    sourceBindingIsTrue : sourceBinding ≡ true
    eventTimeAlignmentIsTrue : eventTimeAlignment ≡ true
    revisionCompletenessIsTrue : revisionCompleteness ≡ true
    entityResolutionIsTrue : entityResolution ≡ true
    noLookaheadIsTrue : noLookahead ≡ true
    mechanismLinkIsTrue : mechanismLink ≡ true
    regimeCompatibilityIsTrue : regimeCompatibility ≡ true
    joinReceiptId : String

open TextMarketJoinReceipt public

record NashiDecisionProof : Set where
  constructor nashiDecisionProof
  field
    marketObservationPNF textEventPNF : PNF.EventPNF
    memoryFibre : Memory.MemoryFibre
    operationalIR : IR.DomainIR
    supportReasonChain structuralReasonChain candidateReasonChain : String
    selectedActionOrRefusal : String
    textMarketJoin : TextMarketJoinReceipt
    textualEvidenceAlonePromotesMechanism : Bool
    textualEvidenceAlonePromotesMechanismIsFalse :
      textualEvidenceAlonePromotesMechanism ≡ false
    decisionProofId : String

open NashiDecisionProof public

record ExistingSystemicStressAdapter : Set where
  constructor existingSystemicStressAdapter
  field
    existingPNFEvidenceReceipt : Existing.PNFScenarioEvidenceReceipt
    joinedDecisionProof : NashiDecisionProof
    sourceResidualAndMarketResidualIdentified : Bool
    sourceResidualAndMarketResidualIdentifiedIsFalse :
      sourceResidualAndMarketResidualIdentified ≡ false

open ExistingSystemicStressAdapter public
