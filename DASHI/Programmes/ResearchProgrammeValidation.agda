module DASHI.Programmes.ResearchProgrammeValidation where

open import DASHI.Core.Prelude
open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Programmes.CFDExact
open import DASHI.Programmes.BrainExact
open import DASHI.Programmes.QuantumExact
open import DASHI.Programmes.DashifineExact
open import DASHI.Programmes.GrokkingExact
open import DASHI.Programmes.CoreReferenceExact
open import DASHI.Programmes.FRACDASHExact
open import DASHI.Programmes.TestHarnessExact
open import DASHI.Programmes.RTXExact

-- Each listed satellite is forced through the same owner + evidence-receipt
-- completeness cutset.  Adding a tenth programme without a corresponding
-- adapter leaves this validation surface intentionally incomplete until it is
-- wired here.

cfdOwner : ownerAssigned dashiCFDProgramme ≡ true
cfdOwner = allRegisteredProgrammesHaveFormalOwner dashiCFDProgramme

brainOwner : ownerAssigned dashiBRAINProgramme ≡ true
brainOwner = allRegisteredProgrammesHaveFormalOwner dashiBRAINProgramme

quantumOwner : ownerAssigned dashiQProgramme ≡ true
quantumOwner = allRegisteredProgrammesHaveFormalOwner dashiQProgramme

dashifineOwner : ownerAssigned dashifineProgramme ≡ true
dashifineOwner = allRegisteredProgrammesHaveFormalOwner dashifineProgramme

grokkingOwner : ownerAssigned DASHIgProgramme ≡ true
grokkingOwner = allRegisteredProgrammesHaveFormalOwner DASHIgProgramme

coreOwner : ownerAssigned dashiCOREProgramme ≡ true
coreOwner = allRegisteredProgrammesHaveFormalOwner dashiCOREProgramme

fracdashOwner : ownerAssigned FRACDASHProgramme ≡ true
fracdashOwner = allRegisteredProgrammesHaveFormalOwner FRACDASHProgramme

testHarnessOwner : ownerAssigned dashitestProgramme ≡ true
testHarnessOwner = allRegisteredProgrammesHaveFormalOwner dashitestProgramme

rtxOwner : ownerAssigned dashiRTXProgramme ≡ true
rtxOwner = allRegisteredProgrammesHaveFormalOwner dashiRTXProgramme

cfdReceipt : promotionReceiptRequired dashiCFDProgramme ≡ true
cfdReceipt = allRegisteredProgrammesUseReceiptGate dashiCFDProgramme

brainReceipt : promotionReceiptRequired dashiBRAINProgramme ≡ true
brainReceipt = allRegisteredProgrammesUseReceiptGate dashiBRAINProgramme

quantumReceipt : promotionReceiptRequired dashiQProgramme ≡ true
quantumReceipt = allRegisteredProgrammesUseReceiptGate dashiQProgramme

dashifineReceipt : promotionReceiptRequired dashifineProgramme ≡ true
dashifineReceipt = allRegisteredProgrammesUseReceiptGate dashifineProgramme

grokkingReceipt : promotionReceiptRequired DASHIgProgramme ≡ true
grokkingReceipt = allRegisteredProgrammesUseReceiptGate DASHIgProgramme

coreReceipt : promotionReceiptRequired dashiCOREProgramme ≡ true
coreReceipt = allRegisteredProgrammesUseReceiptGate dashiCOREProgramme

fracdashReceipt : promotionReceiptRequired FRACDASHProgramme ≡ true
fracdashReceipt = allRegisteredProgrammesUseReceiptGate FRACDASHProgramme

testHarnessReceipt : promotionReceiptRequired dashitestProgramme ≡ true
testHarnessReceipt = allRegisteredProgrammesUseReceiptGate dashitestProgramme

rtxReceipt : promotionReceiptRequired dashiRTXProgramme ≡ true
rtxReceipt = allRegisteredProgrammesUseReceiptGate dashiRTXProgramme
