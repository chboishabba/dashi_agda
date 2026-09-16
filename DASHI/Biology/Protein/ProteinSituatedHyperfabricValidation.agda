module DASHI.Biology.Protein.ProteinSituatedHyperfabricValidation where

open import DASHI.Core.Prelude

import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact as Protein
import DASHI.Biology.Protein.TRPA1SituatedProteinWitnessExact as TRPA1
import DASHI.Biology.Protein.AdenylateKinaseSituatedProteinWitnessExact as AdK

------------------------------------------------------------------------
-- RED-first contract for the approved situated-protein design.
------------------------------------------------------------------------

genericBoundary = Protein.canonicalProteinSituatedHyperfabricBoundary
trpa1Witness = TRPA1.trpa1SituatedQueryWitness
adkWitness = AdK.adkSituatedQueryWitness

queryRelativeProjectionPaid : Bool
queryRelativeProjectionPaid = Protein.ProteinSituatedHyperfabricBoundary.queryRelativeProjectionRequired genericBoundary

proteinIdentityNotCompleteState : Bool
proteinIdentityNotCompleteState = Protein.ProteinSituatedHyperfabricBoundary.proteinIdentityIsCompletePredictiveState genericBoundary

citationNotAuthority : Bool
citationNotAuthority = Protein.ProteinSituatedHyperfabricBoundary.externalIdentityCreatesBiologicalAuthority genericBoundary

trpa1UsesGenericInterface : Bool
trpa1UsesGenericInterface = TRPA1.TRPA1SituatedBoundary.usesGenericSituatedWitness TRPA1.canonicalTRPA1SituatedBoundary

adkUsesGenericInterface : Bool
adkUsesGenericInterface = AdK.AdKSituatedBoundary.usesGenericSituatedWitness AdK.canonicalAdKSituatedBoundary

crossDomainMechanismTransferBlocked : Bool
crossDomainMechanismTransferBlocked = Protein.ProteinSituatedHyperfabricBoundary.crossDomainWitnessTransfersMechanism genericBoundary
