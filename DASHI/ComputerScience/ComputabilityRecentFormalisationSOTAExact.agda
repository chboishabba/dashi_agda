module DASHI.ComputerScience.ComputabilityRecentFormalisationSOTAExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- RECENT COMPUTABILITY / BUSY-BEAVER FORMALISATION SOTA
------------------------------------------------------------------------

isabelleBusyBeaver2026 : Source.AttributedSource
isabelleBusyBeaver2026 =
  Source.mkNoDOISource
    "Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz"
    "The Busy Beaver Function"
    "Archive of Formal Proofs"
    "2026"
    "https://isa-afp.org/entries/Busy_Beaver.html"
    (Source.namedSourceKind "machine-checked Isabelle/HOL development")
    "formalises the Busy Beaver upper-bound principle, its halting-decider consequence, and concrete AFP universal-Turing-machine instantiations; external machine model is not definitionally DASHI's machine"
    Source.publicAttribution

bb5FormalVerification : Source.AttributedSource
bb5FormalVerification =
  Source.mkDOISource
    "The bbchallenge Collaboration et al."
    "Determination of the fifth Busy Beaver value"
    "arXiv:2509.12337 / formally verified Coq development"
    "2025"
    "10.48550/arXiv.2509.12337"
    "https://arxiv.org/abs/2509.12337"
    Source.academicArticleSource
    "proves S(5)=47,176,870 with Coq-backed exhaustive machine classification; a finite exact value does not itself supply universal Busy Beaver noncomputability"
    Source.publicAttribution

recentComputabilitySOTAAtlas : Source.AttributedSourceAtlas
recentComputabilitySOTAAtlas =
  Source.mkSourceAtlas
    "recent computability and Busy Beaver formalisation SOTA"
    "DASHI.ComputerScience.ComputabilityRecentFormalisationSOTAExact"
    (isabelleBusyBeaver2026 ∷ bb5FormalVerification ∷ [])
    "recent machine-checked finite and universal Busy-Beaver/computability results adjacent to DASHI's bounded-halting and finite-envelope fibres"

------------------------------------------------------------------------
-- FINITE VALUE / UNIVERSAL PRINCIPLE / MODEL ADAPTER ARE DISTINCT.
------------------------------------------------------------------------

data ComputabilitySOTARole : Set where
  finiteExactValueProducer
  universalUpperBoundReductionProducer
  universalMachineProducer : ComputabilitySOTARole

data ComputabilityCoordinate : Set where
  finiteHaltingClassification
  exactBusyBeaverValue
  upperBoundDecidesHalting
  universalHaltingUndecidability
  universalMachineEncoding
  programInputPairEncoding : ComputabilityCoordinate

record ComputabilitySOTAProducerReceipt : Set where
  constructor computabilitySOTAProducerReceipt
  field
    source : Source.AttributedSource
    roles : List ComputabilitySOTARole
    coordinates : List ComputabilityCoordinate
    sameMachineAsDASHI : Bool
    exactMachineAdapterOwned : Bool
    importsLocalProof : Bool

isabelleBusyBeaverProducer : ComputabilitySOTAProducerReceipt
isabelleBusyBeaverProducer =
  computabilitySOTAProducerReceipt
    isabelleBusyBeaver2026
    (universalUpperBoundReductionProducer ∷ universalMachineProducer ∷ [])
    (upperBoundDecidesHalting ∷ universalHaltingUndecidability ∷
     universalMachineEncoding ∷ programInputPairEncoding ∷ [])
    false false false

bb5Producer : ComputabilitySOTAProducerReceipt
bb5Producer =
  computabilitySOTAProducerReceipt
    bb5FormalVerification
    (finiteExactValueProducer ∷ [])
    (finiteHaltingClassification ∷ exactBusyBeaverValue ∷ [])
    false false false

------------------------------------------------------------------------
-- CURRENT CUT
------------------------------------------------------------------------

record RecentComputabilitySOTACut : Set where
  constructor recentComputabilitySOTACut
  field
    finiteFiveStateBusyBeaverMachineChecked : Bool
    universalBusyBeaverUpperBoundReductionMachineChecked : Bool
    universalMachineInstantiationMachineChecked : Bool
    dashIFiniteEnvelopeEqualsBB5 : Bool
    externalUniversalMachineEqualsDASHIMachine : Bool
    shortestUniversalRouteIsAdapterSearch : Bool

canonicalRecentComputabilitySOTACut : RecentComputabilitySOTACut
canonicalRecentComputabilitySOTACut =
  recentComputabilitySOTACut true true true false false true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteBusyBeaverValueImpliesUniversalNoncomputability : Set where
data ExternalUniversalMachineImpliesDASHIUniversality : Set where
data SameHaltingTheoremNameImpliesSameMachineEncoding : Set where

finiteValueDoesNotSupplyUniversalTheorem :
  FiniteBusyBeaverValueImpliesUniversalNoncomputability → ⊥
finiteValueDoesNotSupplyUniversalTheorem ()

externalMachineDoesNotMakeDASHIUniversal :
  ExternalUniversalMachineImpliesDASHIUniversality → ⊥
externalMachineDoesNotMakeDASHIUniversal ()

sameNameDoesNotIdentifyMachineModels :
  SameHaltingTheoremNameImpliesSameMachineEncoding → ⊥
sameNameDoesNotIdentifyMachineModels ()
