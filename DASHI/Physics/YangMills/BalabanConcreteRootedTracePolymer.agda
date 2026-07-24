module DASHI.Physics.YangMills.BalabanConcreteRootedTracePolymer where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (_∈_)
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact

------------------------------------------------------------------------
-- Concrete overcounting carrier for rooted connected polymers.
--
-- A rooted traversal is represented literally by its signed-direction word.
-- The carrier is intentionally an overcount: distinct words may visit the same
-- physical block set.  Therefore an injective canonical traversal of physical
-- polymers into this carrier suffices for entropy bounds, while no quotient or
-- undecidable graph isomorphism is required.
------------------------------------------------------------------------

RootedTracePolymer : Set
RootedTracePolymer = List SignedAxis4

tracePolymerSize : RootedTracePolymer → Nat
tracePolymerSize = length

tracePolymerDiameterMajorant : RootedTracePolymer → Nat
tracePolymerDiameterMajorant = length

tracePolymerAnisotropicNorm : RootedTracePolymer → Nat
tracePolymerAnisotropicNorm = length

tracePolymerDiameterBelowAnisotropic : ∀ polymer →
  tracePolymerDiameterMajorant polymer
  ≡ tracePolymerAnisotropicNorm polymer
tracePolymerDiameterBelowAnisotropic polymer = refl

rootedTracePolymerEncoding :
  PhysicalPolymerTraceEncoding RootedTracePolymer
rootedTracePolymerEncoding = record
  { polymerSize = tracePolymerSize
  ; canonicalTraceWord = λ polymer → polymer
  ; canonicalTraceLength = λ polymer → refl
  ; traceEncodingInjective = λ equality → equality
  }

tracePolymersOfSize : Nat → List RootedTracePolymer
tracePolymersOfSize = allSignedWords

tracePolymersOfSizeComplete : ∀ polymer →
  polymer ∈ tracePolymersOfSize (tracePolymerSize polymer)
tracePolymersOfSizeComplete polymer =
  canonicalPolymerTraceEnumerated rootedTracePolymerEncoding polymer

tracePolymersOfSizeCount : ∀ size →
  length (tracePolymersOfSize size) ≡ pow8 size
tracePolymersOfSizeCount = allSignedWordsLength

record TransferCutCrossingWitness (polymer : RootedTracePolymer) : Set where
  field
    requiredTraversalLength : Nat
    crossingNeedsLength :
      requiredTraversalLength ≡ tracePolymerAnisotropicNorm polymer

open TransferCutCrossingWitness public

crossingTraceHasRequiredAnisotropicLength :
  ∀ {polymer} → TransferCutCrossingWitness polymer →
  requiredTraversalLength ≡ tracePolymerAnisotropicNorm polymer
crossingTraceHasRequiredAnisotropicLength = crossingNeedsLength

rootedTracePolymerCarrierLevel : ProofLevel
rootedTracePolymerCarrierLevel = machineChecked

rootedTracePolymerEntropyLevel : ProofLevel
rootedTracePolymerEntropyLevel = machineChecked

rootedTraceAnisotropicDiameterLevel : ProofLevel
rootedTraceAnisotropicDiameterLevel = machineChecked

physicalConnectedPolymerCanonicalTraceLevel : ProofLevel
physicalConnectedPolymerCanonicalTraceLevel = conditional

physicalTransferCutTraceLengthLevel : ProofLevel
physicalTransferCutTraceLengthLevel = conditional
