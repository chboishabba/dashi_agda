module DASHI.Wikimedia.MaboConcreteQidGraphProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Ontology.LeanWikidataExistingContentAudit as Audit
import DASHI.Wikimedia.MaboNativeWikimediaBridgeExact as Mabo
import DASHI.Wikimedia.NativeConcreteQidGraphProjectionExact as Projection

------------------------------------------------------------------------
-- MABO NATIVE FIXTURE -> CONCRETE ONTOLOGY-KERNEL CANDIDATE
--
-- Only the native P31 edges are eligible for the current Aristotle Engine.KB
-- projection.  P710 participant remains in the native/PNF statement layer.
------------------------------------------------------------------------

eddieP31KernelFact : Projection.NativeKernelFact
eddieP31KernelFact =
  Projection.native-kernel-fact
    Projection.instanceRelation
    Mabo.eddieInstanceHuman
    Mabo.eddieMabo
    Mabo.human
    refl refl refl
    "Q975866 P31 Q5 @ Wikidata oldid 2524901559"

maboCaseP31KernelFact : Projection.NativeKernelFact
maboCaseP31KernelFact =
  Projection.native-kernel-fact
    Projection.instanceRelation
    Mabo.maboCaseInstanceLegalCase
    Mabo.maboNo2
    Mabo.legalCase
    refl refl refl
    "Q1501525 P31 Q2334719 @ Wikidata oldid 2333409615"

maboKernelCandidate : Projection.NativeConcreteGraphCandidate
maboKernelCandidate =
  Projection.native-concrete-graph-candidate
    "DASHI.Wikimedia.Mabo.kernel-projection.v0"
    (Mabo.eddieMabo ∷ Mabo.human ∷ Mabo.maboNo2 ∷ Mabo.legalCase ∷ [])
    (eddieP31KernelFact ∷ maboCaseP31KernelFact ∷ [])
    []
    ("Wikidata Q975866 oldid 2524901559" ∷
     "Wikidata Q1501525 oldid 2333409615" ∷
     "Wikipedia Eddie Mabo oldid 1373107539" ∷ [])
    "lossy P31/P279/disjoint projection from the first native Mabo Wikimedia fixture"

maboP31ReferencesExact :
  Projection.instanceFactReferences (Projection.kernelFacts maboKernelCandidate)
  ≡ ("Q975866 P31 Q5 @ Wikidata oldid 2524901559" ∷
     "Q1501525 P31 Q2334719 @ Wikidata oldid 2333409615" ∷ [])
maboP31ReferencesExact = refl

maboP279ReferencesEmpty :
  Projection.subclassFactReferences (Projection.kernelFacts maboKernelCandidate) ≡ []
maboP279ReferencesEmpty = refl

maboDisjointReferencesEmpty :
  Projection.disjointFactReferences (Projection.disjointFacts maboKernelCandidate) ≡ []
maboDisjointReferencesEmpty = refl

maboAdapterAfterVerifiedHash :
  Projection.ContentAddressReceipt maboKernelCandidate →
  Audit.ConcreteQidGraphAdapter
maboAdapterAfterVerifiedHash =
  Projection.asConcreteQidGraphAdapter maboKernelCandidate

-- The first fixture intentionally has revision pins but no exact serialization
-- hash.  There is therefore no closed ContentAddressReceipt in this module.
data MaboKernelCandidateAlreadyContentAddressed : Set where
data MaboParticipantWasProjectedAsOntologyEdge : Set where

maboCandidateNotYetContentAddressed : MaboKernelCandidateAlreadyContentAddressed → ⊥
maboCandidateNotYetContentAddressed ()

p710WasNotProjectedIntoKernel : MaboParticipantWasProjectedAsOntologyEdge → ⊥
p710WasNotProjectedIntoKernel ()
