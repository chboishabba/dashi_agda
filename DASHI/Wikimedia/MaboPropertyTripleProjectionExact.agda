module DASHI.Wikimedia.MaboPropertyTripleProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.MaboNativeWikimediaBridgeExact as Mabo
import DASHI.Wikimedia.NativePropertyTripleProjectionExact as Property

------------------------------------------------------------------------
-- MABO P710 REMAINS EXECUTABLE AS A GENERAL PROPERTY TRIPLE
--
-- This is the companion to MaboConcreteQidGraphProjectionExact: P710 is not an
-- Engine.KB ontology edge, but it is an item-valued property statement suitable
-- for the PropertyEngine.PKB-style projection.
------------------------------------------------------------------------

maboParticipantPropertyFact : Property.NativeItemPropertyFact
maboParticipantPropertyFact =
  Property.native-item-property-fact
    Mabo.maboCaseParticipantEddie
    Mabo.participantP
    Mabo.maboNo2
    Mabo.eddieMabo
    refl refl refl
    "Q1501525 P710 Q975866 @ Wikidata oldid 2333409615"

maboParticipantPropertyTriple : Property.PropertyTriple
maboParticipantPropertyTriple = Property.asPropertyTriple maboParticipantPropertyFact

maboParticipantTripleProperty :
  Property.tripleProperty maboParticipantPropertyTriple ≡ "P710"
maboParticipantTripleProperty = refl

maboParticipantTripleSubject :
  Property.tripleSubject maboParticipantPropertyTriple ≡ "Q1501525"
maboParticipantTripleSubject = refl

maboParticipantTripleObject :
  Property.tripleObject maboParticipantPropertyTriple ≡ "Q975866"
maboParticipantTripleObject = refl

-- The same source statement can support a PNF predicate projection and a
-- PropertyEngine-style triple projection, but neither projection becomes the
-- other or exhausts the native statement.
data PropertyTripleIsPNFPredicateAtom : Set where
data PropertyTripleMeansLegalPartyRole : Set where

propertyTripleDoesNotBecomePNFAtom : PropertyTripleIsPNFPredicateAtom → ⊥
propertyTripleDoesNotBecomePNFAtom ()

participantTripleDoesNotByItselfMeanLegalPartyRole : PropertyTripleMeansLegalPartyRole → ⊥
participantTripleDoesNotByItselfMeanLegalPartyRole ()
