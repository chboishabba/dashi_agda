module DASHI.Culture.McCaslandTechnicalProgrammeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.TechnicalDependencyHypergraphExact as Tech

-- McCasland's currently source-backed objects are programme/engineering
-- leadership roles from the official USAF biography.  Until an authored
-- technical paper/patent/report is welded to him, DASHI must not invent
-- equations or scientific authorship from command responsibility.

record McCaslandProgrammeSocket : Set where
  constructor mccasland-programme-socket
  field
    person : Tech.TechnicalNode
    programme : Tech.TechnicalNode
    roleEdge : Tech.TechnicalHyperedge
    reference : String

open McCaslandProgrammeSocket public

mccaslandNode : Tech.TechnicalNode
mccaslandNode = Tech.technical-node Tech.personNode "William N. McCasland"

afrlScienceTechnology : Tech.TechnicalNode
afrlScienceTechnology = Tech.technical-node Tech.programmeNode "Air Force science and technology programme"

mccaslandLeadershipEdge : Tech.TechnicalHyperedge
mccaslandLeadershipEdge = Tech.technical-hyperedge
  (mccaslandNode ∷ afrlScienceTechnology ∷ [])
  Tech.ledOrDirected
  Tech.primaryRoleReceipt
  "U.S. Air Force official biography, Major General William N. McCasland"
  "AFRL command/programme-management role; not authorship of every subordinate scientific result"

record McCaslandBoundary : Set where
  constructor mccasland-boundary
  field
    programmeLeadershipImpliesAuthorshipOfTechnicalResults : Bool
    programmeLeadershipImpliesAuthorshipOfTechnicalResultsIsFalse : programmeLeadershipImpliesAuthorshipOfTechnicalResults ≡ false
    programmeLeadershipImpliesKnowledgeOfEveryTechnicalDetail : Bool
    programmeLeadershipImpliesKnowledgeOfEveryTechnicalDetailIsFalse : programmeLeadershipImpliesKnowledgeOfEveryTechnicalDetail ≡ false
    roleEdgeMayEnterTechnicalDependencyGraph : Bool
    roleEdgeMayEnterTechnicalDependencyGraphIsTrue : roleEdgeMayEnterTechnicalDependencyGraph ≡ true
    authoredMathRequiresSeparateReceipt : Bool
    authoredMathRequiresSeparateReceiptIsTrue : authoredMathRequiresSeparateReceipt ≡ true

canonicalMcCaslandBoundary : McCaslandBoundary
canonicalMcCaslandBoundary = mccasland-boundary false refl false refl true refl true refl
