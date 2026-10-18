module DASHI.Governance.IranianDialecticalTransportPhilosophyCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.ContextualDialecticRoleExact as Role
import DASHI.Core.DialecticalMaterialRevisionExact as Revision
import DASHI.Culture.HistoricalSocialTotalityBidiExact as Totality
import DASHI.Philosophy.ProcessHistoryEquivalence as Process
import DASHI.Philosophy.RetroactiveMeaning as Retro
import DASHI.Philosophy.InterpretationStrata as Strata
import DASHI.Philosophy.PolyphonicRelation as Polyphony
import DASHI.Philosophy.PowerAndGrammar as Power
import DASHI.Governance.IranMarxianIslamicTranslationExact as Iran
import DASHI.Governance.IranianRevolutionaryIntellectualGenealogyExact as Genealogy

------------------------------------------------------------------------
-- PHILOSOPHY CROSS-POLLINATION
--
-- A relational contradiction may be historically transported and revised
-- across ontologies.  What persists is a typed relation/process, not an
-- immutable word, essence or political authority.
------------------------------------------------------------------------

data RevolutionaryGrammarState : Set where
  marxianClassGrammar : RevolutionaryGrammarState
  shariatiIslamicRevolutionaryGrammar : RevolutionaryGrammarState
  khomeinistIslamicRevolutionaryGrammar : RevolutionaryGrammarState

data AntagonismSurface : Set where
  oppressedOppressorConflict : AntagonismSurface

data OntologyOutcome : Set where
  historicalMaterialClassOntology : OntologyOutcome
  islamicHumanistRevolutionaryOntology : OntologyOutcome
  juristLedIslamicStateOntology : OntologyOutcome

antagonismObserver : RevolutionaryGrammarState → AntagonismSurface
antagonismObserver _ = oppressedOppressorConflict

ontologyOutcome : RevolutionaryGrammarState → OntologyOutcome
ontologyOutcome marxianClassGrammar = historicalMaterialClassOntology
ontologyOutcome shariatiIslamicRevolutionaryGrammar = islamicHumanistRevolutionaryOntology
ontologyOutcome khomeinistIslamicRevolutionaryGrammar = juristLedIslamicStateOntology

data SameAntagonismMeansSameOntology : Set where
sameAntagonismDoesNotMeanSameOntology : SameAntagonismMeansSameOntology → ⊥
sameAntagonismDoesNotMeanSameOntology ()

record MediatedDialecticalTransport : Set where
  constructor mediated-dialectical-transport
  field
    sourceTranslation : Iran.StructuralTranslation
    genealogyEdges : List Genealogy.GenealogyEdge
    sourceTotalityBoundary : Totality.HistoricalSocialTotalityBoundary
    contextualRoleBoundary : Role.ContextualDialecticRoleBoundary
    retroactiveMeaningBoundary : Retro.RetroactiveMeaningBoundary
    polyphonyBoundary : Polyphony.PolyphonyBoundary
    interpretationBoundary : Strata.StratumBoundary
    relationPersistsAcrossOntologyChange : Bool
    ontologyPreservedLiterally : Bool
    finalSynthesisRequired : Bool
    historicalInfluenceCreatedByFormalSimilarity : Bool
    politicalAuthorityCreatedByTransport : Bool

open MediatedDialecticalTransport public

canonicalMediatedTransport : MediatedDialecticalTransport
canonicalMediatedTransport =
  mediated-dialectical-transport
    Iran.imperialismToEstekbar
    Genealogy.canonicalFieldEdges
    Totality.canonicalHistoricalSocialTotalityBoundary
    Role.canonicalContextualDialecticRoleBoundary
    Retro.canonicalRetroactiveMeaningBoundary
    Polyphony.canonicalPolyphonyBoundary
    Strata.structuralInterpretationBoundary
    true false false false false

transportPreservesRelationWithoutOntologyIdentity :
  relationPersistsAcrossOntologyChange canonicalMediatedTransport ≡ true
  × ontologyPreservedLiterally canonicalMediatedTransport ≡ false
transportPreservesRelationWithoutOntologyIdentity = refl , refl

transportRequiresNoForcedFinalSynthesis :
  finalSynthesisRequired canonicalMediatedTransport ≡ false
transportRequiresNoForcedFinalSynthesis = refl

transportStaysAtStructuralInterpretationStratum :
  Strata.stratum (interpretationBoundary canonicalMediatedTransport)
  ≡ Strata.structuralInterpretation
transportStaysAtStructuralInterpretationStratum = refl

data StructuralTransportProvesHistoricalInfluence : Set where
data HistoricalInfluenceProvesExactOntologyTransfer : Set where
data SimilarEndpointErasesProcessHistory : Set where

structuralTransportDoesNotProveHistoricalInfluence :
  StructuralTransportProvesHistoricalInfluence → ⊥
structuralTransportDoesNotProveHistoricalInfluence ()

historicalInfluenceDoesNotProveExactOntologyTransfer :
  HistoricalInfluenceProvesExactOntologyTransfer → ⊥
historicalInfluenceDoesNotProveExactOntologyTransfer ()

similarEndpointDoesNotEraseProcessHistory :
  SimilarEndpointErasesProcessHistory → ⊥
similarEndpointDoesNotEraseProcessHistory ()

------------------------------------------------------------------------
-- Second-order power seam: political struggle can concern the grammar through
-- which a subject is legible, not just first-order policy outputs.
------------------------------------------------------------------------

data RevolutionaryClaim : Set where
  classClaim religiousClaim nationalLiberationClaim antiImperialistClaim : RevolutionaryClaim

data GrammarCode : Set where
  marxianCode shariatiCode khomeinistCode : GrammarCode

data PolicyCode : Set where
  classSovereigntyPolicy juristSovereigntyPolicy pluralLiberationPolicy : PolicyCode

record GrammarPowerBoundary : Set where
  constructor grammar-power-boundary
  field
    grammarCanChangeWhichClaimsAreLegible : Bool
    changedGrammarImpliesSameAuthority : Bool
    changedVocabularyAloneProvesChangedMaterialPower : Bool

canonicalGrammarPowerBoundary : GrammarPowerBoundary
canonicalGrammarPowerBoundary = grammar-power-boundary true false false
