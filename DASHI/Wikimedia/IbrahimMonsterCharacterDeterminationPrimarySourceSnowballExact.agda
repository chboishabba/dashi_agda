module DASHI.Wikimedia.IbrahimMonsterCharacterDeterminationPrimarySourceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannUniquenessBidiExact as Uniqueness
import DASHI.Moonshine.Base369MonsterSemanticRepresentationBidiFrontierExact as Semantic

------------------------------------------------------------------------
-- CHARACTER-DETERMINATION SOURCE PAYMENT
--
-- The live uniqueness owner has already reduced the remaining generic theorem
-- to the standard characteristic-zero statement that finite-dimensional
-- representations with equal characters are isomorphic.  We do NOT postulate
-- an inhabitant here.  This owner records the primary mathematical source,
-- external concept identities, and exact local theorem-interface alignment.
------------------------------------------------------------------------

serreCharacterSource : Attribution.AttributedSource
serreCharacterSource = Attribution.mkDOISource
  "Jean-Pierre Serre"
  "Linear Representations of Finite Groups"
  "Graduate Texts in Mathematics 42, Springer"
  "1977"
  "10.1007/978-1-4684-9458-7"
  "https://doi.org/10.1007/978-1-4684-9458-7"
  Attribution.academicBookSource
  "character-theory source for the theorem that finite-dimensional representations are determined up to isomorphism by their characters; source attribution does not itself inhabit the local representation interface"
  Attribution.publicAttribution

serreSourceSnowball : Snowball.SourceRoleSnowballReceipt serreCharacterSource
serreSourceSnowball = Snowball.canonicalSourceRoleSnowballReceipt serreCharacterSource

------------------------------------------------------------------------
-- QID / Ibrahim coordinates.
------------------------------------------------------------------------

record CharacterTheoryExternalCoordinates : Set where
  constructor character-theory-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupRepresentationArticleRole : String
    sourceDOI : String
    qidCreatesTheoremWitness : Bool
    sourceCitationCreatesTheoremWitness : Bool
open CharacterTheoryExternalCoordinates public

canonicalCharacterTheoryExternalCoordinates : CharacterTheoryExternalCoordinates
canonicalCharacterTheoryExternalCoordinates =
  character-theory-external-coordinates
    "Q1055807"
    "Q600043"
    "secondary navigation / terminology coordinate only"
    "10.1007/978-1-4684-9458-7"
    false false

------------------------------------------------------------------------
-- Exact local alignment.
------------------------------------------------------------------------

localCharacterDeterminationInterface : Set₂
localCharacterDeterminationInterface = Uniqueness.IrreducibleCharacterDetermination

record CharacterDeterminationAlignment : Set where
  constructor character-determination-alignment
  field
    fixedPhaseSignatureUniquenessAlreadyPaid : Bool
    witnessedModelIrreducibilityAlreadyPaid : Bool
    scalarCommutantCrossCheckAlreadyAvailable : Bool
    localInterfaceMatchesCharacterDeterminationShape : Bool
    sourceEstablishesStandardMathematics : Bool
    actualLocalInstanceImportedHere : Bool
    kernelCertifiedHere : Bool
open CharacterDeterminationAlignment public

canonicalCharacterDeterminationAlignment : CharacterDeterminationAlignment
canonicalCharacterDeterminationAlignment =
  character-determination-alignment
    true true true true true false false

------------------------------------------------------------------------
-- Existing frontier remains authoritative.
------------------------------------------------------------------------

uniquenessBoundary : Uniqueness.StoneVonNeumannUniquenessBidiBoundary
uniquenessBoundary = Uniqueness.canonicalStoneVonNeumannUniquenessBidiBoundary

semanticBoundary : Semantic.SemanticRepresentationBidiBoundary
semanticBoundary = Semantic.canonicalSemanticRepresentationBidiBoundary

record CharacterDeterminationSnowballFrontier : Set where
  constructor character-determination-snowball-frontier
  field
    primarySourceIdentityPaid : Bool
    doiPaid : Bool
    groupRepresentationQidPaid : Bool
    characterQidPaid : Bool
    localStatementShapeAligned : Bool
    theoremReprovedLocally : Bool
    theoremInstanceConnectedToActual3BRepresentationLayer : Bool
    actualZetaRecognitionUnlocked : Bool
    nextResidual : String
open CharacterDeterminationSnowballFrontier public

currentCharacterDeterminationSnowballFrontier : CharacterDeterminationSnowballFrontier
currentCharacterDeterminationSnowballFrontier = character-determination-snowball-frontier
  true true true true true false false false
  "instantiate the existing IrreducibleCharacterDetermination interface in the actual finite complex representation layer (or import an already-certified equivalent theorem), then attach the actual restricted zeta and inverse-zeta irreducibles to the unique fixed-phase signatures; do not use QIDs/OEIS/numeric equality as representation authority"
