module DASHI.Wikimedia.IbrahimMonster3BPhaseOrientationGaugeSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BDiagonalC3QuotientOrientationSnowballExact as Diagonal
import DASHI.Wikimedia.IbrahimMonster3BSuzukiMainQuotientSameObjectSnowballExact as PairMatch

------------------------------------------------------------------------
-- PHASE-ORIENTATION GAUGE / COORDINATE CHOICE
--
-- The actual extraspecial centre has two nonidentity generators z and z^-1.
-- Unless an external convention selects one of them, the naming
--
--   zeta-sector versus zeta^2-sector
--
-- is not absolute.  Simultaneously replacing z by z^-1 exchanges the two
-- selected eigensectors and, on the 6.Suz side, exchanges the conjugate
-- character labels in each faithful pair {12a,12b} and {78a,78b}.
--
-- Daniel Allcock's Eisenstein-Leech formulation supplies an independent
-- conceptual cross-check: the scalar omega in 6.Suz may be identified with
-- either generator of the Heisenberg centre, giving two corresponding
-- quotient identifications.  Bray--Wilson remains the explicit computational
-- source for which diagonal quotient is the Monster central product.
--
-- Consequence for proof accounting:
--
--   pair-family occurrence + diagonal quotient identity = invariant content;
--   absolute a/b -> zeta naming requires an orientation convention for z.
--
-- Therefore absence of an externally fixed z orientation is a coordinate
-- choice, not evidence that the pair-family representation itself is unpaid.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Independent conceptual attribution.
------------------------------------------------------------------------

allcockMonstrousProposal : Attribution.AttributedSource
allcockMonstrousProposal = Attribution.mkNoDOISource
  "Daniel Allcock"
  "A Monstrous Proposal"
  "Groups and Symmetries, CRM Proceedings and Lecture Notes 47, 17-24"
  "2009; arXiv preprint math/0606043 dated 2006-06-01"
  "https://arxiv.org/abs/math/0606043"
  Attribution.academicArticleSource
  "independent conceptual source for identifying the scalar omega of 6.Suz with a generator of the Heisenberg centre and for the existence of two generator choices; no DOI located/asserted for this proceedings article"
  Attribution.publicAttribution

allcockAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt allcockMonstrousProposal

allcockArxiv : String
allcockArxiv = "math/0606043"

brayWilsonDOI : String
brayWilsonDOI = Diagonal.paperDOI

record PhaseGaugeExternalCoordinates : Set where
  constructor phase-gauge-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasOrientationAuthority : Bool
open PhaseGaugeExternalCoordinates public

canonicalPhaseGaugeExternalCoordinates : PhaseGaugeExternalCoordinates
canonicalPhaseGaugeExternalCoordinates =
  phase-gauge-external-coordinates
    "Q1055807"
    "Q600043"
    "Q1057968"
    "512.22"
    "512.23"
    "not applicable: orientation of a central generator and its conjugate character labels is not an integer-sequence identity"
    false

------------------------------------------------------------------------
-- 2. Orientation carrier and involution.
------------------------------------------------------------------------

data CentralGeneratorOrientation : Set where
  chooseZ chooseZInverse : CentralGeneratorOrientation

invertOrientation : CentralGeneratorOrientation → CentralGeneratorOrientation
invertOrientation chooseZ = chooseZInverse
invertOrientation chooseZInverse = chooseZ

invertOrientationInvolutive :
  (orientation : CentralGeneratorOrientation) →
  invertOrientation (invertOrientation orientation) ≡ orientation
invertOrientationInvolutive chooseZ = refl
invertOrientationInvolutive chooseZInverse = refl

data ConjugatePairMember : Set where
  memberA memberB : ConjugatePairMember

swapPairMember : ConjugatePairMember → ConjugatePairMember
swapPairMember memberA = memberB
swapPairMember memberB = memberA

swapPairMemberInvolutive :
  (member : ConjugatePairMember) →
  swapPairMember (swapPairMember member) ≡ member
swapPairMemberInvolutive memberA = refl
swapPairMemberInvolutive memberB = refl

record OrientedSuzukiMultiplicityLabels : Set where
  constructor oriented-suzuki-multiplicity-labels
  field
    orientation : CentralGeneratorOrientation
    twelveMember : ConjugatePairMember
    seventyEightMember : ConjugatePairMember
    twelveAtlasLabel : String
    seventyEightAtlasLabel : String

open OrientedSuzukiMultiplicityLabels public

record OrientationReversal : Set₁ where
  constructor orientation-reversal
  field
    before : OrientedSuzukiMultiplicityLabels
    after : OrientedSuzukiMultiplicityLabels
    orientationReversed :
      orientation after ≡ invertOrientation (orientation before)
    twelveMemberSwapped :
      twelveMember after ≡ swapPairMember (twelveMember before)
    seventyEightMemberSwapped :
      seventyEightMember after ≡ swapPairMember (seventyEightMember before)

open OrientationReversal public

------------------------------------------------------------------------
-- 3. Invariant pair-family content versus orientation-dependent section.
------------------------------------------------------------------------

record OrientationInvariantMonsterMultiplicity : Set₁ where
  constructor orientation-invariant-monster-multiplicity
  field
    pairFamilyReceipt : PairMatch.SuzukiMainQuotientSameObjectReceipt
    diagonalQuotientReceipt : Diagonal.MonsterDiagonalOrientationReceipt
    twelveConjugatePairInvariant : Set
    seventyEightConjugatePairInvariant : Set
    totalMultiplicityNinetyInvariant : Set

open OrientationInvariantMonsterMultiplicity public

record OrientedSelectedZetaSection
  (invariant : OrientationInvariantMonsterMultiplicity) : Set₁ where
  field
    centralGeneratorOrientation : CentralGeneratorOrientation
    labels : OrientedSuzukiMultiplicityLabels
    labelsUseChosenOrientation :
      orientation labels ≡ centralGeneratorOrientation
    quotientCompatibility : Set
    selectedZetaSameObjectReceipt : Set

open OrientedSelectedZetaSection public

------------------------------------------------------------------------
-- 4. WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data PairFamilyRequiresAbsoluteABConvention : Set where
data GeneratorOrientationIsIntrinsicGroupInvariant : Set where
data SwappingGeneratorChangesUnorientedPairFamily : Set where
data AllcockConceptualAnalogyCreatesMonsterQuotientReceipt : Set where

pairFamilyDoesNotRequireAbsoluteAB :
  PairFamilyRequiresAbsoluteABConvention → ⊥
pairFamilyDoesNotRequireAbsoluteAB ()

generatorOrientationNotIntrinsic :
  GeneratorOrientationIsIntrinsicGroupInvariant → ⊥
generatorOrientationNotIntrinsic ()

swapDoesNotChangeUnorientedPairFamily :
  SwappingGeneratorChangesUnorientedPairFamily → ⊥
swapDoesNotChangeUnorientedPairFamily ()

allcockDoesNotCreateMonsterReceipt :
  AllcockConceptualAnalogyCreatesMonsterQuotientReceipt → ⊥
allcockDoesNotCreateMonsterReceipt ()

------------------------------------------------------------------------
-- 5. Proof-debt reclassification.
------------------------------------------------------------------------

record PhaseOrientationGaugeFrontier : Set where
  constructor phase-orientation-gauge-frontier
  field
    twoCentralGeneratorChoicesOwned : Bool
    orientationInvolutionOwned : Bool
    conjugatePairSwapOwned : Bool
    allcockIndependentConceptualCrossCheckPaid : Bool
    brayWilsonExplicitDiagonalSourceStillAuthoritative : Bool
    pairFamilyOccurrenceIndependentOfAbsoluteABNaming : Bool
    pairFamilyExecutionReceiptPaid : Bool
    diagonalKernelIdentityPaid : Bool
    externalCentralGeneratorOrientationFixed : Bool
    individualABToSelectedZetaSameObjectPaid : Bool
    nextResidual : String
open PhaseOrientationGaugeFrontier public

currentPhaseOrientationGaugeFrontier : PhaseOrientationGaugeFrontier
currentPhaseOrientationGaugeFrontier =
  phase-orientation-gauge-frontier
    true true true true true true
    false false false false
    "first pay the pair-family and diagonal-kernel receipts. If no external convention fixes which nonidentity centre element is called z, stop treating absolute a/b naming as theorem debt: choose an orientation and transport all phase labels coherently. Only if a specific historical/computational z generator is fixed must a later receipt prove the absolute 12a-vs-12b and 78a-vs-78b naming for that generator."
