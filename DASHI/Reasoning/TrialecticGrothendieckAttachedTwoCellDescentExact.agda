module DASHI.Reasoning.TrialecticGrothendieckAttachedTwoCellDescentExact where

------------------------------------------------------------------------
-- GROTHENDIECK 1-DESCENT + ATTACHED TRIALECTIC 2-CELL
--
-- DASHI CONTRIBUTION
--
-- The mature finite trialectic now has three distinct categorical layers:
--
--   0-local overlap sections : participant T^3 / 27-state cells
--   1-local patch sections   : dialectical T^9 cell hyperforms
--   1-global descent section : compatible T^18 boundary
--
-- The irreducible triadic face is NOT a Cech triple intersection because the
-- literal dyadic cover has empty triple intersection and the relational
-- Grothendieck site exposes no separate triple-overlap object.
--
-- We therefore retain the face as an attached relational 2-cell whose boundary
-- is exactly the Grothendieck-descended T^18 section.  A face mediation law may
-- then select a next-depth T^3 cell.
--
-- This is an explicit finite "augmented 2-descent" interface.  It is not
-- promoted to a bicategory, 2-sheaf, higher stack, hypersheaf, simplicial
-- object, or cubical set: those names require additional composition,
-- identity/degeneracy, higher restriction and coherence laws.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Reasoning.TrialecticDyadicCoverNerveExact as Nerve
import DASHI.Reasoning.TrialecticAttachedTwoCellExact as Attached
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as GrothCell

------------------------------------------------------------------------
-- 1. Dimension-role tags.  These are categorical bookkeeping roles, not a
-- claim that the finite carriers are literal topological cells.
------------------------------------------------------------------------

data DescentCellRole : Set where
  overlapZeroCellRole : DescentCellRole
  patchOneCellRole : DescentCellRole
  attachedTwoCellRole : DescentCellRole
  promotedThreeCellRole : DescentCellRole

------------------------------------------------------------------------
-- 2. One global boundary obtained from Grothendieck descent.
------------------------------------------------------------------------

record DescendedTrialecticBoundary : Set where
  constructor descended-trialectic-boundary
  field
    locals :
      RelSheaf.TriadicLocals Cell.CellDialectic

    compatibility :
      RelSheaf.CompatibleOnTriadicCover
        GrothCell.cellOverlapSystem
        locals

    globalBoundary :
      Cell.CompatibleThreeCellTrialecticBoundary

    globalBoundaryIsGlue :
      globalBoundary
      ≡
      GrothCell.glueStructured locals compatibility

open DescendedTrialecticBoundary public

descend :
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (compatibility :
    RelSheaf.CompatibleOnTriadicCover
      GrothCell.cellOverlapSystem
      locals) →
  DescendedTrialecticBoundary
descend locals compatibility =
  descended-trialectic-boundary
    locals
    compatibility
    (GrothCell.glueStructured locals compatibility)
    refl

descendedRestrictsAB :
  (state : DescendedTrialecticBoundary) →
  Cell.edgeAB (globalBoundary state)
  ≡ RelSheaf.localAB (locals state)
descendedRestrictsAB
  (descended-trialectic-boundary locals compatibility global refl) =
  GrothCell.glueStructuredRestrictsAB locals compatibility

descendedRestrictsBC :
  (state : DescendedTrialecticBoundary) →
  Cell.edgeBC (globalBoundary state)
  ≡ RelSheaf.localBC (locals state)
descendedRestrictsBC
  (descended-trialectic-boundary locals compatibility global refl) =
  GrothCell.glueStructuredRestrictsBC locals compatibility

descendedRestrictsCA :
  (state : DescendedTrialecticBoundary) →
  Cell.edgeCA (globalBoundary state)
  ≡ RelSheaf.localCA (locals state)
descendedRestrictsCA
  (descended-trialectic-boundary locals compatibility global refl) =
  GrothCell.glueStructuredRestrictsCA locals compatibility

------------------------------------------------------------------------
-- 3. Attach the irreducible 2-cell to that exact descended boundary.
------------------------------------------------------------------------

record AttachedTrialecticTwoCell : Set where
  constructor attached-trialectic-two-cell
  field
    descended :
      DescendedTrialecticBoundary

    face :
      Face.TriadicFaceRelation

    boundaryState :
      Cell.StructuredTrialecticState

    boundaryStateExact :
      boundaryState
      ≡
      Cell.structured-trialectic-state
        (globalBoundary descended)
        face

open AttachedTrialecticTwoCell public

attachFace :
  DescendedTrialecticBoundary →
  Face.TriadicFaceRelation →
  AttachedTrialecticTwoCell
attachFace descended face =
  attached-trialectic-two-cell
    descended
    face
    (Cell.structured-trialectic-state
      (globalBoundary descended)
      face)
    refl

------------------------------------------------------------------------
-- 4. Same ordinary descent boundary, distinct 2-cells.
------------------------------------------------------------------------

canonicalDescendedBoundary :
  DescendedTrialecticBoundary
canonicalDescendedBoundary =
  descend
    (GrothCell.structuredLocals
      Cell.canonicalCompatibleThreeCellBoundary)
    (GrothCell.structuredCompatibility
      Cell.canonicalCompatibleThreeCellBoundary)

reciprocalAttachedTwoCell :
  AttachedTrialecticTwoCell
reciprocalAttachedTwoCell =
  attachFace canonicalDescendedBoundary Face.reciprocalFace

underdeterminedAttachedTwoCell :
  AttachedTrialecticTwoCell
underdeterminedAttachedTwoCell =
  attachFace canonicalDescendedBoundary Face.underdeterminedFace

ordinaryDescentObserver :
  AttachedTrialecticTwoCell →
  Cell.CompatibleThreeCellTrialecticBoundary
ordinaryDescentObserver state =
  globalBoundary (descended state)

twoCellConsumer :
  AttachedTrialecticTwoCell →
  Face.TriadicFaceRelation
twoCellConsumer = face

sameOrdinaryDescent :
  ordinaryDescentObserver reciprocalAttachedTwoCell
  ≡ ordinaryDescentObserver underdeterminedAttachedTwoCell
sameOrdinaryDescent = refl

differentAttachedTwoCell :
  twoCellConsumer reciprocalAttachedTwoCell
  ≡ twoCellConsumer underdeterminedAttachedTwoCell
  →
  ⊥
differentAttachedTwoCell ()

attachedTwoCellDoesNotDescendFromOrdinaryBoundary :
  Descent.FactorsThrough ordinaryDescentObserver twoCellConsumer →
  ⊥
attachedTwoCellDoesNotDescendFromOrdinaryBoundary =
  Descent.nonDescentWitnessBlocksFactorization
    (Descent.consumerNonDescentWitness
      reciprocalAttachedTwoCell
      underdeterminedAttachedTwoCell
      sameOrdinaryDescent
      differentAttachedTwoCell)

------------------------------------------------------------------------
-- 5. Explicit face mediation to a promoted T^3 / 27-state cell.
------------------------------------------------------------------------

TwoCellMediationLaw : Set₁
TwoCellMediationLaw =
  AttachedTrialecticTwoCell →
  Cell.TrialecticBasis3Cell →
  Set

record MediatedAttachedTwoCell
    (law : TwoCellMediationLaw) : Set₁ where
  constructor mediated-attached-two-cell
  field
    attached :
      AttachedTrialecticTwoCell

    promotedCell :
      Cell.TrialecticBasis3Cell

    mediation :
      law attached promotedCell

open MediatedAttachedTwoCell public

------------------------------------------------------------------------
-- 6. Adapter to the existing Grothendieck face-mediated section.
------------------------------------------------------------------------

toGrothendieckFaceMediatedSection :
  {law : TwoCellMediationLaw} →
  (state : MediatedAttachedTwoCell law) →
  GrothCell.GrothendieckFaceMediatedSection
    (λ boundary face output →
      law
        (attachFace
          (descended-trialectic-boundary
            (locals (descended (attached state)))
            (compatibility (descended (attached state)))
            boundary
            refl)
          face)
        output)
toGrothendieckFaceMediatedSection {law} state =
  GrothCell.grothendieck-face-mediated-section
    (locals (descended (attached state)))
    (compatibility (descended (attached state)))
    (face (attached state))
    (promotedCell state)
    (mediation state)

------------------------------------------------------------------------
-- 7. Existing nerve / attached-face results remain authoritative.
------------------------------------------------------------------------

dyadicTripleIntersectionStillEmpty :
  Nerve.TripleIntersectionWitness →
  ⊥
dyadicTripleIntersectionStillEmpty =
  Nerve.relationalDyadicTripleIntersectionEmpty

existingAttachedFaceIsNotCechTripleIntersection :
  Attached.AttachedFaceIsCechTripleIntersection →
  ⊥
existingAttachedFaceIsNotCechTripleIntersection =
  Attached.attachedFaceIsNotCechTripleIntersection

------------------------------------------------------------------------
-- 8. Higher-structure promotion boundary.
------------------------------------------------------------------------

data AugmentedTwoDescentIsBicategory : Set where
data AugmentedTwoDescentIsTwoSheaf : Set where
data AugmentedTwoDescentIsHigherStack : Set where
data AugmentedTwoDescentIsHypersheaf : Set where
data AttachedFaceIsSimplicialTwoSimplex : Set where
data AttachedFaceIsCubicalTwoFace : Set where

augmentedTwoDescentDoesNotCreateBicategory :
  AugmentedTwoDescentIsBicategory → ⊥
augmentedTwoDescentDoesNotCreateBicategory ()

augmentedTwoDescentDoesNotCreateTwoSheaf :
  AugmentedTwoDescentIsTwoSheaf → ⊥
augmentedTwoDescentDoesNotCreateTwoSheaf ()

augmentedTwoDescentDoesNotCreateHigherStack :
  AugmentedTwoDescentIsHigherStack → ⊥
augmentedTwoDescentDoesNotCreateHigherStack ()

augmentedTwoDescentDoesNotCreateHypersheaf :
  AugmentedTwoDescentIsHypersheaf → ⊥
augmentedTwoDescentDoesNotCreateHypersheaf ()

attachedFaceNotPromotedToSimplicialTwoSimplex :
  AttachedFaceIsSimplicialTwoSimplex → ⊥
attachedFaceNotPromotedToSimplicialTwoSimplex ()

attachedFaceNotPromotedToCubicalTwoFace :
  AttachedFaceIsCubicalTwoFace → ⊥
attachedFaceNotPromotedToCubicalTwoFace ()

record TrialecticGrothendieckAttachedTwoCellBoundary : Set where
  constructor trialectic-grothendieck-attached-two-cell-boundary
  field
    zeroRoleUsesT3OverlapCells : Bool
    oneRoleUsesT9DialecticalSections : Bool
    ordinaryDescentProducesT18GlobalBoundary : Bool
    attachedFaceIsAdditionalTwoCellCoordinate : Bool
    attachedFaceRecoveredByOrdinaryDescent : Bool
    promotedOutputUsesT3Cell : Bool
    tripleIntersectionRequiredForAttachedFace : Bool
    simplicialTwoSimplexClaimed : Bool
    cubicalTwoFaceClaimed : Bool
    bicategoryClaimed : Bool
    twoSheafClaimed : Bool
    higherStackClaimed : Bool
    hypersheafClaimed : Bool

canonicalTrialecticGrothendieckAttachedTwoCellBoundary :
  TrialecticGrothendieckAttachedTwoCellBoundary
canonicalTrialecticGrothendieckAttachedTwoCellBoundary =
  trialectic-grothendieck-attached-two-cell-boundary
    true
    true
    true
    true
    false
    true
    false
    false
    false
    false
    false
    false
    false
