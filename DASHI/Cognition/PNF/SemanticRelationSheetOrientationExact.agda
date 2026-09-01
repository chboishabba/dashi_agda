module DASHI.Cognition.PNF.SemanticRelationSheetOrientationExact where

-- A complete three-role semantic relation sheet.  The one-edge signed relation
-- used by a local consumer is a projection of this richer 3x3 object.
--
-- This owner keeps permutation/relation symmetry separate from Base369 cyclic
-- phase symmetry.  Any phase interpretation must supply an explicit
-- intertwining theorem downstream.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv; inv-invol)

------------------------------------------------------------------------
-- 1. Three typed semantic positions and their full relation sheet.
------------------------------------------------------------------------

data SemanticPosition3 : Set where
  leftEntity rightEntity contextualEntity : SemanticPosition3

record SemanticRelationSheet3 : Set where
  constructor semanticRelationSheet3
  field
    ll lr lc
      rl rr rc
      cl cr cc : Trit

open SemanticRelationSheet3 public

relationAt :
  SemanticRelationSheet3 → SemanticPosition3 → SemanticPosition3 → Trit
relationAt s leftEntity leftEntity = ll s
relationAt s leftEntity rightEntity = lr s
relationAt s leftEntity contextualEntity = lc s
relationAt s rightEntity leftEntity = rl s
relationAt s rightEntity rightEntity = rr s
relationAt s rightEntity contextualEntity = rc s
relationAt s contextualEntity leftEntity = cl s
relationAt s contextualEntity rightEntity = cr s
relationAt s contextualEntity contextualEntity = cc s

------------------------------------------------------------------------
-- 2. Transposition and signed inversion.
------------------------------------------------------------------------

transposeSheet : SemanticRelationSheet3 → SemanticRelationSheet3
transposeSheet s =
  semanticRelationSheet3
    (ll s) (rl s) (cl s)
    (lr s) (rr s) (cr s)
    (lc s) (rc s) (cc s)

invertSheet : SemanticRelationSheet3 → SemanticRelationSheet3
invertSheet s =
  semanticRelationSheet3
    (inv (ll s)) (inv (lr s)) (inv (lc s))
    (inv (rl s)) (inv (rr s)) (inv (rc s))
    (inv (cl s)) (inv (cr s)) (inv (cc s))

transposeInvolutive :
  (s : SemanticRelationSheet3) → transposeSheet (transposeSheet s) ≡ s
transposeInvolutive (semanticRelationSheet3 a b c d e f g h i) = refl

invertSheetInvolutive :
  (s : SemanticRelationSheet3) → invertSheet (invertSheet s) ≡ s
invertSheetInvolutive (semanticRelationSheet3 a b c d e f g h i)
  rewrite inv-invol a
        | inv-invol b
        | inv-invol c
        | inv-invol d
        | inv-invol e
        | inv-invol f
        | inv-invol g
        | inv-invol h
        | inv-invol i
  = refl

------------------------------------------------------------------------
-- 3. Antisymmetric oriented semantic sheet.
--
-- For an oriented relation, reversing an ordered pair flips the sign and the
-- diagonal is neutral.  The property is carried as proofs rather than inferred
-- from the nine-value carrier alone.
------------------------------------------------------------------------

record OrientedRelationSheet : Set where
  constructor orientedRelationSheet
  field
    sheet : SemanticRelationSheet3
    diagonalLeftNeutral : ll sheet ≡ zer
    diagonalRightNeutral : rr sheet ≡ zer
    diagonalContextNeutral : cc sheet ≡ zer
    leftRightAntisymmetric : rl sheet ≡ inv (lr sheet)
    leftContextAntisymmetric : cl sheet ≡ inv (lc sheet)
    rightContextAntisymmetric : cr sheet ≡ inv (rc sheet)

open OrientedRelationSheet public

canonicalDirectedSheet : OrientedRelationSheet
canonicalDirectedSheet =
  orientedRelationSheet
    (semanticRelationSheet3
      zer pos zer
      neg zer neg
      zer pos zer)
    refl refl refl refl refl refl

canonicalLeftToRight :
  relationAt (sheet canonicalDirectedSheet) leftEntity rightEntity ≡ pos
canonicalLeftToRight = refl

canonicalRightToLeft :
  relationAt (sheet canonicalDirectedSheet) rightEntity leftEntity ≡ neg
canonicalRightToLeft = refl

------------------------------------------------------------------------
-- 4. Reversing the relation is transposition.
--
-- On an antisymmetric oriented sheet, transposition flips each off-diagonal
-- sign.  This is the relation-level theorem that a later phase bridge may be
-- required to intertwine with phase inversion.
------------------------------------------------------------------------

canonicalTranspose :
  transposeSheet (sheet canonicalDirectedSheet) ≡
  semanticRelationSheet3
    zer neg zer
    pos zer pos
    zer neg zer
canonicalTranspose = refl

canonicalTransposeFlipsLeftRight :
  relationAt (transposeSheet (sheet canonicalDirectedSheet))
    leftEntity rightEntity
  ≡ inv (relationAt (sheet canonicalDirectedSheet) leftEntity rightEntity)
canonicalTransposeFlipsLeftRight = refl

------------------------------------------------------------------------
-- 5. One-edge query projection.
------------------------------------------------------------------------

record RelationQuery : Set where
  constructor relationQuery
  field
    source target : SemanticPosition3

open RelationQuery public

observeRelation : RelationQuery → SemanticRelationSheet3 → Trit
observeRelation q s = relationAt s (source q) (target q)

leftToRightQuery : RelationQuery
leftToRightQuery = relationQuery leftEntity rightEntity

canonicalOneEdgeProjection :
  observeRelation leftToRightQuery (sheet canonicalDirectedSheet) ≡ pos
canonicalOneEdgeProjection = refl

------------------------------------------------------------------------
-- 6. Phase-intertwiner authority boundary.
------------------------------------------------------------------------

record RelationPhaseIntertwiner
  (Phase : Set)
  (invertPhase : Phase → Phase)
  : Set₁ where
  constructor relationPhaseIntertwiner
  field
    projectPhase : SemanticRelationSheet3 → Phase
    transposeIntertwinesInversion :
      (s : SemanticRelationSheet3) →
      projectPhase (transposeSheet s) ≡ invertPhase (projectPhase s)

record SemanticRelationSheetBoundary : Set where
  constructor semanticRelationSheetBoundary
  field
    nineCellRelationSheetConstructed : Bool
    nineCellRelationSheetConstructedIsTrue :
      nineCellRelationSheetConstructed ≡ true
    transposeRelationSymmetryConstructed : Bool
    transposeRelationSymmetryConstructedIsTrue :
      transposeRelationSymmetryConstructed ≡ true
    cyclicC9PhaseIdentifiedWithoutIntertwiner : Bool
    cyclicC9PhaseIdentifiedWithoutIntertwinerIsFalse :
      cyclicC9PhaseIdentifiedWithoutIntertwiner ≡ false

canonicalSemanticRelationSheetBoundary : SemanticRelationSheetBoundary
canonicalSemanticRelationSheetBoundary =
  semanticRelationSheetBoundary true refl true refl false refl
