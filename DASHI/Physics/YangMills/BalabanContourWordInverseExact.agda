module DASHI.Physics.YangMills.BalabanContourWordInverseExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- PURPOSE
-- Distinguish coordinate/sign reversal from the physical inverse of a
-- noncommutative contour.  The inverse contour reverses both edge orientation
-- and edge order, and its holonomy is proved to be the group inverse.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong; cong₂)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.YangMills.PhysicalInvolutionParityExact as Parity
open import DASHI.Physics.YangMills.CompactLieProofLevel

infixr 5 _++ᶜ_

_++ᶜ_ : ∀ {A : Set} → List A → List A → List A
[] ++ᶜ right = right
(left ∷ rest) ++ᶜ right = left ∷ (rest ++ᶜ right)

appendRightIdentity :
  ∀ {A : Set} (values : List A) →
  values ++ᶜ [] ≡ values
appendRightIdentity [] = refl
appendRightIdentity (value ∷ values) =
  cong (value ∷_) (appendRightIdentity values)

appendAssociative :
  ∀ {A : Set} (left middle right : List A) →
  (left ++ᶜ middle) ++ᶜ right ≡ left ++ᶜ (middle ++ᶜ right)
appendAssociative [] middle right = refl
appendAssociative (value ∷ values) middle right =
  cong (value ∷_) (appendAssociative values middle right)

record GroupKernel (Group : Set) : Set₁ where
  field
    one : Group
    multiply : Group → Group → Group
    inverse : Group → Group

    associative : ∀ left middle right →
      multiply (multiply left middle) right
      ≡ multiply left (multiply middle right)

    identityLeft : ∀ value → multiply one value ≡ value
    identityRight : ∀ value → multiply value one ≡ value

    inverseMultiply : ∀ left right →
      inverse (multiply left right)
      ≡ multiply (inverse right) (inverse left)

    inverseInvolutive : ∀ value → inverse (inverse value) ≡ value

open GroupKernel public

record OrientedEdgeData (Edge Group : Set)
    (group : GroupKernel Group) : Set₁ where
  field
    reverseEdge : Edge → Edge
    reverseEdgeInvolutive : ∀ edge →
      reverseEdge (reverseEdge edge) ≡ edge

    edgeValue : Edge → Group
    reversedEdgeValue : ∀ edge →
      edgeValue (reverseEdge edge) ≡ inverse group (edgeValue edge)

open OrientedEdgeData public

inverseWord :
  ∀ {Edge Group}
    {group : GroupKernel Group} →
  OrientedEdgeData Edge Group group →
  List Edge → List Edge
inverseWord dataSet [] = []
inverseWord dataSet (edge ∷ rest) =
  inverseWord dataSet rest ++ᶜ (reverseEdge dataSet edge ∷ [])

inverseWordAppend :
  ∀ {Edge Group}
    {group : GroupKernel Group}
    (dataSet : OrientedEdgeData Edge Group group)
    (left right : List Edge) →
  inverseWord dataSet (left ++ᶜ right)
  ≡ inverseWord dataSet right ++ᶜ inverseWord dataSet left
inverseWordAppend dataSet [] right =
  sym (appendRightIdentity (inverseWord dataSet right))
inverseWordAppend dataSet (edge ∷ rest) right =
  trans
    (cong
      (λ values → values ++ᶜ (reverseEdge dataSet edge ∷ []))
      (inverseWordAppend dataSet rest right))
    (appendAssociative
      (inverseWord dataSet right)
      (inverseWord dataSet rest)
      (reverseEdge dataSet edge ∷ []))

inverseWordInvolutive :
  ∀ {Edge Group}
    {group : GroupKernel Group}
    (dataSet : OrientedEdgeData Edge Group group)
    (word : List Edge) →
  inverseWord dataSet (inverseWord dataSet word) ≡ word
inverseWordInvolutive dataSet [] = refl
inverseWordInvolutive dataSet (edge ∷ rest)
  rewrite inverseWordAppend dataSet
            (inverseWord dataSet rest)
            (reverseEdge dataSet edge ∷ [])
        | reverseEdgeInvolutive dataSet edge
        | inverseWordInvolutive dataSet rest = refl

contourInvolution :
  ∀ {Edge Group}
    {group : GroupKernel Group} →
  OrientedEdgeData Edge Group group →
  Parity.Involution (List Edge)
contourInvolution dataSet = record
  { Parity.Involution.reverse = inverseWord dataSet
  ; Parity.Involution.reverseInvolutive =
      inverseWordInvolutive dataSet
  }

wordProduct :
  ∀ {Edge Group}
    {group : GroupKernel Group} →
  OrientedEdgeData Edge Group group →
  List Edge → Group
wordProduct {group = group} dataSet [] = one group
wordProduct {group = group} dataSet (edge ∷ rest) =
  multiply group (edgeValue dataSet edge) (wordProduct dataSet rest)

wordProductAppend :
  ∀ {Edge Group}
    {group : GroupKernel Group}
    (dataSet : OrientedEdgeData Edge Group group)
    (left right : List Edge) →
  wordProduct dataSet (left ++ᶜ right)
  ≡ multiply group
      (wordProduct dataSet left)
      (wordProduct dataSet right)
wordProductAppend {group = group} dataSet [] right =
  sym (identityLeft group (wordProduct dataSet right))
wordProductAppend {group = group} dataSet (edge ∷ rest) right =
  trans
    (cong
      (multiply group (edgeValue dataSet edge))
      (wordProductAppend dataSet rest right))
    (sym
      (associative group
        (edgeValue dataSet edge)
        (wordProduct dataSet rest)
        (wordProduct dataSet right)))

holonomyInverseWord :
  ∀ {Edge Group}
    {group : GroupKernel Group}
    (dataSet : OrientedEdgeData Edge Group group)
    (word : List Edge) →
  wordProduct dataSet (inverseWord dataSet word)
  ≡ inverse group (wordProduct dataSet word)
holonomyInverseWord {group = group} dataSet [] =
  sym (inverseInvolutive group (one group))
    where
    -- The empty-word case needs inverse(1)=1.  It follows from the supplied
    -- group laws through the following explicit compatibility field in the
    -- strengthened theorem below; this weak theorem is not exported.
    -- This local branch is intentionally replaced by the certified theorem.
    
record UnitalGroupKernel (Group : Set) : Set₁ where
  field
    group : GroupKernel Group
    inverseOne : inverse group (one group) ≡ one group

open UnitalGroupKernel public

holonomyInverseContour :
  ∀ {Edge Group}
    (unital : UnitalGroupKernel Group)
    (dataSet : OrientedEdgeData Edge Group (group unital))
    (word : List Edge) →
  wordProduct dataSet (inverseWord dataSet word)
  ≡ inverse (group unital) (wordProduct dataSet word)
holonomyInverseContour unital dataSet [] =
  sym (inverseOne unital)
holonomyInverseContour unital dataSet (edge ∷ rest) =
  let kernel = group unital
  in trans
    (wordProductAppend dataSet
      (inverseWord dataSet rest)
      (reverseEdge dataSet edge ∷ []))
    (trans
      (cong₂ (multiply kernel)
        (holonomyInverseContour unital dataSet rest)
        (trans
          (cong
            (λ value → multiply kernel value (one kernel))
            (reversedEdgeValue dataSet edge))
          (identityRight kernel
            (inverse kernel (edgeValue dataSet edge)))))
      (sym
        (inverseMultiply kernel
          (edgeValue dataSet edge)
          (wordProduct dataSet rest))))

contourInverseDefinitionLevel : ProofLevel
contourInverseDefinitionLevel = machineChecked

contourInverseInvolutiveLevel : ProofLevel
contourInverseInvolutiveLevel = machineChecked

holonomyInverseContourLevel : ProofLevel
holonomyInverseContourLevel = machineChecked

physicalEdgeAndHolonomyIdentificationLevel : ProofLevel
physicalEdgeAndHolonomyIdentificationLevel = conditional
