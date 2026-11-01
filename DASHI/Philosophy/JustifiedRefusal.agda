module DASHI.Philosophy.JustifiedRefusal where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Relationality does not require compulsory reconciliation or unsafe access.

data RefusalGround : Set where
  domination : RefusalGround
  badFaith : RefusalGround
  repeatedHarm : RefusalGround
  noReciprocity : RefusalGround
  unsafeExposure : RefusalGround
  impossibleRepairConditions : RefusalGround

canonicalRefusalGrounds : List RefusalGround
canonicalRefusalGrounds =
  domination ∷ badFaith ∷ repeatedHarm ∷ noReciprocity ∷
  unsafeExposure ∷ impossibleRepairConditions ∷ []

record RefusalReceipt (Party Relation Evidence Boundary : Set) : Set₁ where
  field
    refusingParty : Party
    relation : Relation
    ground : RefusalGround
    evidence : Evidence
    boundary : Boundary
    harmMitigation : Set
    reviewPossible : Bool
    refusalErasesOtherParty : Bool

open RefusalReceipt public

record RefusalBoundary : Set where
  constructor mkRefusalBoundary
  field
    everyRefusalIsClosedMinded : Bool
    everyRelationMustContinue : Bool
    safetyCanJustifyRefusal : Bool
    refusalNeedsReceipt : Bool
    disagreementAloneJustifiesErasure : Bool

open RefusalBoundary public

canonicalRefusalBoundary : RefusalBoundary
canonicalRefusalBoundary =
  mkRefusalBoundary false false true true false

canonicalNoCompulsoryReconciliation :
  everyRelationMustContinue canonicalRefusalBoundary ≡ false
canonicalNoCompulsoryReconciliation = refl
