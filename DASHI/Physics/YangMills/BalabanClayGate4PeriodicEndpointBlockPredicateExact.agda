module DASHI.Physics.YangMills.BalabanClayGate4PeriodicEndpointBlockPredicateExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Empty; Dec; yes; no; Not; _∈_; here; there;
    PositiveBond; DecidableEquality; productDecidableEquality;
    periodicTorus4DecidableEquality; cyclicIndexDecidableEquality)

import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support

------------------------------------------------------------------------
-- Literal endpoint-block support from explicit finite block lists.
--
-- Once each endpoint block is given as a finite list of positive fine bonds,
-- membership and the endpoint union are decidable by the repository's existing
-- periodic equality.  This removes decidability as an independent physical
-- theorem: the remaining geometric work is constructing the correct lists and
-- proving that they coincide with Bałaban's derivative support.
------------------------------------------------------------------------

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

data Either (left right : Set) : Set where
  leftWitness : left → Either left right
  rightWitness : right → Either left right

positiveBondDecidableEquality :
  ∀ side → DecidableEquality (PositiveBond side)
positiveBondDecidableEquality side =
  productDecidableEquality
    (periodicTorus4DecidableEquality side)
    cyclicIndexDecidableEquality

membershipDecidable :
  ∀ {A : Set} →
  DecidableEquality A →
  (value : A) → (values : List A) →
  Dec (value ∈ values)
membershipDecidable decide value [] = no (λ ())
membershipDecidable decide value (candidate ∷ values)
  with decide value candidate
... | yes equality with equality
...   | yes _ = yes here
... | no value≢candidate with membershipDecidable decide value values
...   | yes membership = yes (there membership)
...   | no absent = no λ where
      here → value≢candidate (Agda.Builtin.Equality.refl)
      (there membership) → absent membership

unionDecidable :
  ∀ {left right : Set} →
  Dec left → Dec right → Dec (Either left right)
unionDecidable (yes leftProof) rightDecision =
  yes (leftWitness leftProof)
unionDecidable (no leftRefutation) (yes rightProof) =
  yes (rightWitness rightProof)
unionDecidable (no leftRefutation) (no rightRefutation) =
  no λ where
    (leftWitness proof) → leftRefutation proof
    (rightWitness proof) → rightRefutation proof

record PeriodicEndpointBlockLists
    (fineSide coarseSide : Nat) : Set₁ where
  field
    sourceEndpointBlock targetEndpointBlock :
      PositiveBond coarseSide → List (PositiveBond fineSide)

open PeriodicEndpointBlockLists public

FineBondInSourceEndpointBlock :
  ∀ {fineSide coarseSide} →
  PeriodicEndpointBlockLists fineSide coarseSide →
  PositiveBond coarseSide → PositiveBond fineSide → Set
FineBondInSourceEndpointBlock geometry coarse fine =
  fine ∈ sourceEndpointBlock geometry coarse

FineBondInTargetEndpointBlock :
  ∀ {fineSide coarseSide} →
  PeriodicEndpointBlockLists fineSide coarseSide →
  PositiveBond coarseSide → PositiveBond fineSide → Set
FineBondInTargetEndpointBlock geometry coarse fine =
  fine ∈ targetEndpointBlock geometry coarse

EndpointBlockUnionSupport :
  ∀ {fineSide coarseSide} →
  PeriodicEndpointBlockLists fineSide coarseSide →
  PositiveBond coarseSide → PositiveBond fineSide → Set
EndpointBlockUnionSupport geometry coarse fine =
  Either
    (FineBondInSourceEndpointBlock geometry coarse fine)
    (FineBondInTargetEndpointBlock geometry coarse fine)

fineBondInSourceEndpointBlockDecidable :
  ∀ {fineSide coarseSide}
    (geometry : PeriodicEndpointBlockLists fineSide coarseSide)
    coarse fine →
  Dec (FineBondInSourceEndpointBlock geometry coarse fine)
fineBondInSourceEndpointBlockDecidable {fineSide = fineSide} geometry coarse fine =
  membershipDecidable
    (positiveBondDecidableEquality fineSide)
    fine
    (sourceEndpointBlock geometry coarse)

fineBondInTargetEndpointBlockDecidable :
  ∀ {fineSide coarseSide}
    (geometry : PeriodicEndpointBlockLists fineSide coarseSide)
    coarse fine →
  Dec (FineBondInTargetEndpointBlock geometry coarse fine)
fineBondInTargetEndpointBlockDecidable {fineSide = fineSide} geometry coarse fine =
  membershipDecidable
    (positiveBondDecidableEquality fineSide)
    fine
    (targetEndpointBlock geometry coarse)

endpointBlockUnionSupportDecidable :
  ∀ {fineSide coarseSide}
    (geometry : PeriodicEndpointBlockLists fineSide coarseSide)
    coarse fine →
  Dec (EndpointBlockUnionSupport geometry coarse fine)
endpointBlockUnionSupportDecidable geometry coarse fine =
  unionDecidable
    (fineBondInSourceEndpointBlockDecidable geometry coarse fine)
    (fineBondInTargetEndpointBlockDecidable geometry coarse fine)

endpointBlockSupportMeaning :
  ∀ {fineSide coarseSide}
    (geometry : PeriodicEndpointBlockLists fineSide coarseSide) →
  Support.PeriodicQkSupportMeaning fineSide coarseSide
endpointBlockSupportMeaning geometry =
  Support.periodicQkSupportMeaningFromEndpointPredicate
    (EndpointBlockUnionSupport geometry)
    (endpointBlockUnionSupportDecidable geometry)

record TranslationCovariantEndpointBlocks
    {fineSide coarseSide : Nat}
    (geometry : PeriodicEndpointBlockLists fineSide coarseSide)
    (Translation : Set) : Set₁ where
  field
    translateCoarse : Translation → PositiveBond coarseSide → PositiveBond coarseSide
    translateFine : Translation → PositiveBond fineSide → PositiveBond fineSide

    SourceMembershipTranslationIff :
      Translation → PositiveBond coarseSide → PositiveBond fineSide → Set
    TargetMembershipTranslationIff :
      Translation → PositiveBond coarseSide → PositiveBond fineSide → Set

    sourceMembershipTranslationIff : ∀ translation coarse fine →
      SourceMembershipTranslationIff translation coarse fine

    targetMembershipTranslationIff : ∀ translation coarse fine →
      TargetMembershipTranslationIff translation coarse fine

    sourceForward : ∀ translation coarse fine →
      FineBondInSourceEndpointBlock geometry coarse fine →
      FineBondInSourceEndpointBlock geometry
        (translateCoarse translation coarse)
        (translateFine translation fine)

    sourceBackward : ∀ translation coarse fine →
      FineBondInSourceEndpointBlock geometry
        (translateCoarse translation coarse)
        (translateFine translation fine) →
      FineBondInSourceEndpointBlock geometry coarse fine

    targetForward : ∀ translation coarse fine →
      FineBondInTargetEndpointBlock geometry coarse fine →
      FineBondInTargetEndpointBlock geometry
        (translateCoarse translation coarse)
        (translateFine translation fine)

    targetBackward : ∀ translation coarse fine →
      FineBondInTargetEndpointBlock geometry
        (translateCoarse translation coarse)
        (translateFine translation fine) →
      FineBondInTargetEndpointBlock geometry coarse fine

open TranslationCovariantEndpointBlocks public

endpointBlockUnionTranslationForward :
  ∀ {fineSide coarseSide Translation}
    {geometry : PeriodicEndpointBlockLists fineSide coarseSide}
    (dataSet : TranslationCovariantEndpointBlocks geometry Translation)
    translation coarse fine →
  EndpointBlockUnionSupport geometry coarse fine →
  EndpointBlockUnionSupport geometry
    (translateCoarse dataSet translation coarse)
    (translateFine dataSet translation fine)
endpointBlockUnionTranslationForward dataSet translation coarse fine
  (leftWitness source) =
    leftWitness (sourceForward dataSet translation coarse fine source)
endpointBlockUnionTranslationForward dataSet translation coarse fine
  (rightWitness target) =
    rightWitness (targetForward dataSet translation coarse fine target)

endpointBlockUnionTranslationBackward :
  ∀ {fineSide coarseSide Translation}
    {geometry : PeriodicEndpointBlockLists fineSide coarseSide}
    (dataSet : TranslationCovariantEndpointBlocks geometry Translation)
    translation coarse fine →
  EndpointBlockUnionSupport geometry
    (translateCoarse dataSet translation coarse)
    (translateFine dataSet translation fine) →
  EndpointBlockUnionSupport geometry coarse fine
endpointBlockUnionTranslationBackward dataSet translation coarse fine
  (leftWitness source) =
    leftWitness (sourceBackward dataSet translation coarse fine source)
endpointBlockUnionTranslationBackward dataSet translation coarse fine
  (rightWitness target) =
    rightWitness (targetBackward dataSet translation coarse fine target)

periodicEndpointBlockMembershipDecidableLevel : ProofLevel
periodicEndpointBlockMembershipDecidableLevel = machineChecked

periodicEndpointUnionDecidableLevel : ProofLevel
periodicEndpointUnionDecidableLevel = machineChecked

periodicEndpointSupportCarrierAssemblyLevel : ProofLevel
periodicEndpointSupportCarrierAssemblyLevel = machineChecked

endpointBlockTranslationTransportLevel : ProofLevel
endpointBlockTranslationTransportLevel = machineChecked

physicalEndpointBlockListConstructionInputsLevel : ProofLevel
physicalEndpointBlockListConstructionInputsLevel = conditional

physicalDerivativeSupportIdentificationInputsLevel : ProofLevel
physicalDerivativeSupportIdentificationInputsLevel = conditional

physicalBlockTranslationCovarianceInputsLevel : ProofLevel
physicalBlockTranslationCovarianceInputsLevel = conditional
