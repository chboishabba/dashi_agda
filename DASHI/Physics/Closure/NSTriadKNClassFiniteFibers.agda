module DASHI.Physics.Closure.NSTriadKNClassFiniteFibers where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import Data.Fin as Fin

import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as FTClass
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as FT
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as AdvClass
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as Adv
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as TrClass
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as Tr
open import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedAuthorities public

open KernelFormula using (_∈_)

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

enumerateFin : (n : Nat) → List (Fin.Fin n)
enumerateFin zero = []
enumerateFin (suc n) = Fin.zero ∷ mapList Fin.suc (enumerateFin n)

mapMembership :
  {A B : Set} {x : A} {xs : List A} →
  (f : A → B) → x ∈ xs → f x ∈ mapList f xs
mapMembership f KernelFormula.here = KernelFormula.here
mapMembership f (KernelFormula.there member) =
  KernelFormula.there (mapMembership f member)

enumerateFinComplete : {n : Nat} → (r : Fin.Fin n) → r ∈ enumerateFin n
enumerateFinComplete {suc n} Fin.zero = KernelFormula.here
enumerateFinComplete {suc n} (Fin.suc r) =
  KernelFormula.there (mapMembership Fin.suc (enumerateFinComplete r))

infix 4 _∉_
_∉_ : {A : Set} → A → List A → Set
x ∉ xs = x ∈ xs → ⊥

data NoDuplicates {A : Set} : List A → Set where
  unique[] : NoDuplicates []
  unique∷ : {x : A} {xs : List A} → x ∉ xs → NoDuplicates xs → NoDuplicates (x ∷ xs)

zeroNotInSucMap : {n : Nat} {xs : List (Fin.Fin n)} → Fin.zero ∉ mapList Fin.suc xs
zeroNotInSucMap {xs = []} ()
zeroNotInSucMap {xs = _ ∷ _} (KernelFormula.there member) = zeroNotInSucMap member

sucMembershipReflect :
  {n : Nat} {x : Fin.Fin n} {xs : List (Fin.Fin n)} →
  Fin.suc x ∈ mapList Fin.suc xs → x ∈ xs
sucMembershipReflect {xs = _ ∷ _} KernelFormula.here = KernelFormula.here
sucMembershipReflect {xs = _ ∷ _} (KernelFormula.there member) =
  KernelFormula.there (sucMembershipReflect member)

mapSucNoDuplicates :
  {n : Nat} {xs : List (Fin.Fin n)} → NoDuplicates xs → NoDuplicates (mapList Fin.suc xs)
mapSucNoDuplicates unique[] = unique[]
mapSucNoDuplicates (unique∷ headFresh tailUnique) =
  unique∷
    (λ member → headFresh (sucMembershipReflect member))
    (mapSucNoDuplicates tailUnique)

enumerateFinNoDuplicates : (n : Nat) → NoDuplicates (enumerateFin n)
enumerateFinNoDuplicates zero = unique[]
enumerateFinNoDuplicates (suc n) =
  unique∷ zeroNotInSucMap (mapSucNoDuplicates (enumerateFinNoDuplicates n))

mapMembershipReflect :
  {A B : Set} {x : A} {xs : List A} →
  (f : A → B) →
  ((u v : A) → f u ≡ f v → u ≡ v) →
  f x ∈ mapList f xs → x ∈ xs
mapMembershipReflect f injective {xs = y ∷ ys} KernelFormula.here
  with injective x y refl
... | refl = KernelFormula.here
mapMembershipReflect f injective {xs = y ∷ ys} (KernelFormula.there member) =
  KernelFormula.there (mapMembershipReflect f injective member)

mapNoDuplicates :
  {A B : Set} {xs : List A} →
  (f : A → B) →
  ((u v : A) → f u ≡ f v → u ≡ v) →
  NoDuplicates xs → NoDuplicates (mapList f xs)
mapNoDuplicates f injective unique[] = unique[]
mapNoDuplicates f injective (unique∷ headFresh tailUnique) =
  unique∷
    (λ member → headFresh (mapMembershipReflect f injective member))
    (mapNoDuplicates f injective tailUnique)

mappedPropertyWithMembership :
  {A B : Set} →
  (xs : List A) →
  (f : A → B) →
  (P : B → Set) →
  ((x : A) → x ∈ xs → P (f x)) →
  (y : B) → y ∈ mapList f xs → P y
mappedPropertyWithMembership [] f P local y ()
mappedPropertyWithMembership (x ∷ xs) f P local .(f x) KernelFormula.here =
  local x KernelFormula.here
mappedPropertyWithMembership (x ∷ xs) f P local y (KernelFormula.there member) =
  mappedPropertyWithMembership
    xs f P
    (λ z zMember → local z (KernelFormula.there zMember))
    y member

------------------------------------------------------------------------
-- Class-specific literal fibers.
------------------------------------------------------------------------

enumerateForcedTailResidues :
  (c : FTClass.ForcedTailClass) → List (Fin.Fin (FTClass.forcedTailFiberConstant c))
enumerateForcedTailResidues c = enumerateFin (FTClass.forcedTailFiberConstant c)

forcedTailFiber :
  {c : FTClass.ForcedTailClass} {N : Nat} →
  FT.ForcedTailHead c N → FT.ForcedTailTail c N →
  List (FT.ForcedTailTriadIncidence c N)
forcedTailFiber {c} h t =
  mapList (FT.forcedTailFiberFromResidue h t) (enumerateForcedTailResidues c)

forcedTailFiberSourceAgreement :
  {c : FTClass.ForcedTailClass} {N : Nat} →
  (h : FT.ForcedTailHead c N) → (t : FT.ForcedTailTail c N) →
  (τ : FT.ForcedTailTriadIncidence c N) →
  τ ∈ forcedTailFiber h t → FT.headParam τ ≡ h
forcedTailFiberSourceAgreement {c} h t τ member =
  mappedPropertyWithMembership
    (enumerateForcedTailResidues c)
    (FT.forcedTailFiberFromResidue h t)
    (λ σ → FT.headParam σ ≡ h)
    (λ r rMember → refl) τ member

forcedTailFiberTargetAgreement :
  {c : FTClass.ForcedTailClass} {N : Nat} →
  (h : FT.ForcedTailHead c N) → (t : FT.ForcedTailTail c N) →
  (τ : FT.ForcedTailTriadIncidence c N) →
  τ ∈ forcedTailFiber h t → FT.tailParam τ ≡ t
forcedTailFiberTargetAgreement {c} h t τ member =
  mappedPropertyWithMembership
    (enumerateForcedTailResidues c)
    (FT.forcedTailFiberFromResidue h t)
    (λ σ → FT.tailParam σ ≡ t)
    (λ r rMember → refl) τ member

forcedTailFiberRetainedAgreement :
  {realization : ConcreteFourierRealization} →
  {weights : PhysicalTriadWeightAuthority realization} →
  {predicates : PhysicalRetainedSectorPredicates realization weights} →
  (landing : PhysicalRetainedFamilyLanding predicates) →
  {c : FTClass.ForcedTailClass} {N : Nat} →
  (h : FT.ForcedTailHead c N) → (t : FT.ForcedTailTail c N) →
  (τ : FT.ForcedTailTriadIncidence c N) →
  τ ∈ forcedTailFiber h t →
  PhysicalRetainedPositiveSector predicates (Relation.forcedTailIncidence c τ)
forcedTailFiberRetainedAgreement landing h t τ member =
  forcedTailIncidenceRetained landing τ

forcedTailFiberComplete :
  {realization : ConcreteFourierRealization} →
  {weights : PhysicalTriadWeightAuthority realization} →
  {predicates : PhysicalRetainedSectorPredicates realization weights} →
  (landing : PhysicalRetainedFamilyLanding predicates) →
  {c : FTClass.ForcedTailClass} {N : Nat} →
  (h : FT.ForcedTailHead c N) → (t : FT.ForcedTailTail c N) →
  (τ : FT.ForcedTailTriadIncidence c N) →
  FT.headParam τ ≡ h → FT.tailParam τ ≡ t →
  PhysicalRetainedPositiveSector predicates (Relation.forcedTailIncidence c τ) →
  τ ∈ forcedTailFiber h t
forcedTailFiberComplete landing h t
  (FT.mkForcedTailTriadIncidence .h .t r) refl refl retained =
  mapMembership (FT.forcedTailFiberFromResidue h t) (enumerateFinComplete r)

forcedTailFiberNoDuplicates :
  {c : FTClass.ForcedTailClass} {N : Nat} →
  (h : FT.ForcedTailHead c N) → (t : FT.ForcedTailTail c N) →
  NoDuplicates (forcedTailFiber h t)
forcedTailFiberNoDuplicates {c} h t =
  mapNoDuplicates
    (FT.forcedTailFiberFromResidue h t)
    (λ r s equality → cong FT.residueTag equality)
    (enumerateFinNoDuplicates (FTClass.forcedTailFiberConstant c))

adversarialFiberFromResidue :
  {c : AdvClass.AdversarialClass} {N : Nat} →
  Adv.AdversarialHead c N → Adv.AdversarialTail c N →
  Fin.Fin (Adv.adversarialFiberConstant c) →
  Adv.AdversarialTriadIncidence c N
adversarialFiberFromResidue h t r = Adv.mkAdversarialTriadIncidence h t r

adversarialFiberToResidue :
  {c : AdvClass.AdversarialClass} {N : Nat} →
  Adv.AdversarialTriadIncidence c N → Fin.Fin (Adv.adversarialFiberConstant c)
adversarialFiberToResidue = Adv.residueTag

enumerateAdversarialResidues :
  (c : AdvClass.AdversarialClass) → List (Fin.Fin (Adv.adversarialFiberConstant c))
enumerateAdversarialResidues c = enumerateFin (Adv.adversarialFiberConstant c)

adversarialFiber :
  {c : AdvClass.AdversarialClass} {N : Nat} →
  Adv.AdversarialHead c N → Adv.AdversarialTail c N →
  List (Adv.AdversarialTriadIncidence c N)
adversarialFiber {c} h t =
  mapList (adversarialFiberFromResidue h t) (enumerateAdversarialResidues c)

adversarialFiberSourceAgreement :
  {c : AdvClass.AdversarialClass} {N : Nat} →
  (h : Adv.AdversarialHead c N) → (t : Adv.AdversarialTail c N) →
  (τ : Adv.AdversarialTriadIncidence c N) →
  τ ∈ adversarialFiber h t → Adv.headParam τ ≡ h
adversarialFiberSourceAgreement {c} h t τ member =
  mappedPropertyWithMembership
    (enumerateAdversarialResidues c)
    (adversarialFiberFromResidue h t)
    (λ σ → Adv.headParam σ ≡ h)
    (λ r rMember → refl) τ member

adversarialFiberTargetAgreement :
  {c : AdvClass.AdversarialClass} {N : Nat} →
  (h : Adv.AdversarialHead c N) → (t : Adv.AdversarialTail c N) →
  (τ : Adv.AdversarialTriadIncidence c N) →
  τ ∈ adversarialFiber h t → Adv.tailParam τ ≡ t
adversarialFiberTargetAgreement {c} h t τ member =
  mappedPropertyWithMembership
    (enumerateAdversarialResidues c)
    (adversarialFiberFromResidue h t)
    (λ σ → Adv.tailParam σ ≡ t)
    (λ r rMember → refl) τ member

adversarialFiberRetainedAgreement :
  {realization : ConcreteFourierRealization} →
  {weights : PhysicalTriadWeightAuthority realization} →
  {predicates : PhysicalRetainedSectorPredicates realization weights} →
  (landing : PhysicalRetainedFamilyLanding predicates) →
  {c : AdvClass.AdversarialClass} {N : Nat} →
  (h : Adv.AdversarialHead c N) → (t : Adv.AdversarialTail c N) →
  (τ : Adv.AdversarialTriadIncidence c N) →
  τ ∈ adversarialFiber h t →
  PhysicalRetainedPositiveSector predicates (Relation.adversarialIncidence c τ)
adversarialFiberRetainedAgreement landing h t τ member =
  adversarialIncidenceRetained landing τ

adversarialFiberComplete :
  {realization : ConcreteFourierRealization} →
  {weights : PhysicalTriadWeightAuthority realization} →
  {predicates : PhysicalRetainedSectorPredicates realization weights} →
  (landing : PhysicalRetainedFamilyLanding predicates) →
  {c : AdvClass.AdversarialClass} {N : Nat} →
  (h : Adv.AdversarialHead c N) → (t : Adv.AdversarialTail c N) →
  (τ : Adv.AdversarialTriadIncidence c N) →
  Adv.headParam τ ≡ h → Adv.tailParam τ ≡ t →
  PhysicalRetainedPositiveSector predicates (Relation.adversarialIncidence c τ) →
  τ ∈ adversarialFiber h t
adversarialFiberComplete landing h t
  (Adv.mkAdversarialTriadIncidence .h .t r) refl refl retained =
  mapMembership (adversarialFiberFromResidue h t) (enumerateFinComplete r)

adversarialFiberNoDuplicates :
  {c : AdvClass.AdversarialClass} {N : Nat} →
  (h : Adv.AdversarialHead c N) → (t : Adv.AdversarialTail c N) →
  NoDuplicates (adversarialFiber h t)
adversarialFiberNoDuplicates {c} h t =
  mapNoDuplicates
    (adversarialFiberFromResidue h t)
    (λ r s equality → cong Adv.residueTag equality)
    (enumerateFinNoDuplicates (Adv.adversarialFiberConstant c))

transitionFiberFromResidue :
  {c : TrClass.TransitionClass} {N : Nat} →
  Tr.TransitionHead c N → Tr.TransitionTail c N →
  Fin.Fin (Tr.transitionFiberConstant c) → Tr.TransitionTriadIncidence c N
transitionFiberFromResidue h t r = Tr.mkTransitionTriadIncidence h t r

transitionFiberToResidue :
  {c : TrClass.TransitionClass} {N : Nat} →
  Tr.TransitionTriadIncidence c N → Fin.Fin (Tr.transitionFiberConstant c)
transitionFiberToResidue = Tr.residueTag

enumerateTransitionResidues :
  (c : TrClass.TransitionClass) → List (Fin.Fin (Tr.transitionFiberConstant c))
enumerateTransitionResidues c = enumerateFin (Tr.transitionFiberConstant c)

transitionFiber :
  {c : TrClass.TransitionClass} {N : Nat} →
  Tr.TransitionHead c N → Tr.TransitionTail c N →
  List (Tr.TransitionTriadIncidence c N)
transitionFiber {c} h t =
  mapList (transitionFiberFromResidue h t) (enumerateTransitionResidues c)

transitionFiberSourceAgreement :
  {c : TrClass.TransitionClass} {N : Nat} →
  (h : Tr.TransitionHead c N) → (t : Tr.TransitionTail c N) →
  (τ : Tr.TransitionTriadIncidence c N) →
  τ ∈ transitionFiber h t → Tr.headParam τ ≡ h
transitionFiberSourceAgreement {c} h t τ member =
  mappedPropertyWithMembership
    (enumerateTransitionResidues c)
    (transitionFiberFromResidue h t)
    (λ σ → Tr.headParam σ ≡ h)
    (λ r rMember → refl) τ member

transitionFiberTargetAgreement :
  {c : TrClass.TransitionClass} {N : Nat} →
  (h : Tr.TransitionHead c N) → (t : Tr.TransitionTail c N) →
  (τ : Tr.TransitionTriadIncidence c N) →
  τ ∈ transitionFiber h t → Tr.tailParam τ ≡ t
transitionFiberTargetAgreement {c} h t τ member =
  mappedPropertyWithMembership
    (enumerateTransitionResidues c)
    (transitionFiberFromResidue h t)
    (λ σ → Tr.tailParam σ ≡ t)
    (λ r rMember → refl) τ member

transitionFiberRetainedAgreement :
  {realization : ConcreteFourierRealization} →
  {weights : PhysicalTriadWeightAuthority realization} →
  {predicates : PhysicalRetainedSectorPredicates realization weights} →
  (landing : PhysicalRetainedFamilyLanding predicates) →
  {c : TrClass.TransitionClass} {N : Nat} →
  (h : Tr.TransitionHead c N) → (t : Tr.TransitionTail c N) →
  (τ : Tr.TransitionTriadIncidence c N) →
  τ ∈ transitionFiber h t →
  PhysicalRetainedPositiveSector predicates (Relation.transitionIncidence c τ)
transitionFiberRetainedAgreement landing h t τ member =
  transitionIncidenceRetained landing τ

transitionFiberComplete :
  {realization : ConcreteFourierRealization} →
  {weights : PhysicalTriadWeightAuthority realization} →
  {predicates : PhysicalRetainedSectorPredicates realization weights} →
  (landing : PhysicalRetainedFamilyLanding predicates) →
  {c : TrClass.TransitionClass} {N : Nat} →
  (h : Tr.TransitionHead c N) → (t : Tr.TransitionTail c N) →
  (τ : Tr.TransitionTriadIncidence c N) →
  Tr.headParam τ ≡ h → Tr.tailParam τ ≡ t →
  PhysicalRetainedPositiveSector predicates (Relation.transitionIncidence c τ) →
  τ ∈ transitionFiber h t
transitionFiberComplete landing h t
  (Tr.mkTransitionTriadIncidence .h .t r) refl refl retained =
  mapMembership (transitionFiberFromResidue h t) (enumerateFinComplete r)

transitionFiberNoDuplicates :
  {c : TrClass.TransitionClass} {N : Nat} →
  (h : Tr.TransitionHead c N) → (t : Tr.TransitionTail c N) →
  NoDuplicates (transitionFiber h t)
transitionFiberNoDuplicates {c} h t =
  mapNoDuplicates
    (transitionFiberFromResidue h t)
    (λ r s equality → cong Tr.residueTag equality)
    (enumerateFinNoDuplicates (Tr.transitionFiberConstant c))
