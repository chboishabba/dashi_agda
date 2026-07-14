module DASHI.Physics.Closure.NSTriadKNConcreteNonResidualFiberEnumeration where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as ForcedTail
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as Adversarial
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as Transition
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTailEstimates
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as AdversarialEstimates
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as TransitionEstimates
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula using
  (_∈_; here; there; weightedListSum;
   RetainedTriadFiberEnumerationInputs;
   mkRetainedTriadFiberEnumerationInputs)

------------------------------------------------------------------------
-- This module is an encoded finite enumeration only.  Its incidence type is
-- the existing tagged non-residual proxy; it does not construct the separate
-- physical relation or claim any Navier-Stokes or Clay closure.
------------------------------------------------------------------------

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

mapMember : {A B : Set} →
  (f : A → B) → {x : A} {xs : List A} →
  x ∈ xs → f x ∈ mapList f xs
mapMember f {xs = []} ()
mapMember f {xs = x ∷ xs} here = here
mapMember f {xs = x ∷ xs} (there p) = there (mapMember f p)

mapMembershipProperty : {A B : Set} →
  (f : A → B) → (P : B → Set) →
  ((x : A) → P (f x)) → {y : B} {xs : List A} →
  y ∈ mapList f xs → P y
mapMembershipProperty f P proof {xs = []} ()
mapMembershipProperty f P proof {xs = x ∷ xs} here = proof x
mapMembershipProperty f P proof {xs = x ∷ xs} (there p) =
  mapMembershipProperty f P proof p

emptyMember : {A : Set} {x : A} {P : Set} → x ∈ [] → P
emptyMember ()

------------------------------------------------------------------------
-- Canonical enumeration of every Fin residue.
------------------------------------------------------------------------

mapFinSuc : {n : Nat} → List (Fin n) → List (Fin (suc n))
mapFinSuc [] = []
mapFinSuc (i ∷ is) = fsuc i ∷ mapFinSuc is

mapFinSucMember : {n : Nat} {i : Fin n} {xs : List (Fin n)} →
  i ∈ xs → fsuc i ∈ mapFinSuc xs
mapFinSucMember {xs = []} ()
mapFinSucMember {xs = i ∷ xs} here = here
mapFinSucMember {xs = i ∷ xs} (there p) = there (mapFinSucMember p)

allFin : {n : Nat} → List (Fin n)
allFin {n = zero} = []
allFin {n = suc n} = fzero ∷ mapFinSuc (allFin {n = n})

allFinMember : {n : Nat} → (i : Fin n) → i ∈ allFin
allFinMember fzero = here
allFinMember (fsuc i) = there (mapFinSucMember (allFinMember i))

------------------------------------------------------------------------
-- One diagonal class fiber is the image of allFin under the incidence
-- constructor.  Mixed class pairs are empty, so the tagged union remains
-- disjoint without an untyped equality test.
------------------------------------------------------------------------

forcedTailFiber : {N : Nat} →
  {c : ForcedTailEstimates.ForcedTailClass} →
  ForcedTail.ForcedTailHead c N → ForcedTail.ForcedTailTail c N →
  List (Relation.ConcreteNonResidualTriadIncidence N)
forcedTailFiber {c = c} h t =
  mapList
    (λ r → Relation.forcedTailIncidence c
      (ForcedTail.mkForcedTailTriadIncidence h t r))
    allFin

adversarialFiber : {N : Nat} →
  {c : AdversarialEstimates.AdversarialClass} →
  Adversarial.AdversarialHead c N → Adversarial.AdversarialTail c N →
  List (Relation.ConcreteNonResidualTriadIncidence N)
adversarialFiber {c = c} h t =
  mapList
    (λ r → Relation.adversarialIncidence c
      (Adversarial.mkAdversarialTriadIncidence h t r))
    allFin

transitionFiber : {N : Nat} →
  {c : TransitionEstimates.TransitionClass} →
  Transition.TransitionHead c N → Transition.TransitionTail c N →
  List (Relation.ConcreteNonResidualTriadIncidence N)
transitionFiber {c = c} h t =
  mapList
    (λ r → Relation.transitionIncidence c
      (Transition.mkTransitionTriadIncidence h t r))
    allFin

forcedTailDiagonalFiber : {N : Nat} →
  (c c' : ForcedTailEstimates.ForcedTailClass) →
  ForcedTail.ForcedTailHead c N → ForcedTail.ForcedTailTail c' N →
  List (Relation.ConcreteNonResidualTriadIncidence N)
forcedTailDiagonalFiber ForcedTailEstimates.tailEnd ForcedTailEstimates.tailEnd h t =
  forcedTailFiber h t
forcedTailDiagonalFiber ForcedTailEstimates.tailEnd ForcedTailEstimates.nearTail h t = []
forcedTailDiagonalFiber ForcedTailEstimates.tailEnd ForcedTailEstimates.transition h t = []
forcedTailDiagonalFiber ForcedTailEstimates.tailEnd ForcedTailEstimates.degenerate h t = []
forcedTailDiagonalFiber ForcedTailEstimates.nearTail ForcedTailEstimates.tailEnd h t = []
forcedTailDiagonalFiber ForcedTailEstimates.nearTail ForcedTailEstimates.nearTail h t =
  forcedTailFiber h t
forcedTailDiagonalFiber ForcedTailEstimates.nearTail ForcedTailEstimates.transition h t = []
forcedTailDiagonalFiber ForcedTailEstimates.nearTail ForcedTailEstimates.degenerate h t = []
forcedTailDiagonalFiber ForcedTailEstimates.transition ForcedTailEstimates.tailEnd h t = []
forcedTailDiagonalFiber ForcedTailEstimates.transition ForcedTailEstimates.nearTail h t = []
forcedTailDiagonalFiber ForcedTailEstimates.transition ForcedTailEstimates.transition h t =
  forcedTailFiber h t
forcedTailDiagonalFiber ForcedTailEstimates.transition ForcedTailEstimates.degenerate h t = []
forcedTailDiagonalFiber ForcedTailEstimates.degenerate ForcedTailEstimates.tailEnd h t = []
forcedTailDiagonalFiber ForcedTailEstimates.degenerate ForcedTailEstimates.nearTail h t = []
forcedTailDiagonalFiber ForcedTailEstimates.degenerate ForcedTailEstimates.transition h t = []
forcedTailDiagonalFiber ForcedTailEstimates.degenerate ForcedTailEstimates.degenerate h t =
  forcedTailFiber h t

adversarialDiagonalFiber : {N : Nat} →
  (c c' : AdversarialEstimates.AdversarialClass) →
  Adversarial.AdversarialHead c N → Adversarial.AdversarialTail c' N →
  List (Relation.ConcreteNonResidualTriadIncidence N)
adversarialDiagonalFiber AdversarialEstimates.sparseAdmissible
  AdversarialEstimates.sparseAdmissible h t = adversarialFiber h t
adversarialDiagonalFiber AdversarialEstimates.sparseAdmissible
  AdversarialEstimates.angularDegenerate h t = []
adversarialDiagonalFiber AdversarialEstimates.sparseAdmissible
  AdversarialEstimates.boundarySmallShell h t = []
adversarialDiagonalFiber AdversarialEstimates.angularDegenerate
  AdversarialEstimates.sparseAdmissible h t = []
adversarialDiagonalFiber AdversarialEstimates.angularDegenerate
  AdversarialEstimates.angularDegenerate h t = adversarialFiber h t
adversarialDiagonalFiber AdversarialEstimates.angularDegenerate
  AdversarialEstimates.boundarySmallShell h t = []
adversarialDiagonalFiber AdversarialEstimates.boundarySmallShell
  AdversarialEstimates.sparseAdmissible h t = []
adversarialDiagonalFiber AdversarialEstimates.boundarySmallShell
  AdversarialEstimates.angularDegenerate h t = []
adversarialDiagonalFiber AdversarialEstimates.boundarySmallShell
  AdversarialEstimates.boundarySmallShell h t = adversarialFiber h t

transitionDiagonalFiber : {N : Nat} →
  (c c' : TransitionEstimates.TransitionClass) →
  Transition.TransitionHead c N → Transition.TransitionTail c' N →
  List (Relation.ConcreteNonResidualTriadIncidence N)
transitionDiagonalFiber TransitionEstimates.thinTransition TransitionEstimates.thinTransition h t =
  transitionFiber h t
transitionDiagonalFiber TransitionEstimates.thinTransition TransitionEstimates.balancedTransition h t = []
transitionDiagonalFiber TransitionEstimates.thinTransition TransitionEstimates.rowThickTransition h t = []
transitionDiagonalFiber TransitionEstimates.thinTransition TransitionEstimates.columnThickTransition h t = []
transitionDiagonalFiber TransitionEstimates.balancedTransition TransitionEstimates.thinTransition h t = []
transitionDiagonalFiber TransitionEstimates.balancedTransition TransitionEstimates.balancedTransition h t =
  transitionFiber h t
transitionDiagonalFiber TransitionEstimates.balancedTransition TransitionEstimates.rowThickTransition h t = []
transitionDiagonalFiber TransitionEstimates.balancedTransition TransitionEstimates.columnThickTransition h t = []
transitionDiagonalFiber TransitionEstimates.rowThickTransition TransitionEstimates.thinTransition h t = []
transitionDiagonalFiber TransitionEstimates.rowThickTransition TransitionEstimates.balancedTransition h t = []
transitionDiagonalFiber TransitionEstimates.rowThickTransition TransitionEstimates.rowThickTransition h t =
  transitionFiber h t
transitionDiagonalFiber TransitionEstimates.rowThickTransition TransitionEstimates.columnThickTransition h t = []
transitionDiagonalFiber TransitionEstimates.columnThickTransition TransitionEstimates.thinTransition h t = []
transitionDiagonalFiber TransitionEstimates.columnThickTransition TransitionEstimates.balancedTransition h t = []
transitionDiagonalFiber TransitionEstimates.columnThickTransition TransitionEstimates.rowThickTransition h t = []
transitionDiagonalFiber TransitionEstimates.columnThickTransition TransitionEstimates.columnThickTransition h t =
  transitionFiber h t

encodedFiber : {N : Nat} →
  Relation.ConcreteNonResidualFiniteIndex N →
  Relation.ConcreteNonResidualTailIndex N →
  List (Relation.ConcreteNonResidualTriadIncidence N)
encodedFiber (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex c' t) =
  forcedTailDiagonalFiber c c' h t
encodedFiber (Relation.forcedTailFiniteIndex c h)
  (Relation.adversarialTailIndex c' t) = []
encodedFiber (Relation.forcedTailFiniteIndex c h)
  (Relation.transitionTailIndex c' t) = []
encodedFiber (Relation.adversarialFiniteIndex c h)
  (Relation.forcedTailTailIndex c' t) = []
encodedFiber (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex c' t) =
  adversarialDiagonalFiber c c' h t
encodedFiber (Relation.adversarialFiniteIndex c h)
  (Relation.transitionTailIndex c' t) = []
encodedFiber (Relation.transitionFiniteIndex c h)
  (Relation.forcedTailTailIndex c' t) = []
encodedFiber (Relation.transitionFiniteIndex c h)
  (Relation.adversarialTailIndex c' t) = []
encodedFiber (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex c' t) =
  transitionDiagonalFiber c c' h t

------------------------------------------------------------------------
-- Source/target agreement and retained-sector agreement.
------------------------------------------------------------------------

forcedTailSourceAgreement : {N : Nat} →
  {c : ForcedTailEstimates.ForcedTailClass} →
  (h : ForcedTail.ForcedTailHead c N) →
  (t : ForcedTail.ForcedTailTail c N) →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  r ∈ forcedTailFiber h t →
  Relation.concreteNonResidualSourceIndex r ≡
  Relation.forcedTailFiniteIndex c h
forcedTailSourceAgreement h t r p =
  mapMembershipProperty
    (λ q → Relation.forcedTailIncidence _
      (ForcedTail.mkForcedTailTriadIncidence h t q))
    (λ x → Relation.concreteNonResidualSourceIndex x ≡
      Relation.forcedTailFiniteIndex _ h)
    (λ q → refl)
    p

forcedTailTargetAgreement : {N : Nat} →
  {c : ForcedTailEstimates.ForcedTailClass} →
  (h : ForcedTail.ForcedTailHead c N) →
  (t : ForcedTail.ForcedTailTail c N) →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  r ∈ forcedTailFiber h t →
  Relation.concreteNonResidualTargetIndex r ≡
  Relation.forcedTailTailIndex c t
forcedTailTargetAgreement h t r p =
  mapMembershipProperty
    (λ q → Relation.forcedTailIncidence _
      (ForcedTail.mkForcedTailTriadIncidence h t q))
    (λ x → Relation.concreteNonResidualTargetIndex x ≡
      Relation.forcedTailTailIndex _ t)
    (λ q → refl)
    p

adversarialSourceAgreement : {N : Nat} →
  {c : AdversarialEstimates.AdversarialClass} →
  (h : Adversarial.AdversarialHead c N) →
  (t : Adversarial.AdversarialTail c N) →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  r ∈ adversarialFiber h t →
  Relation.concreteNonResidualSourceIndex r ≡
  Relation.adversarialFiniteIndex c h
adversarialSourceAgreement h t r p =
  mapMembershipProperty
    (λ q → Relation.adversarialIncidence _
      (Adversarial.mkAdversarialTriadIncidence h t q))
    (λ x → Relation.concreteNonResidualSourceIndex x ≡
      Relation.adversarialFiniteIndex _ h)
    (λ q → refl)
    p

adversarialTargetAgreement : {N : Nat} →
  {c : AdversarialEstimates.AdversarialClass} →
  (h : Adversarial.AdversarialHead c N) →
  (t : Adversarial.AdversarialTail c N) →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  r ∈ adversarialFiber h t →
  Relation.concreteNonResidualTargetIndex r ≡
  Relation.adversarialTailIndex c t
adversarialTargetAgreement h t r p =
  mapMembershipProperty
    (λ q → Relation.adversarialIncidence _
      (Adversarial.mkAdversarialTriadIncidence h t q))
    (λ x → Relation.concreteNonResidualTargetIndex x ≡
      Relation.adversarialTailIndex _ t)
    (λ q → refl)
    p

transitionSourceAgreement : {N : Nat} →
  {c : TransitionEstimates.TransitionClass} →
  (h : Transition.TransitionHead c N) →
  (t : Transition.TransitionTail c N) →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  r ∈ transitionFiber h t →
  Relation.concreteNonResidualSourceIndex r ≡
  Relation.transitionFiniteIndex c h
transitionSourceAgreement h t r p =
  mapMembershipProperty
    (λ q → Relation.transitionIncidence _
      (Transition.mkTransitionTriadIncidence h t q))
    (λ x → Relation.concreteNonResidualSourceIndex x ≡
      Relation.transitionFiniteIndex _ h)
    (λ q → refl)
    p

transitionTargetAgreement : {N : Nat} →
  {c : TransitionEstimates.TransitionClass} →
  (h : Transition.TransitionHead c N) →
  (t : Transition.TransitionTail c N) →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  r ∈ transitionFiber h t →
  Relation.concreteNonResidualTargetIndex r ≡
  Relation.transitionTailIndex c t
transitionTargetAgreement h t r p =
  mapMembershipProperty
    (λ q → Relation.transitionIncidence _
      (Transition.mkTransitionTriadIncidence h t q))
    (λ x → Relation.concreteNonResidualTargetIndex x ≡
      Relation.transitionTailIndex _ t)
    (λ q → refl)
    p

encodedFiberSourceAgreement : {N : Nat} →
  {f : Relation.ConcreteNonResidualFiniteIndex N} →
  {t : Relation.ConcreteNonResidualTailIndex N} →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  r ∈ encodedFiber f t →
  Relation.concreteNonResidualSourceIndex r ≡ f
encodedFiberSourceAgreement {f = Relation.forcedTailFiniteIndex c h}
  {t = Relation.forcedTailTailIndex c' t} r p with c | c'
... | ForcedTailEstimates.tailEnd | ForcedTailEstimates.tailEnd = forcedTailSourceAgreement h t r p
... | ForcedTailEstimates.tailEnd | ForcedTailEstimates.nearTail = emptyMember p
... | ForcedTailEstimates.tailEnd | ForcedTailEstimates.transition = emptyMember p
... | ForcedTailEstimates.tailEnd | ForcedTailEstimates.degenerate = emptyMember p
... | ForcedTailEstimates.nearTail | ForcedTailEstimates.tailEnd = emptyMember p
... | ForcedTailEstimates.nearTail | ForcedTailEstimates.nearTail = forcedTailSourceAgreement h t r p
... | ForcedTailEstimates.nearTail | ForcedTailEstimates.transition = emptyMember p
... | ForcedTailEstimates.nearTail | ForcedTailEstimates.degenerate = emptyMember p
... | ForcedTailEstimates.transition | ForcedTailEstimates.tailEnd = emptyMember p
... | ForcedTailEstimates.transition | ForcedTailEstimates.nearTail = emptyMember p
... | ForcedTailEstimates.transition | ForcedTailEstimates.transition = forcedTailSourceAgreement h t r p
... | ForcedTailEstimates.transition | ForcedTailEstimates.degenerate = emptyMember p
... | ForcedTailEstimates.degenerate | ForcedTailEstimates.tailEnd = emptyMember p
... | ForcedTailEstimates.degenerate | ForcedTailEstimates.nearTail = emptyMember p
... | ForcedTailEstimates.degenerate | ForcedTailEstimates.transition = emptyMember p
... | ForcedTailEstimates.degenerate | ForcedTailEstimates.degenerate = forcedTailSourceAgreement h t r p
encodedFiberSourceAgreement {f = Relation.forcedTailFiniteIndex c h}
  {t = Relation.adversarialTailIndex c' t} r ()
encodedFiberSourceAgreement {f = Relation.forcedTailFiniteIndex c h}
  {t = Relation.transitionTailIndex c' t} r ()
encodedFiberSourceAgreement {f = Relation.adversarialFiniteIndex c h}
  {t = Relation.forcedTailTailIndex c' t} r ()
encodedFiberSourceAgreement {f = Relation.adversarialFiniteIndex c h}
  {t = Relation.adversarialTailIndex c' t} r p = adversarialSourceAgreement h t r p
encodedFiberSourceAgreement {f = Relation.adversarialFiniteIndex c h}
  {t = Relation.transitionTailIndex c' t} r ()
encodedFiberSourceAgreement {f = Relation.transitionFiniteIndex c h}
  {t = Relation.forcedTailTailIndex c' t} r ()
encodedFiberSourceAgreement {f = Relation.transitionFiniteIndex c h}
  {t = Relation.adversarialTailIndex c' t} r ()
encodedFiberSourceAgreement {f = Relation.transitionFiniteIndex c h}
  {t = Relation.transitionTailIndex c' t} r p = transitionSourceAgreement h t r p

encodedFiberTargetAgreement : {N : Nat} →
  {f : Relation.ConcreteNonResidualFiniteIndex N} →
  {t : Relation.ConcreteNonResidualTailIndex N} →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  r ∈ encodedFiber f t →
  Relation.concreteNonResidualTargetIndex r ≡ t
encodedFiberTargetAgreement {f = Relation.forcedTailFiniteIndex c h}
  {t = Relation.forcedTailTailIndex c' t} r p with c | c'
... | ForcedTailEstimates.tailEnd | ForcedTailEstimates.tailEnd = forcedTailTargetAgreement h t r p
... | ForcedTailEstimates.tailEnd | ForcedTailEstimates.nearTail = emptyMember p
... | ForcedTailEstimates.tailEnd | ForcedTailEstimates.transition = emptyMember p
... | ForcedTailEstimates.tailEnd | ForcedTailEstimates.degenerate = emptyMember p
... | ForcedTailEstimates.nearTail | ForcedTailEstimates.tailEnd = emptyMember p
... | ForcedTailEstimates.nearTail | ForcedTailEstimates.nearTail = forcedTailTargetAgreement h t r p
... | ForcedTailEstimates.nearTail | ForcedTailEstimates.transition = emptyMember p
... | ForcedTailEstimates.nearTail | ForcedTailEstimates.degenerate = emptyMember p
... | ForcedTailEstimates.transition | ForcedTailEstimates.tailEnd = emptyMember p
... | ForcedTailEstimates.transition | ForcedTailEstimates.nearTail = emptyMember p
... | ForcedTailEstimates.transition | ForcedTailEstimates.transition = forcedTailTargetAgreement h t r p
... | ForcedTailEstimates.transition | ForcedTailEstimates.degenerate = emptyMember p
... | ForcedTailEstimates.degenerate | ForcedTailEstimates.tailEnd = emptyMember p
... | ForcedTailEstimates.degenerate | ForcedTailEstimates.nearTail = emptyMember p
... | ForcedTailEstimates.degenerate | ForcedTailEstimates.transition = emptyMember p
... | ForcedTailEstimates.degenerate | ForcedTailEstimates.degenerate = forcedTailTargetAgreement h t r p
encodedFiberTargetAgreement {f = Relation.forcedTailFiniteIndex c h}
  {t = Relation.adversarialTailIndex c' t} r ()
encodedFiberTargetAgreement {f = Relation.forcedTailFiniteIndex c h}
  {t = Relation.transitionTailIndex c' t} r ()
encodedFiberTargetAgreement {f = Relation.adversarialFiniteIndex c h}
  {t = Relation.forcedTailTailIndex c' t} r ()
encodedFiberTargetAgreement {f = Relation.adversarialFiniteIndex c h}
  {t = Relation.adversarialTailIndex c' t} r p = adversarialTargetAgreement h t r p
encodedFiberTargetAgreement {f = Relation.adversarialFiniteIndex c h}
  {t = Relation.transitionTailIndex c' t} r ()
encodedFiberTargetAgreement {f = Relation.transitionFiniteIndex c h}
  {t = Relation.forcedTailTailIndex c' t} r ()
encodedFiberTargetAgreement {f = Relation.transitionFiniteIndex c h}
  {t = Relation.adversarialTailIndex c' t} r ()
encodedFiberTargetAgreement {f = Relation.transitionFiniteIndex c h}
  {t = Relation.transitionTailIndex c' t} r p = transitionTargetAgreement h t r p

encodedFiberRetainedAgreement : {N : Nat} →
  {f : Relation.ConcreteNonResidualFiniteIndex N} →
  {t : Relation.ConcreteNonResidualTailIndex N} →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  r ∈ encodedFiber f t →
  Relation.concreteNonResidualRetainedPositiveSector r
encodedFiberRetainedAgreement _ _ = tt

------------------------------------------------------------------------
-- Completeness: source and target equalities place an incidence in the
-- corresponding diagonal class fiber.  The residue is then found by the
-- constructive allFinMember proof.
------------------------------------------------------------------------

forcedTailComplete : {N : Nat} →
  {c : ForcedTailEstimates.ForcedTailClass} →
  (h : ForcedTail.ForcedTailHead c N) →
  (t : ForcedTail.ForcedTailTail c N) →
  (r : ForcedTail.ForcedTailTriadIncidence c N) →
  Relation.concreteNonResidualSourceIndex
    (Relation.forcedTailIncidence c r) ≡
    Relation.forcedTailFiniteIndex c h →
  Relation.concreteNonResidualTargetIndex
    (Relation.forcedTailIncidence c r) ≡
    Relation.forcedTailTailIndex c t →
  Relation.forcedTailIncidence c r ∈ forcedTailFiber h t
forcedTailComplete h t
  (ForcedTail.mkForcedTailTriadIncidence .h .t r) refl refl =
  mapMember
    (λ q → Relation.forcedTailIncidence _
      (ForcedTail.mkForcedTailTriadIncidence h t q))
    (allFinMember r)

adversarialComplete : {N : Nat} →
  {c : AdversarialEstimates.AdversarialClass} →
  (h : Adversarial.AdversarialHead c N) →
  (t : Adversarial.AdversarialTail c N) →
  (r : Adversarial.AdversarialTriadIncidence c N) →
  Relation.concreteNonResidualSourceIndex
    (Relation.adversarialIncidence c r) ≡
    Relation.adversarialFiniteIndex c h →
  Relation.concreteNonResidualTargetIndex
    (Relation.adversarialIncidence c r) ≡
    Relation.adversarialTailIndex c t →
  Relation.adversarialIncidence c r ∈ adversarialFiber h t
adversarialComplete h t
  (Adversarial.mkAdversarialTriadIncidence .h .t r) refl refl =
  mapMember
    (λ q → Relation.adversarialIncidence _
      (Adversarial.mkAdversarialTriadIncidence h t q))
    (allFinMember r)

transitionComplete : {N : Nat} →
  {c : TransitionEstimates.TransitionClass} →
  (h : Transition.TransitionHead c N) →
  (t : Transition.TransitionTail c N) →
  (r : Transition.TransitionTriadIncidence c N) →
  Relation.concreteNonResidualSourceIndex
    (Relation.transitionIncidence c r) ≡
    Relation.transitionFiniteIndex c h →
  Relation.concreteNonResidualTargetIndex
    (Relation.transitionIncidence c r) ≡
    Relation.transitionTailIndex c t →
  Relation.transitionIncidence c r ∈ transitionFiber h t
transitionComplete h t
  (Transition.mkTransitionTriadIncidence .h .t r) refl refl =
  mapMember
    (λ q → Relation.transitionIncidence _
      (Transition.mkTransitionTriadIncidence h t q))
    (allFinMember r)

encodedFiberComplete : {N : Nat} →
  {f : Relation.ConcreteNonResidualFiniteIndex N} →
  {t : Relation.ConcreteNonResidualTailIndex N} →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  Relation.concreteNonResidualSourceIndex r ≡ f →
  Relation.concreteNonResidualTargetIndex r ≡ t →
  Relation.concreteNonResidualRetainedPositiveSector r →
  r ∈ encodedFiber f t
encodedFiberComplete
  {f = Relation.forcedTailFiniteIndex c h}
  {t = Relation.forcedTailTailIndex c' t}
  (Relation.forcedTailIncidence c r) hs ht _ with c | c'
... | ForcedTailEstimates.tailEnd | ForcedTailEstimates.tailEnd = forcedTailComplete h t r hs ht
... | ForcedTailEstimates.nearTail | ForcedTailEstimates.nearTail = forcedTailComplete h t r hs ht
... | ForcedTailEstimates.transition | ForcedTailEstimates.transition = forcedTailComplete h t r hs ht
... | ForcedTailEstimates.degenerate | ForcedTailEstimates.degenerate = forcedTailComplete h t r hs ht
encodedFiberComplete {f = Relation.forcedTailFiniteIndex c h}
  {t = Relation.adversarialTailIndex c' t} (Relation.forcedTailIncidence c r) () _ _
encodedFiberComplete {f = Relation.forcedTailFiniteIndex c h}
  {t = Relation.transitionTailIndex c' t} (Relation.forcedTailIncidence c r) () _ _
encodedFiberComplete {f = Relation.adversarialFiniteIndex c h}
  {t = Relation.forcedTailTailIndex c' t} (Relation.adversarialIncidence c r) () _ _
encodedFiberComplete
  {f = Relation.adversarialFiniteIndex c h}
  {t = Relation.adversarialTailIndex c' t}
  (Relation.adversarialIncidence c r) hs ht _ with c | c'
... | AdversarialEstimates.sparseAdmissible | AdversarialEstimates.sparseAdmissible = adversarialComplete h t r hs ht
... | AdversarialEstimates.angularDegenerate | AdversarialEstimates.angularDegenerate = adversarialComplete h t r hs ht
... | AdversarialEstimates.boundarySmallShell | AdversarialEstimates.boundarySmallShell = adversarialComplete h t r hs ht
encodedFiberComplete {f = Relation.adversarialFiniteIndex c h}
  {t = Relation.transitionTailIndex c' t} (Relation.adversarialIncidence c r) () _ _
encodedFiberComplete {f = Relation.transitionFiniteIndex c h}
  {t = Relation.forcedTailTailIndex c' t} (Relation.transitionIncidence c r) () _ _
encodedFiberComplete {f = Relation.transitionFiniteIndex c h}
  {t = Relation.adversarialTailIndex c' t} (Relation.transitionIncidence c r) () _ _
encodedFiberComplete
  {f = Relation.transitionFiniteIndex c h}
  {t = Relation.transitionTailIndex c' t}
  (Relation.transitionIncidence c r) hs ht _ with c | c'
... | TransitionEstimates.thinTransition | TransitionEstimates.thinTransition = transitionComplete h t r hs ht
... | TransitionEstimates.balancedTransition | TransitionEstimates.balancedTransition = transitionComplete h t r hs ht
... | TransitionEstimates.rowThickTransition | TransitionEstimates.rowThickTransition = transitionComplete h t r hs ht
... | TransitionEstimates.columnThickTransition | TransitionEstimates.columnThickTransition = transitionComplete h t r hs ht

------------------------------------------------------------------------
-- Unit encoded weights and the typed encoded-only bridge.
------------------------------------------------------------------------

triadWeight : {N : Nat} →
  Relation.ConcreteNonResidualTriadIncidence N → Nat
triadWeight _ = suc zero

triadWeightIsOne : {N : Nat} →
  (r : Relation.ConcreteNonResidualTriadIncidence N) →
  triadWeight r ≡ suc zero
triadWeightIsOne _ = refl

encodedFiberAggregate : {N : Nat} →
  Relation.ConcreteNonResidualFiniteIndex N →
  Relation.ConcreteNonResidualTailIndex N → Nat
encodedFiberAggregate f t =
  KernelFormula.weightedListSum triadWeight (encodedFiber f t)

encodedFiberAggregateIsWeightedListSum : {N : Nat} →
  (f : Relation.ConcreteNonResidualFiniteIndex N) →
  (t : Relation.ConcreteNonResidualTailIndex N) →
  encodedFiberAggregate f t ≡
  KernelFormula.weightedListSum triadWeight (encodedFiber f t)
encodedFiberAggregateIsWeightedListSum _ _ = refl

EncodedConcreteNonResidualFiberTarget : Nat → Set₁
EncodedConcreteNonResidualFiberTarget N =
  KernelFormula.RetainedTriadFiberEnumerationInputs
    (Relation.ConcreteNonResidualFiniteIndex N)
    (Relation.ConcreteNonResidualTailIndex N)
    (Relation.ConcreteNonResidualTriadIncidence N)
    Relation.concreteNonResidualSourceIndex
    Relation.concreteNonResidualTargetIndex
    Relation.concreteNonResidualRetainedPositiveSector
    triadWeight

encodedConcreteNonResidualFiberEnumeration : {N : Nat} →
  EncodedConcreteNonResidualFiberTarget N
encodedConcreteNonResidualFiberEnumeration =
  KernelFormula.mkRetainedTriadFiberEnumerationInputs
    encodedFiber
    encodedFiberSourceAgreement
    encodedFiberTargetAgreement
    encodedFiberRetainedAgreement
    encodedFiberComplete
    encodedFiberAggregate
    encodedFiberAggregateIsWeightedListSum

encodedOnlyBridgeIsNotPhysicalFormulaTarget :
  Set
encodedOnlyBridgeIsNotPhysicalFormulaTarget = ⊤
