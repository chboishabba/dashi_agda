module DASHI.Geometry.ConeArrowIsotropyShellEnumeration where

open import Agda.Builtin.Nat using (Nat)
open import Data.Bool using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; map; filterᵇ; length)
open import Data.Nat.Properties as NatP using (_≤?_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Level using (_⊔_; suc)

open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.ProjectionDefect using (Additive)
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.ConeArrowIsotropyShellAction as CAS

record ShellOrbitEnumerationDerivation {ℓv ℓs}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {QF : QuadraticForm A F}
  (shellAction : CAS.AbstractShellAction A F QF) : Set where
  field
    shell1OrbitSizes : List Nat
    shell2OrbitSizes : List Nat

open ShellOrbitEnumerationDerivation public

record FiniteCarrierShellDerivation {ℓv ℓs ℓx ℓg}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {QF : QuadraticForm A F}
  (shellAction : CAS.AbstractShellAction A F QF)
  (X : Set ℓx) (G : Set ℓg) : Set (suc (ℓv ⊔ ℓs ⊔ ℓx ⊔ ℓg)) where
  field
    decEq : (x y : X) → Dec (x ≡ y)
    carrierPoints : List X
    shell1Pred : X → Bool
    shell2Pred : X → Bool
    actions : List G
    act : G → X → X

open FiniteCarrierShellDerivation public

record FiniteShellEnumerationDerivation {ℓv ℓs ℓx ℓg}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {QF : QuadraticForm A F}
  (shellAction : CAS.AbstractShellAction A F QF)
  (X : Set ℓx) (G : Set ℓg) : Set (suc (ℓv ⊔ ℓs ⊔ ℓx ⊔ ℓg)) where
  field
    decEq : (x y : X) → Dec (x ≡ y)
    shell1Points : List X
    shell2Points : List X
    actions : List G
    act : G → X → X

open FiniteShellEnumerationDerivation public

member : ∀ {ℓ} {A : Set ℓ} → ((x y : A) → Dec (x ≡ y)) → A → List A → Bool
member dec x [] = false
member dec x (y ∷ ys) with dec x y
... | yes _ = true
... | no _ = member dec x ys

nub : ∀ {ℓ} {A : Set ℓ} → ((x y : A) → Dec (x ≡ y)) → List A → List A
nub dec [] = []
nub dec (x ∷ xs) with member dec x xs
... | true = nub dec xs
... | false = x ∷ nub dec xs

orbitSizes :
  ∀ {ℓx ℓg} {X : Set ℓx} {G : Set ℓg} →
  ((x y : X) → Dec (x ≡ y)) →
  List G →
  (G → X → X) →
  List X →
  List Nat
{-# TERMINATING #-}
orbitSizes dec gs act [] = []
orbitSizes dec gs act (x ∷ xs) =
  let
    orb = nub dec (map (λ g → act g x) gs)
    rest = filterᵇ (λ z → not (member dec z orb)) xs
  in
  length orb ∷ orbitSizes dec gs act rest
  where
    not : Bool → Bool
    not true = false
    not false = true

insertDesc : Nat → List Nat → List Nat
insertDesc x [] = x ∷ []
insertDesc x (y ∷ ys) with x NatP.≤? y
... | yes _ = y ∷ insertDesc x ys
... | no _ = x ∷ y ∷ ys

sortDesc : List Nat → List Nat
sortDesc [] = []
sortDesc (x ∷ xs) = insertDesc x (sortDesc xs)

filterBy : ∀ {ℓ} {A : Set ℓ} → (A → Bool) → List A → List A
filterBy = filterᵇ

buildShellOrbitEnumeration :
  ∀ {ℓv ℓs}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {QF : QuadraticForm A F} →
  {shellAction : CAS.AbstractShellAction A F QF} →
  ShellOrbitEnumerationDerivation shellAction →
  CTI.ShellOrbitEnumeration
buildShellOrbitEnumeration deriv =
  record
    { shell1OrbitSizes = ShellOrbitEnumerationDerivation.shell1OrbitSizes deriv
    ; shell2OrbitSizes = ShellOrbitEnumerationDerivation.shell2OrbitSizes deriv
    }

buildShellOrbitEnumerationFromFinite :
  ∀ {ℓv ℓs ℓx ℓg}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {QF : QuadraticForm A F}
  {shellAction : CAS.AbstractShellAction A F QF}
  {X : Set ℓx} {G : Set ℓg} →
  FiniteShellEnumerationDerivation shellAction X G →
  CTI.ShellOrbitEnumeration
buildShellOrbitEnumerationFromFinite deriv =
  let module D = FiniteShellEnumerationDerivation deriv in
  record
    { shell1OrbitSizes =
        sortDesc
          (orbitSizes
            D.decEq
            D.actions
            D.act
            D.shell1Points)
    ; shell2OrbitSizes =
        sortDesc
          (orbitSizes
            D.decEq
            D.actions
            D.act
            D.shell2Points)
    }

buildFiniteShellEnumeration :
  ∀ {ℓv ℓs ℓx ℓg}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {QF : QuadraticForm A F}
  {shellAction : CAS.AbstractShellAction A F QF}
  {X : Set ℓx} {G : Set ℓg} →
  FiniteCarrierShellDerivation shellAction X G →
  FiniteShellEnumerationDerivation shellAction X G
buildFiniteShellEnumeration deriv =
  let module D = FiniteCarrierShellDerivation deriv in
  record
    { decEq = D.decEq
    ; shell1Points = filterBy D.shell1Pred D.carrierPoints
    ; shell2Points = filterBy D.shell2Pred D.carrierPoints
    ; actions = D.actions
    ; act = D.act
    }

buildFiniteShellEnumerationFromShellAction :
  ∀ {ℓv ℓs}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {QF : QuadraticForm A F} →
  (shellAction : CAS.AbstractShellAction A F QF) →
  FiniteShellEnumerationDerivation
    shellAction
    (CTI.FiniteShellRealization.CarrierPoint (CAS.AbstractShellAction.finiteShell shellAction))
    (CTI.FiniteIsotropyRealization.GroupPoint
      (CAS.AbstractShellAction.finiteIso shellAction))
buildFiniteShellEnumerationFromShellAction shellAction =
  record
    { decEq = Fin.decEq
    ; shell1Points = filterBy shell1Pred' carrierPts
    ; shell2Points = filterBy shell2Pred' carrierPts
    ; actions = groupPts
    ; act = actFinite'
    }
  where
    module Fin = CTI.FiniteShellRealization (CAS.AbstractShellAction.finiteShell shellAction)
    module Iso = CTI.FiniteIsotropyRealization (CAS.AbstractShellAction.finiteIso shellAction)

    carrierPts : List Fin.CarrierPoint
    carrierPts = Fin.carrierPoints

    shell1Pred' : Fin.CarrierPoint → Bool
    shell1Pred' = Fin.shell1Pred

    shell2Pred' : Fin.CarrierPoint → Bool
    shell2Pred' = Fin.shell2Pred

    groupPts : List Iso.GroupPoint
    groupPts = Iso.groupPoints

    actFinite' : Iso.GroupPoint → Fin.CarrierPoint → Fin.CarrierPoint
    actFinite' = Iso.actFinite

buildShellOrbitEnumerationFromShellAction :
  ∀ {ℓv ℓs}
  {A : Additive ℓv} {F : ScalarField ℓs}
  {QF : QuadraticForm A F} →
  (shellAction : CAS.AbstractShellAction A F QF) →
  CTI.ShellOrbitEnumeration
buildShellOrbitEnumerationFromShellAction shellAction =
  buildShellOrbitEnumerationFromFinite
    (buildFiniteShellEnumerationFromShellAction shellAction)
