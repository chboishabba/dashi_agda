module DASHI.Physics.Closure.NSTriadKNCanonicalTriadOrbitEnumerationConcrete where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Bool.Base using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base using (ℤ)
import Data.Integer.Base as ℤ
import Data.Integer.Properties as ℤP
open import Data.List.Base using (List; []; _∷_; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNCanonicalTriadOrbitEnumeration as Orbit
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- A decidable, coordinate-lexicographic key surface.
--
-- The quotient construction below uses first occurrence in the exact raw
-- cartesian enumeration.  These keys expose that order independently, so the
-- representative choice is stable and executable rather than an opaque choice
-- function.  No numerical or sampled ordering enters the construction.
------------------------------------------------------------------------

modeLex≤ᵇ : Lattice.LatticeMode3 → Lattice.LatticeMode3 → Bool
modeLex≤ᵇ p q
  with Lattice.k₁ p ℤ.<ᵇ Lattice.k₁ q
     | Lattice.k₁ q ℤ.<ᵇ Lattice.k₁ p
... | true  | _     = true
... | false | true  = false
... | false | false
  with Lattice.k₂ p ℤ.<ᵇ Lattice.k₂ q
     | Lattice.k₂ q ℤ.<ᵇ Lattice.k₂ p
... | true  | _     = true
... | false | true  = false
... | false | false = not (Lattice.k₃ q ℤ.<ᵇ Lattice.k₃ p)

triadLex≤ᵇ : Lattice.LatticeTriad → Lattice.LatticeTriad → Bool
triadLex≤ᵇ τ σ
  with modeLex≤ᵇ (Lattice.left τ) (Lattice.left σ)
     | modeLex≤ᵇ (Lattice.left σ) (Lattice.left τ)
... | true  | false = true
... | false | true  = false
... | _     | _
  with modeLex≤ᵇ (Lattice.right τ) (Lattice.right σ)
     | modeLex≤ᵇ (Lattice.right σ) (Lattice.right τ)
... | true  | false = true
... | false | true  = false
... | _     | _ = modeLex≤ᵇ (Lattice.out τ) (Lattice.out σ)

ModeKeyLe : Lattice.LatticeMode3 → Lattice.LatticeMode3 → Set
ModeKeyLe p q = T (modeLex≤ᵇ p q)

TriadKeyLe : Lattice.LatticeTriad → Lattice.LatticeTriad → Set
TriadKeyLe τ σ = T (triadLex≤ᵇ τ σ)

modeKeyLe? : (p q : Lattice.LatticeMode3) → Dec (ModeKeyLe p q)
modeKeyLe? p q = T? (modeLex≤ᵇ p q)

triadKeyLe? : (τ σ : Lattice.LatticeTriad) → Dec (TriadKeyLe τ σ)
triadKeyLe? τ σ = T? (triadLex≤ᵇ τ σ)

------------------------------------------------------------------------
-- Exact decidable equality for modes and labelled triads.
------------------------------------------------------------------------

modeExt :
  {p q : Lattice.LatticeMode3} →
  Lattice.k₁ p ≡ Lattice.k₁ q →
  Lattice.k₂ p ≡ Lattice.k₂ q →
  Lattice.k₃ p ≡ Lattice.k₃ q → p ≡ q
modeExt {Lattice.mkLatticeMode3 _ _ _} {Lattice.mkLatticeMode3 _ _ _}
  refl refl refl = refl

mode≟ : (p q : Lattice.LatticeMode3) → Dec (p ≡ q)
mode≟ p q with ℤP._≟_ (Lattice.k₁ p) (Lattice.k₁ q)
... | no k₁≢ = no (λ p≡q → k₁≢ (cong Lattice.k₁ p≡q))
... | yes k₁≡ with ℤP._≟_ (Lattice.k₂ p) (Lattice.k₂ q)
...   | no k₂≢ = no (λ p≡q → k₂≢ (cong Lattice.k₂ p≡q))
...   | yes k₂≡ with ℤP._≟_ (Lattice.k₃ p) (Lattice.k₃ q)
...     | no k₃≢ = no (λ p≡q → k₃≢ (cong Lattice.k₃ p≡q))
...     | yes k₃≡ = yes (modeExt k₁≡ k₂≡ k₃≡)

triadExt :
  {τ σ : Lattice.LatticeTriad} →
  Lattice.left τ ≡ Lattice.left σ →
  Lattice.right τ ≡ Lattice.right σ →
  Lattice.out τ ≡ Lattice.out σ → τ ≡ σ
triadExt {Lattice.mkLatticeTriad _ _ _} {Lattice.mkLatticeTriad _ _ _}
  refl refl refl = refl

triad≟ : (τ σ : Lattice.LatticeTriad) → Dec (τ ≡ σ)
triad≟ τ σ with mode≟ (Lattice.left τ) (Lattice.left σ)
... | no left≢ = no (λ τ≡σ → left≢ (cong Lattice.left τ≡σ))
... | yes left≡ with mode≟ (Lattice.right τ) (Lattice.right σ)
...   | no right≢ = no (λ τ≡σ → right≢ (cong Lattice.right τ≡σ))
...   | yes right≡ with mode≟ (Lattice.out τ) (Lattice.out σ)
...     | no out≢ = no (λ τ≡σ → out≢ (cong Lattice.out τ≡σ))
...     | yes out≡ = yes (triadExt left≡ right≡ out≡)

decToBool : {A : Set} → Dec A → Bool
decToBool (yes _) = true
decToBool (no _) = false

triadEq? : Lattice.LatticeTriad → Lattice.LatticeTriad → Bool
triadEq? τ σ = decToBool (triad≟ τ σ)

false≢true : false ≡ true → ⊥
false≢true ()

triadEqSound :
  (τ σ : Lattice.LatticeTriad) → triadEq? τ σ ≡ true → τ ≡ σ
triadEqSound τ σ eq with triad≟ τ σ
... | yes τ≡σ = τ≡σ
... | no _ = ⊥-elim (false≢true eq)

triadEqComplete :
  (τ σ : Lattice.LatticeTriad) → τ ≡ σ → triadEq? τ σ ≡ true
triadEqComplete τ .τ refl with triad≟ τ τ
... | yes _ = refl
... | no τ≢ = ⊥-elim (τ≢ refl)

------------------------------------------------------------------------
-- Executable membership in the twelve-action permutation/reality orbit.
------------------------------------------------------------------------

triadMember? : Lattice.LatticeTriad → List Lattice.LatticeTriad → Bool
triadMember? τ [] = false
triadMember? τ (σ ∷ σs) with triadEq? τ σ
... | true = true
... | false = triadMember? τ σs

triadMemberSound :
  (τ : Lattice.LatticeTriad) → (xs : List Lattice.LatticeTriad) →
  triadMember? τ xs ≡ true → τ ∈ xs
triadMemberSound τ [] ()
triadMemberSound τ (σ ∷ σs) member with triadEq? τ σ
... | true = here (triadEqSound τ σ refl)
... | false = there (triadMemberSound τ σs member)

triadMemberComplete :
  (τ : Lattice.LatticeTriad) → (xs : List Lattice.LatticeTriad) →
  τ ∈ xs → triadMember? τ xs ≡ true
triadMemberComplete τ (σ ∷ σs) (here τ≡σ)
  rewrite triadEqComplete τ σ τ≡σ = refl
triadMemberComplete τ (σ ∷ σs) (there τ∈σs) with triadEq? τ σ
... | true = refl
... | false = triadMemberComplete τ σs τ∈σs

sameOrbit? : Lattice.LatticeTriad → Lattice.LatticeTriad → Bool
sameOrbit? τ σ = triadMember? τ (Orbit.canonicalOrbitMembers σ)

sameOrbitSound :
  (τ σ : Lattice.LatticeTriad) → sameOrbit? τ σ ≡ true →
  Orbit.SameCanonicalTriadOrbit τ σ
sameOrbitSound τ σ =
  triadMemberSound τ (Orbit.canonicalOrbitMembers σ)

sameOrbitComplete :
  (τ σ : Lattice.LatticeTriad) → Orbit.SameCanonicalTriadOrbit τ σ →
  sameOrbit? τ σ ≡ true
sameOrbitComplete τ σ =
  triadMemberComplete τ (Orbit.canonicalOrbitMembers σ)

sameOrbitRefl :
  (τ : Lattice.LatticeTriad) → Orbit.SameCanonicalTriadOrbit τ τ
sameOrbitRefl τ = here refl

------------------------------------------------------------------------
-- Inverses of the twelve concrete actions.
------------------------------------------------------------------------

reverseId :
  (τ : Lattice.LatticeTriad) → Orbit.SameCanonicalTriadOrbit τ τ
reverseId τ = here refl

reverseSwap :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ (Lattice.triadSwap τ)
reverseSwap (Lattice.mkLatticeTriad left right out) =
  there (here refl)

reverseCycle :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ (Lattice.triadCycle τ)
reverseCycle (Lattice.mkLatticeTriad left right out) =
  there (there (there (there (here refl))))

reverseSwapCycle :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ
    (Lattice.triadSwap (Lattice.triadCycle τ))
reverseSwapCycle (Lattice.mkLatticeTriad left right out) =
  there (there (there (here refl)))

reverseCycleTwice :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ (Orbit.triadCycleTwice τ)
reverseCycleTwice (Lattice.mkLatticeTriad left right out) =
  there (there (here refl))

reverseSwapCycleTwice :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ
    (Lattice.triadSwap (Orbit.triadCycleTwice τ))
reverseSwapCycleTwice (Lattice.mkLatticeTriad left right out) =
  there (there (there (there (there (here refl)))))

reverseNegId :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ (Lattice.triadNeg τ)
reverseNegId (Lattice.mkLatticeTriad left right out) =
  there (there (there (there (there (there (here refl))))))

reverseNegSwap :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ
    (Lattice.triadNeg (Lattice.triadSwap τ))
reverseNegSwap (Lattice.mkLatticeTriad left right out) =
  there (there (there (there (there (there (there (here refl)))))))

reverseNegCycle :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ
    (Lattice.triadNeg (Lattice.triadCycle τ))
reverseNegCycle (Lattice.mkLatticeTriad left right out) =
  there (there (there (there (there (there (there (there
    (there (there (here refl))))))))))

reverseNegSwapCycle :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ
    (Lattice.triadNeg (Lattice.triadSwap (Lattice.triadCycle τ)))
reverseNegSwapCycle (Lattice.mkLatticeTriad left right out) =
  there (there (there (there (there (there (there (there
    (there (here refl)))))))))

reverseNegCycleTwice :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ
    (Lattice.triadNeg (Orbit.triadCycleTwice τ))
reverseNegCycleTwice (Lattice.mkLatticeTriad left right out) =
  there (there (there (there (there (there (there (there
    (here refl))))))))

reverseNegSwapCycleTwice :
  (τ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ
    (Lattice.triadNeg (Lattice.triadSwap (Orbit.triadCycleTwice τ)))
reverseNegSwapCycleTwice (Lattice.mkLatticeTriad left right out) =
  there (there (there (there (there (there (there (there
    (there (there (there (here refl)))))))))))

sameOrbitSym :
  {τ σ : Lattice.LatticeTriad} →
  Orbit.SameCanonicalTriadOrbit τ σ →
  Orbit.SameCanonicalTriadOrbit σ τ
sameOrbitSym {τ} {σ} (here eq) rewrite eq = reverseId σ
sameOrbitSym {τ} {σ} (there (here eq)) rewrite eq = reverseSwap σ
sameOrbitSym {τ} {σ} (there (there (here eq))) rewrite eq = reverseCycle σ
sameOrbitSym {τ} {σ} (there (there (there (here eq)))) rewrite eq =
  reverseSwapCycle σ
sameOrbitSym {τ} {σ} (there (there (there (there (here eq))))) rewrite eq =
  reverseCycleTwice σ
sameOrbitSym {τ} {σ}
  (there (there (there (there (there (here eq)))))) rewrite eq =
  reverseSwapCycleTwice σ
sameOrbitSym {τ} {σ}
  (there (there (there (there (there (there (here eq))))))) rewrite eq =
  reverseNegId σ
sameOrbitSym {τ} {σ}
  (there (there (there (there (there (there (there (here eq)))))))) rewrite eq =
  reverseNegSwap σ
sameOrbitSym {τ} {σ}
  (there (there (there (there (there (there (there (there (here eq)))))))))
  rewrite eq = reverseNegCycle σ
sameOrbitSym {τ} {σ}
  (there (there (there (there (there (there (there (there
    (there (here eq)))))))))) rewrite eq = reverseNegSwapCycle σ
sameOrbitSym {τ} {σ}
  (there (there (there (there (there (there (there (there
    (there (there (here eq))))))))))) rewrite eq = reverseNegCycleTwice σ
sameOrbitSym {τ} {σ}
  (there (there (there (there (there (there (there (there
    (there (there (there (here eq)))))))))))) rewrite eq =
  reverseNegSwapCycleTwice σ

------------------------------------------------------------------------
-- First-occurrence quotient under the exact raw enumeration order.
------------------------------------------------------------------------

notSameOrbit? : Lattice.LatticeTriad → Lattice.LatticeTriad → Bool
notSameOrbit? pivot candidate = not (sameOrbit? candidate pivot)

removeOrbit :
  Lattice.LatticeTriad → List Lattice.LatticeTriad →
  List Lattice.LatticeTriad
removeOrbit pivot = filterᵇ (notSameOrbit? pivot)

orbitRepresentatives :
  List Lattice.LatticeTriad → List Lattice.LatticeTriad
orbitRepresentatives [] = []
orbitRepresentatives (τ ∷ τs) =
  τ ∷ orbitRepresentatives (removeOrbit τ τs)

boolFalseFromTNot : {b : Bool} → T (not b) → b ≡ false
boolFalseFromTNot {false} _ = refl
boolFalseFromTNot {true} ()

tNotFromFalse : {b : Bool} → b ≡ false → T (not b)
tNotFromFalse {false} _ = _
tNotFromFalse {true} ()

orbitRepresentativesSubset :
  {xs : List Lattice.LatticeTriad} → {τ : Lattice.LatticeTriad} →
  τ ∈ orbitRepresentatives xs → τ ∈ xs
orbitRepresentativesSubset {[]} ()
orbitRepresentativesSubset {pivot ∷ xs} (here eq) = here eq
orbitRepresentativesSubset {pivot ∷ xs} (there τ∈reps) =
  there τ∈xs
  where
  τ∈filtered : _
  τ∈filtered = orbitRepresentativesSubset τ∈reps

  τ∈xs : _
  τ∈xs = proj₁
    (∈-filter⁻ (T? ∘ notSameOrbit? pivot) τ∈filtered)

orbitRepresentativesCover :
  {xs : List Lattice.LatticeTriad} → {τ : Lattice.LatticeTriad} →
  τ ∈ xs →
  Σ Lattice.LatticeTriad
    (λ σ → (σ ∈ orbitRepresentatives xs) ×
      Orbit.SameCanonicalTriadOrbit τ σ)
orbitRepresentativesCover {[]} ()
orbitRepresentativesCover {pivot ∷ xs} {τ} (here eq)
  rewrite eq = pivot , (here refl , sameOrbitRefl pivot)
orbitRepresentativesCover {pivot ∷ xs} {τ} (there τ∈xs)
  with sameOrbit? τ pivot
... | true = pivot , (here refl , sameOrbitSound τ pivot refl)
... | false
  with orbitRepresentativesCover
    (∈-filter⁺ (T? ∘ notSameOrbit? pivot) τ∈xs (tNotFromFalse refl))
... | σ , σ∈reps , τ~σ = σ , (there σ∈reps , τ~σ)

laterRepresentativeNotSame :
  {pivot τ : Lattice.LatticeTriad} →
  {xs : List Lattice.LatticeTriad} →
  τ ∈ orbitRepresentatives (removeOrbit pivot xs) →
  sameOrbit? τ pivot ≡ false
laterRepresentativeNotSame {pivot} {τ} {xs} τ∈reps =
  boolFalseFromTNot (proj₂ filtered)
  where
  τ∈filtered : τ ∈ removeOrbit pivot xs
  τ∈filtered = orbitRepresentativesSubset τ∈reps

  filtered :
    (τ ∈ xs) × T (notSameOrbit? pivot τ)
  filtered = ∈-filter⁻ (T? ∘ notSameOrbit? pivot) τ∈filtered

orbitRepresentativesSeparate :
  {xs : List Lattice.LatticeTriad} →
  {τ σ : Lattice.LatticeTriad} →
  τ ∈ orbitRepresentatives xs →
  σ ∈ orbitRepresentatives xs →
  Orbit.SameCanonicalTriadOrbit τ σ → τ ≡ σ
orbitRepresentativesSeparate {[]} ()
orbitRepresentativesSeparate {pivot ∷ xs}
  (here refl) (here refl) same = refl
orbitRepresentativesSeparate {pivot ∷ xs} {σ = σ}
  (here refl) (there σ∈later) same =
  ⊥-elim (false≢true contradiction)
  where
  contradiction : false ≡ true
  contradiction = trans
    (sym (laterRepresentativeNotSame σ∈later))
    (sameOrbitComplete σ pivot (sameOrbitSym same))
orbitRepresentativesSeparate {pivot ∷ xs} {τ = τ}
  (there τ∈later) (here refl) same =
  ⊥-elim (false≢true contradiction)
  where
  contradiction : false ≡ true
  contradiction = trans
    (sym (laterRepresentativeNotSame τ∈later))
    (sameOrbitComplete τ pivot same)
orbitRepresentativesSeparate {pivot ∷ xs}
  (there τ∈later) (there σ∈later) same =
  orbitRepresentativesSeparate τ∈later σ∈later same

------------------------------------------------------------------------
-- Attach exact zero-sum witnesses and inhabit the original theorem record.
------------------------------------------------------------------------

representativeTriads : Nat → List Lattice.LatticeTriad
representativeTriads R =
  orbitRepresentatives (Orbit.fullCutoffZeroSumTriads R)

representativeTriadRetained :
  (R : Nat) → (τ : Lattice.LatticeTriad) →
  τ ∈ representativeTriads R → Orbit.FullCutoffZeroSumTriad R τ
representativeTriadRetained R τ τ∈ =
  Orbit.fullCutoffZeroSumTriadsSound R τ
    (orbitRepresentativesSubset τ∈)

zeroSumFromRetained :
  {R : Nat} → {τ : Lattice.LatticeTriad} →
  Orbit.FullCutoffZeroSumTriad R τ → Lattice.zeroSum? τ ≡ true
zeroSumFromRetained (_ , (_ , (_ , zeroSum))) = zeroSum

attachRepresentatives :
  (R : Nat) → (xs : List Lattice.LatticeTriad) →
  ((τ : Lattice.LatticeTriad) → τ ∈ xs →
    Orbit.FullCutoffZeroSumTriad R τ) →
  List Energy.ZeroSumTriad
attachRepresentatives R [] retained = []
attachRepresentatives R (τ ∷ τs) retained =
  Energy.mkZeroSumTriad τ (zeroSumFromRetained (retained τ (here refl))) ∷
  attachRepresentatives R τs
    (λ σ σ∈ → retained σ (there σ∈))

canonicalZeroSumRepresentatives : Nat → List Energy.ZeroSumTriad
canonicalZeroSumRepresentatives R =
  attachRepresentatives R (representativeTriads R)
    (representativeTriadRetained R)

attachedRepresentativeRetained :
  (R : Nat) →
  (xs : List Lattice.LatticeTriad) →
  (retained : (τ : Lattice.LatticeTriad) → τ ∈ xs →
    Orbit.FullCutoffZeroSumTriad R τ) →
  (σ : Energy.ZeroSumTriad) →
  σ ∈ attachRepresentatives R xs retained →
  Orbit.FullCutoffZeroSumTriad R (Energy.triad σ)
attachedRepresentativeRetained R [] retained σ ()
attachedRepresentativeRetained R (τ ∷ τs) retained σ (here eq)
  rewrite eq = retained τ (here refl)
attachedRepresentativeRetained R (τ ∷ τs) retained σ (there σ∈) =
  attachedRepresentativeRetained R τs
    (λ ρ ρ∈ → retained ρ (there ρ∈)) σ σ∈

attachedRepresentativeForMember :
  (R : Nat) →
  (xs : List Lattice.LatticeTriad) →
  (retained : (τ : Lattice.LatticeTriad) → τ ∈ xs →
    Orbit.FullCutoffZeroSumTriad R τ) →
  (τ : Lattice.LatticeTriad) → τ ∈ xs →
  Σ Energy.ZeroSumTriad
    (λ σ → (σ ∈ attachRepresentatives R xs retained) ×
      (τ ≡ Energy.triad σ))
attachedRepresentativeForMember R [] retained τ ()
attachedRepresentativeForMember R (pivot ∷ xs) retained τ (here eq)
  rewrite eq =
  Energy.mkZeroSumTriad pivot
      (zeroSumFromRetained (retained pivot (here refl))) ,
    (here refl , refl)
attachedRepresentativeForMember R (pivot ∷ xs) retained τ (there τ∈xs)
  with attachedRepresentativeForMember R xs
    (λ ρ ρ∈ → retained ρ (there ρ∈)) τ τ∈xs
... | σ , σ∈ , τ≡σ = σ , (there σ∈ , τ≡σ)

attachedRepresentativeUnderlyingMember :
  (R : Nat) →
  (xs : List Lattice.LatticeTriad) →
  (retained : (τ : Lattice.LatticeTriad) → τ ∈ xs →
    Orbit.FullCutoffZeroSumTriad R τ) →
  (σ : Energy.ZeroSumTriad) →
  σ ∈ attachRepresentatives R xs retained →
  Energy.triad σ ∈ xs
attachedRepresentativeUnderlyingMember R [] retained σ ()
attachedRepresentativeUnderlyingMember R (τ ∷ τs) retained σ (here eq)
  rewrite eq = here refl
attachedRepresentativeUnderlyingMember R (τ ∷ τs) retained σ (there σ∈) =
  there (attachedRepresentativeUnderlyingMember R τs
    (λ ρ ρ∈ → retained ρ (there ρ∈)) σ σ∈)

fullCutoffCanonicalTriadOrbitEnumeration :
  (R : Nat) → Orbit.FullCutoffCanonicalTriadOrbitEnumeration R
fullCutoffCanonicalTriadOrbitEnumeration R = record
  { representatives = canonicalZeroSumRepresentatives R
  ; representativeRetained =
      attachedRepresentativeRetained R (representativeTriads R)
        (representativeTriadRetained R)
  ; everyRetainedTriadHasRepresentative = every
  ; representativesSeparateOrbits = separate
  }
  where
  every :
    (τ : Lattice.LatticeTriad) → Orbit.FullCutoffZeroSumTriad R τ →
    Σ Energy.ZeroSumTriad
      (λ σ → (σ ∈ canonicalZeroSumRepresentatives R) ×
        Orbit.SameCanonicalTriadOrbit τ (Energy.triad σ))
  every τ retained
    with orbitRepresentativesCover
      (Orbit.fullCutoffZeroSumTriadsComplete R τ retained)
  ... | representative , representative∈ , τ~representative
    with attachedRepresentativeForMember R (representativeTriads R)
      (representativeTriadRetained R) representative representative∈
  ... | σ , σ∈ , representative≡σ rewrite representative≡σ =
    σ , (σ∈ , τ~representative)

  separate :
    (σ ρ : Energy.ZeroSumTriad) →
    σ ∈ canonicalZeroSumRepresentatives R →
    ρ ∈ canonicalZeroSumRepresentatives R →
    Orbit.SameCanonicalTriadOrbit (Energy.triad σ) (Energy.triad ρ) →
    Energy.triad σ ≡ Energy.triad ρ
  separate σ ρ σ∈ ρ∈ same =
    orbitRepresentativesSeparate
      (attachedRepresentativeUnderlyingMember R (representativeTriads R)
        (representativeTriadRetained R) σ σ∈)
      (attachedRepresentativeUnderlyingMember R (representativeTriads R)
        (representativeTriadRetained R) ρ ρ∈)
      same

concreteCanonicalTriadOrbitEnumerationClosed : Bool
concreteCanonicalTriadOrbitEnumerationClosed = true

concreteCanonicalTriadOrbitEnumerationClosedIsTrue :
  concreteCanonicalTriadOrbitEnumerationClosed ≡ true
concreteCanonicalTriadOrbitEnumerationClosedIsTrue = refl
