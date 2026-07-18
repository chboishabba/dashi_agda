module DASHI.Physics.Closure.NSTriadKNCanonicalTriadOrbitQuotient where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Bool.Base using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
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
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNCanonicalTriadOrbitEnumeration as Orbit
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

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

modeNegInvolutive :
  (p : Lattice.LatticeMode3) → Lattice.modeNeg (Lattice.modeNeg p) ≡ p
modeNegInvolutive (Lattice.mkLatticeMode3 k₁ k₂ k₃) =
  modeExt (ℤP.neg-involutive k₁)
    (ℤP.neg-involutive k₂) (ℤP.neg-involutive k₃)

data TriadAction : Set where
  identity swap cycle swapCycle cycleTwice swapCycleTwice : TriadAction
  negIdentity negSwap negCycle negSwapCycle negCycleTwice negSwapCycleTwice : TriadAction

applyAction : TriadAction → Lattice.LatticeTriad → Lattice.LatticeTriad
applyAction identity τ = τ
applyAction swap τ = Lattice.triadSwap τ
applyAction cycle τ = Lattice.triadCycle τ
applyAction swapCycle τ = Lattice.triadSwap (Lattice.triadCycle τ)
applyAction cycleTwice τ = Orbit.triadCycleTwice τ
applyAction swapCycleTwice τ = Lattice.triadSwap (Orbit.triadCycleTwice τ)
applyAction negIdentity τ = Lattice.triadNeg τ
applyAction negSwap τ = Lattice.triadNeg (Lattice.triadSwap τ)
applyAction negCycle τ = Lattice.triadNeg (Lattice.triadCycle τ)
applyAction negSwapCycle τ =
  Lattice.triadNeg (Lattice.triadSwap (Lattice.triadCycle τ))
applyAction negCycleTwice τ = Lattice.triadNeg (Orbit.triadCycleTwice τ)
applyAction negSwapCycleTwice τ =
  Lattice.triadNeg (Lattice.triadSwap (Orbit.triadCycleTwice τ))

inverseAction : TriadAction → TriadAction
inverseAction identity = identity
inverseAction swap = swap
inverseAction cycle = cycleTwice
inverseAction swapCycle = swapCycle
inverseAction cycleTwice = cycle
inverseAction swapCycleTwice = swapCycleTwice
inverseAction negIdentity = negIdentity
inverseAction negSwap = negSwap
inverseAction negCycle = negCycleTwice
inverseAction negSwapCycle = negSwapCycle
inverseAction negCycleTwice = negCycle
inverseAction negSwapCycleTwice = negSwapCycleTwice

inverseActionLaw :
  (a : TriadAction) → (τ : Lattice.LatticeTriad) →
  applyAction (inverseAction a) (applyAction a τ) ≡ τ
inverseActionLaw identity (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw swap (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw cycle (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw swapCycle (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw cycleTwice (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw swapCycleTwice (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw negIdentity (Lattice.mkLatticeTriad left right out) =
  triadExt (modeNegInvolutive left) (modeNegInvolutive right)
    (modeNegInvolutive out)
inverseActionLaw negSwap (Lattice.mkLatticeTriad left right out) =
  triadExt (modeNegInvolutive left) (modeNegInvolutive right)
    (modeNegInvolutive out)
inverseActionLaw negCycle (Lattice.mkLatticeTriad left right out) =
  triadExt (modeNegInvolutive left) (modeNegInvolutive right)
    (modeNegInvolutive out)
inverseActionLaw negSwapCycle (Lattice.mkLatticeTriad left right out) =
  triadExt (modeNegInvolutive left) (modeNegInvolutive right)
    (modeNegInvolutive out)
inverseActionLaw negCycleTwice (Lattice.mkLatticeTriad left right out) =
  triadExt (modeNegInvolutive left) (modeNegInvolutive right)
    (modeNegInvolutive out)
inverseActionLaw negSwapCycleTwice (Lattice.mkLatticeTriad left right out) =
  triadExt (modeNegInvolutive left) (modeNegInvolutive right)
    (modeNegInvolutive out)

actionInOrbit :
  (a : TriadAction) → (τ : Lattice.LatticeTriad) →
  applyAction a τ ∈ Orbit.canonicalOrbitMembers τ
actionInOrbit identity τ = here refl
actionInOrbit swap τ = there (here refl)
actionInOrbit cycle τ = there (there (here refl))
actionInOrbit swapCycle τ = there (there (there (here refl)))
actionInOrbit cycleTwice τ = there (there (there (there (here refl))))
actionInOrbit swapCycleTwice τ = there (there (there (there (there (here refl)))))
actionInOrbit negIdentity τ =
  there (there (there (there (there (there (here refl))))))
actionInOrbit negSwap τ =
  there (there (there (there (there (there (there (here refl)))))))
actionInOrbit negCycle τ =
  there (there (there (there (there (there (there (there (here refl))))))))
actionInOrbit negSwapCycle τ =
  there (there (there (there (there (there (there (there (there (here refl)))))))))
actionInOrbit negCycleTwice τ =
  there (there (there (there (there (there (there (there (there (there (here refl))))))))))
actionInOrbit negSwapCycleTwice τ =
  there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))

memberToAction :
  (τ σ : Lattice.LatticeTriad) →
  τ ∈ Orbit.canonicalOrbitMembers σ →
  Σ TriadAction (λ a → τ ≡ applyAction a σ)
memberToAction τ σ (here eq) = identity , eq
memberToAction τ σ (there (here eq)) = swap , eq
memberToAction τ σ (there (there (here eq))) = cycle , eq
memberToAction τ σ (there (there (there (here eq)))) = swapCycle , eq
memberToAction τ σ (there (there (there (there (here eq))))) = cycleTwice , eq
memberToAction τ σ
  (there (there (there (there (there (here eq)))))) = swapCycleTwice , eq
memberToAction τ σ
  (there (there (there (there (there (there (here eq))))))) = negIdentity , eq
memberToAction τ σ
  (there (there (there (there (there (there (there (here eq)))))))) = negSwap , eq
memberToAction τ σ
  (there (there (there (there (there (there (there (there (here eq))))))))) = negCycle , eq
memberToAction τ σ
  (there (there (there (there (there (there (there (there (there (here eq)))))))))) = negSwapCycle , eq
memberToAction τ σ
  (there (there (there (there (there (there (there (there (there (there (here eq))))))))))) = negCycleTwice , eq
memberToAction τ σ
  (there (there (there (there (there (there (there (there (there (there (there (here eq)))))))))))) = negSwapCycleTwice , eq

triadMember? : Lattice.LatticeTriad → List Lattice.LatticeTriad → Bool
triadMember? τ [] = false
triadMember? τ (σ ∷ σs) with triad≟ τ σ
... | yes _ = true
... | no _ = triadMember? τ σs

triadMemberSound :
  (τ : Lattice.LatticeTriad) → (xs : List Lattice.LatticeTriad) →
  triadMember? τ xs ≡ true → τ ∈ xs
triadMemberSound τ [] ()
triadMemberSound τ (σ ∷ σs) member with triad≟ τ σ
... | yes τ≡σ = here τ≡σ
... | no _ = there (triadMemberSound τ σs member)

triadMemberComplete :
  (τ : Lattice.LatticeTriad) → (xs : List Lattice.LatticeTriad) →
  τ ∈ xs → triadMember? τ xs ≡ true
triadMemberComplete τ (σ ∷ σs) member with triad≟ τ σ
... | yes _ = refl
... | no τ≢ with member
...   | here τ≡σ = ⊥-elim (τ≢ τ≡σ)
...   | there τ∈σs = triadMemberComplete τ σs τ∈σs

sameOrbit? : Lattice.LatticeTriad → Lattice.LatticeTriad → Bool
sameOrbit? τ σ = triadMember? τ (Orbit.canonicalOrbitMembers σ)

sameOrbitSound :
  (τ σ : Lattice.LatticeTriad) → sameOrbit? τ σ ≡ true →
  Orbit.SameCanonicalTriadOrbit τ σ
sameOrbitSound τ σ = triadMemberSound τ (Orbit.canonicalOrbitMembers σ)

sameOrbitComplete :
  (τ σ : Lattice.LatticeTriad) → Orbit.SameCanonicalTriadOrbit τ σ →
  sameOrbit? τ σ ≡ true
sameOrbitComplete τ σ = triadMemberComplete τ (Orbit.canonicalOrbitMembers σ)

sameOrbitRefl :
  (τ : Lattice.LatticeTriad) → Orbit.SameCanonicalTriadOrbit τ τ
sameOrbitRefl τ = actionInOrbit identity τ

sameOrbitSym :
  {τ σ : Lattice.LatticeTriad} →
  Orbit.SameCanonicalTriadOrbit τ σ → Orbit.SameCanonicalTriadOrbit σ τ
sameOrbitSym {τ} {σ} same with memberToAction τ σ same
... | a , eq = subst
  (λ x → σ ∈ Orbit.canonicalOrbitMembers x)
  (sym eq)
  (subst
    (λ x → x ∈ Orbit.canonicalOrbitMembers (applyAction a σ))
    (inverseActionLaw a σ)
    (actionInOrbit (inverseAction a) (applyAction a σ)))

notSameOrbit? : Lattice.LatticeTriad → Lattice.LatticeTriad → Bool
notSameOrbit? pivot candidate = not (sameOrbit? candidate pivot)

removeOrbit : Lattice.LatticeTriad → List Lattice.LatticeTriad → List Lattice.LatticeTriad
removeOrbit pivot = filterᵇ (notSameOrbit? pivot)

orbitRepresentatives : List Lattice.LatticeTriad → List Lattice.LatticeTriad
{-# TERMINATING #-}
orbitRepresentatives [] = []
orbitRepresentatives (τ ∷ τs) = τ ∷ orbitRepresentatives (removeOrbit τ τs)

false≢true : false ≡ true → ⊥
false≢true ()

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
  there (proj₁ (∈-filter⁻ (T? ∘ notSameOrbit? pivot)
    (orbitRepresentativesSubset τ∈reps)))

orbitRepresentativesCover :
  {xs : List Lattice.LatticeTriad} → {τ : Lattice.LatticeTriad} →
  τ ∈ xs →
  Σ Lattice.LatticeTriad
    (λ σ → (σ ∈ orbitRepresentatives xs) ×
      Orbit.SameCanonicalTriadOrbit τ σ)
{-# TERMINATING #-}
orbitRepresentativesCover {[]} ()
orbitRepresentativesCover {pivot ∷ xs} {τ} (here eq)
  rewrite eq = pivot , (here refl , sameOrbitRefl pivot)
orbitRepresentativesCover {pivot ∷ xs} {τ} (there τ∈xs)
  with sameOrbit? τ pivot in orbitResult
... | true = pivot , (here refl , sameOrbitSound τ pivot orbitResult)
... | false
  with orbitRepresentativesCover
    (∈-filter⁺ (T? ∘ notSameOrbit? pivot) τ∈xs
      (tNotFromFalse orbitResult))
... | σ , σ∈ , τ~σ = σ , (there σ∈ , τ~σ)

laterRepresentativeNotSame :
  {pivot τ : Lattice.LatticeTriad} →
  {xs : List Lattice.LatticeTriad} →
  τ ∈ orbitRepresentatives (removeOrbit pivot xs) →
  sameOrbit? τ pivot ≡ false
laterRepresentativeNotSame {pivot} {τ} {xs} τ∈reps =
  boolFalseFromTNot
    (proj₂ (∈-filter⁻ (T? ∘ notSameOrbit? pivot)
      (orbitRepresentativesSubset τ∈reps)))

orbitRepresentativesSeparate :
  {xs : List Lattice.LatticeTriad} →
  {τ σ : Lattice.LatticeTriad} →
  τ ∈ orbitRepresentatives xs →
  σ ∈ orbitRepresentatives xs →
  Orbit.SameCanonicalTriadOrbit τ σ → τ ≡ σ
orbitRepresentativesSeparate {[]} ()
orbitRepresentativesSeparate {pivot ∷ xs} (here refl) (here refl) same = refl
orbitRepresentativesSeparate {pivot ∷ xs} {σ = σ}
  (here refl) (there σ∈later) same =
  ⊥-elim (false≢true
    (trans (sym (laterRepresentativeNotSame σ∈later))
      (sameOrbitComplete σ pivot (sameOrbitSym same))))
orbitRepresentativesSeparate {pivot ∷ xs} {τ = τ}
  (there τ∈later) (here refl) same =
  ⊥-elim (false≢true
    (trans (sym (laterRepresentativeNotSame τ∈later))
      (sameOrbitComplete τ pivot same)))
orbitRepresentativesSeparate {pivot ∷ xs}
  (there τ∈later) (there σ∈later) same =
  orbitRepresentativesSeparate τ∈later σ∈later same

representativeTriads : Nat → List Lattice.LatticeTriad
representativeTriads R = orbitRepresentatives (Orbit.fullCutoffZeroSumTriads R)

representativeTriadRetained :
  (R : Nat) → (τ : Lattice.LatticeTriad) →
  τ ∈ representativeTriads R → Orbit.FullCutoffZeroSumTriad R τ
representativeTriadRetained R τ τ∈ =
  Orbit.fullCutoffZeroSumTriadsSound R τ (orbitRepresentativesSubset τ∈)

zeroSumFromRetained :
  {R : Nat} → {τ : Lattice.LatticeTriad} →
  Orbit.FullCutoffZeroSumTriad R τ → Lattice.zeroSum? τ ≡ true
zeroSumFromRetained (_ , (_ , (_ , zeroSum))) = zeroSum

attachRepresentatives :
  (R : Nat) → (xs : List Lattice.LatticeTriad) →
  ((τ : Lattice.LatticeTriad) → τ ∈ xs → Orbit.FullCutoffZeroSumTriad R τ) →
  List Energy.ZeroSumTriad
attachRepresentatives R [] retained = []
attachRepresentatives R (τ ∷ τs) retained =
  Energy.mkZeroSumTriad τ (zeroSumFromRetained (retained τ (here refl))) ∷
  attachRepresentatives R τs (λ σ σ∈ → retained σ (there σ∈))

canonicalZeroSumRepresentatives : Nat → List Energy.ZeroSumTriad
canonicalZeroSumRepresentatives R =
  attachRepresentatives R (representativeTriads R) (representativeTriadRetained R)

attachedRepresentativeRetained :
  (R : Nat) → (xs : List Lattice.LatticeTriad) →
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
  (R : Nat) → (xs : List Lattice.LatticeTriad) →
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
  (R : Nat) → (xs : List Lattice.LatticeTriad) →
  (retained : (τ : Lattice.LatticeTriad) → τ ∈ xs →
    Orbit.FullCutoffZeroSumTriad R τ) →
  (σ : Energy.ZeroSumTriad) →
  σ ∈ attachRepresentatives R xs retained → Energy.triad σ ∈ xs
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

canonicalTriadOrbitQuotientClosed : Bool
canonicalTriadOrbitQuotientClosed = true

canonicalTriadOrbitQuotientClosedIsTrue :
  canonicalTriadOrbitQuotientClosed ≡ true
canonicalTriadOrbitQuotientClosedIsTrue = refl