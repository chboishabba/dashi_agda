module DASHI.Physics.Closure.NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Peter Constantin; Ciprian Foias.
-- Title: "Navier--Stokes Equations".
-- University of Chicago Press, 1988.
-- DOI: 10.7208/chicago/9780226115498.001.0001.
--
-- DASHI CONTRIBUTION
--
-- Construct the canonical permutation/reality quotient of the finite retained
-- zero-sum triads without `TERMINATING`, a postulate, or a hidden ordering
-- axiom.  The older quotient recursively called itself on a filtered tail and
-- therefore carried a termination pragma even though the mathematics was
-- finite.
--
-- Here recursion is strictly structural on the original input list.  The
-- recursive result is a proof-carrying `OrbitRepresentativePartition` whose
-- representatives are a subset of the processed list, cover every processed
-- triad modulo the 12-element permutation/reality orbit, and are pairwise
-- orbit-separated.
--
-- Inserting one new triad performs a decidable orbit lookup.  If an existing
-- representative is found, coverage is extended.  Otherwise the triad is
-- inserted and the lookup's negative proof establishes separation.  No
-- recursion occurs on a filtered list.
--
-- Specialising this partition to the exact full-cutoff zero-sum enumeration
-- and attaching its zero-sum proofs constructs the existing
-- `CanonicalTriadOrbitEnumeration` record.  This closes the finite
-- exhaustive/no-duplicate orbit-enumeration subleaf needed by the literal
-- triad-energy producer; identifying the actual three-leg complex Galerkin
-- energy transfer remains a separate physical theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Integer.Properties as ℤP
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNCanonicalTriadOrbitEnumeration as Orbit
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- Decidable exact equality and orbit membership.
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

triadMember? : Lattice.LatticeTriad → List Lattice.LatticeTriad → Bool
triadMember? τ [] = false
triadMember? τ (σ ∷ rest) with triad≟ τ σ
... | yes _ = true
... | no _ = triadMember? τ rest

triadMemberSound :
  (τ : Lattice.LatticeTriad) → (xs : List Lattice.LatticeTriad) →
  triadMember? τ xs ≡ true → τ ∈ xs
triadMemberSound τ [] ()
triadMemberSound τ (σ ∷ rest) proof with triad≟ τ σ
... | yes equality = here equality
... | no _ = there (triadMemberSound τ rest proof)

triadMemberComplete :
  (τ : Lattice.LatticeTriad) → (xs : List Lattice.LatticeTriad) →
  τ ∈ xs → triadMember? τ xs ≡ true
triadMemberComplete τ (σ ∷ rest) member with triad≟ τ σ
... | yes _ = refl
... | no τ≢ with member
...   | here equality = ⊥-elim (τ≢ equality)
...   | there tailMember = triadMemberComplete τ rest tailMember

sameOrbit? : Lattice.LatticeTriad → Lattice.LatticeTriad → Bool
sameOrbit? τ σ = triadMember? τ (Orbit.canonicalOrbitMembers σ)

sameOrbitSound :
  (τ σ : Lattice.LatticeTriad) →
  sameOrbit? τ σ ≡ true → Orbit.SameCanonicalTriadOrbit τ σ
sameOrbitSound τ σ =
  triadMemberSound τ (Orbit.canonicalOrbitMembers σ)

sameOrbitComplete :
  (τ σ : Lattice.LatticeTriad) →
  Orbit.SameCanonicalTriadOrbit τ σ → sameOrbit? τ σ ≡ true
sameOrbitComplete τ σ =
  triadMemberComplete τ (Orbit.canonicalOrbitMembers σ)

sameOrbitRefl :
  (τ : Lattice.LatticeTriad) → Orbit.SameCanonicalTriadOrbit τ τ
sameOrbitRefl τ = here refl

------------------------------------------------------------------------
-- Symmetry of the concrete 12-element orbit relation.
------------------------------------------------------------------------

data TriadAction : Set where
  identity swap cycle swapCycle cycleTwice swapCycleTwice : TriadAction
  negIdentity negSwap negCycle negSwapCycle
    negCycleTwice negSwapCycleTwice : TriadAction

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

modeNegInvolutive :
  (p : Lattice.LatticeMode3) → Lattice.modeNeg (Lattice.modeNeg p) ≡ p
modeNegInvolutive (Lattice.mkLatticeMode3 k₁ k₂ k₃) =
  modeExt
    (ℤP.neg-involutive k₁)
    (ℤP.neg-involutive k₂)
    (ℤP.neg-involutive k₃)

inverseActionLaw :
  (action : TriadAction) → (τ : Lattice.LatticeTriad) →
  applyAction (inverseAction action) (applyAction action τ) ≡ τ
inverseActionLaw identity (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw swap (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw cycle (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw swapCycle (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw cycleTwice (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw swapCycleTwice (Lattice.mkLatticeTriad _ _ _) = refl
inverseActionLaw negIdentity (Lattice.mkLatticeTriad left right out) =
  triadExt
    (modeNegInvolutive left)
    (modeNegInvolutive right)
    (modeNegInvolutive out)
inverseActionLaw negSwap (Lattice.mkLatticeTriad left right out) =
  triadExt
    (modeNegInvolutive left)
    (modeNegInvolutive right)
    (modeNegInvolutive out)
inverseActionLaw negCycle (Lattice.mkLatticeTriad left right out) =
  triadExt
    (modeNegInvolutive left)
    (modeNegInvolutive right)
    (modeNegInvolutive out)
inverseActionLaw negSwapCycle (Lattice.mkLatticeTriad left right out) =
  triadExt
    (modeNegInvolutive left)
    (modeNegInvolutive right)
    (modeNegInvolutive out)
inverseActionLaw negCycleTwice (Lattice.mkLatticeTriad left right out) =
  triadExt
    (modeNegInvolutive left)
    (modeNegInvolutive right)
    (modeNegInvolutive out)
inverseActionLaw negSwapCycleTwice (Lattice.mkLatticeTriad left right out) =
  triadExt
    (modeNegInvolutive left)
    (modeNegInvolutive right)
    (modeNegInvolutive out)

actionInOrbit :
  (action : TriadAction) → (τ : Lattice.LatticeTriad) →
  applyAction action τ ∈ Orbit.canonicalOrbitMembers τ
actionInOrbit identity τ = here refl
actionInOrbit swap τ = there (here refl)
actionInOrbit cycle τ = there (there (here refl))
actionInOrbit swapCycle τ = there (there (there (here refl)))
actionInOrbit cycleTwice τ = there (there (there (there (here refl))))
actionInOrbit swapCycleTwice τ =
  there (there (there (there (there (here refl)))))
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
  Σ TriadAction (λ action → τ ≡ applyAction action σ)
memberToAction τ σ (here equality) = identity , equality
memberToAction τ σ (there (here equality)) = swap , equality
memberToAction τ σ (there (there (here equality))) = cycle , equality
memberToAction τ σ (there (there (there (here equality)))) =
  swapCycle , equality
memberToAction τ σ (there (there (there (there (here equality))))) =
  cycleTwice , equality
memberToAction τ σ
  (there (there (there (there (there (here equality)))))) =
  swapCycleTwice , equality
memberToAction τ σ
  (there (there (there (there (there (there (here equality))))))) =
  negIdentity , equality
memberToAction τ σ
  (there (there (there (there (there (there (there (here equality)))))))) =
  negSwap , equality
memberToAction τ σ
  (there (there (there (there (there (there (there (there (here equality))))))))) =
  negCycle , equality
memberToAction τ σ
  (there (there (there (there (there (there (there (there (there (here equality)))))))))) =
  negSwapCycle , equality
memberToAction τ σ
  (there (there (there (there (there (there (there (there (there (there (here equality))))))))))) =
  negCycleTwice , equality
memberToAction τ σ
  (there (there (there (there (there (there (there (there (there (there (there (here equality)))))))))))) =
  negSwapCycleTwice , equality

sameOrbitSym :
  {τ σ : Lattice.LatticeTriad} →
  Orbit.SameCanonicalTriadOrbit τ σ →
  Orbit.SameCanonicalTriadOrbit σ τ
sameOrbitSym {τ} {σ} same
  with memberToAction τ σ same
... | action , equality =
  subst
    (λ selected → σ ∈ Orbit.canonicalOrbitMembers selected)
    (sym equality)
    (subst
      (λ selected →
        selected ∈ Orbit.canonicalOrbitMembers (applyAction action σ))
      (inverseActionLaw action σ)
      (actionInOrbit
        (inverseAction action)
        (applyAction action σ)))

------------------------------------------------------------------------
-- Decidable lookup in an already-separated representative list.
------------------------------------------------------------------------

data OrbitLookup
    (candidate : Lattice.LatticeTriad) :
    List Lattice.LatticeTriad → Set where
  orbit-hit :
    ∀ {representatives} (representative : Lattice.LatticeTriad) →
    representative ∈ representatives →
    Orbit.SameCanonicalTriadOrbit candidate representative →
    OrbitLookup candidate representatives

  orbit-miss :
    ∀ {representatives} →
    (∀ representative → representative ∈ representatives →
      Orbit.SameCanonicalTriadOrbit candidate representative → ⊥) →
    OrbitLookup candidate representatives

false≢true : false ≡ true → ⊥
false≢true ()

lookupOrbit :
  (candidate : Lattice.LatticeTriad) →
  (representatives : List Lattice.LatticeTriad) →
  OrbitLookup candidate representatives
lookupOrbit candidate [] = orbit-miss (λ representative () same)
lookupOrbit candidate (head ∷ tail)
  with sameOrbit? candidate head in orbitResult
... | true =
  orbit-hit head (here refl)
    (sameOrbitSound candidate head orbitResult)
... | false with lookupOrbit candidate tail
...   | orbit-hit representative member same =
      orbit-hit representative (there member) same
...   | orbit-miss tailMiss =
      orbit-miss miss
      where
      miss :
        ∀ representative → representative ∈ head ∷ tail →
        Orbit.SameCanonicalTriadOrbit candidate representative → ⊥
      miss representative (here equality) same =
        false≢true
          (trans
            (sym orbitResult)
            (sameOrbitComplete candidate head
              (subst
                (Orbit.SameCanonicalTriadOrbit candidate)
                equality same)))
      miss representative (there member) same =
        tailMiss representative member same

------------------------------------------------------------------------
-- Structural proof-carrying partition.
------------------------------------------------------------------------

record OrbitRepresentativePartition
    (source : List Lattice.LatticeTriad) : Set where
  constructor orbit-representative-partition
  field
    representatives : List Lattice.LatticeTriad

    representativeSubset :
      ∀ representative → representative ∈ representatives →
      representative ∈ source

    cover :
      ∀ triad → triad ∈ source →
      Σ Lattice.LatticeTriad
        (λ representative →
          (representative ∈ representatives) ×
          Orbit.SameCanonicalTriadOrbit triad representative)

    separate :
      ∀ left right →
      left ∈ representatives →
      right ∈ representatives →
      Orbit.SameCanonicalTriadOrbit left right →
      left ≡ right

open OrbitRepresentativePartition public

insertHead :
  (head : Lattice.LatticeTriad) →
  {tail : List Lattice.LatticeTriad} →
  OrbitRepresentativePartition tail →
  OrbitRepresentativePartition (head ∷ tail)
insertHead head {tail} partition
  with lookupOrbit head (representatives partition)
... | orbit-hit representative representativeMember same =
  orbit-representative-partition
    (representatives partition)
    (λ selected member →
      there (representativeSubset partition selected member))
    coverHeadOrTail
    (separate partition)
  where
  coverHeadOrTail :
    ∀ triad → triad ∈ head ∷ tail →
    Σ Lattice.LatticeTriad
      (λ selected →
        (selected ∈ representatives partition) ×
        Orbit.SameCanonicalTriadOrbit triad selected)
  coverHeadOrTail triad (here equality) =
    representative ,
      (representativeMember ,
       subst
         (λ selected →
           Orbit.SameCanonicalTriadOrbit selected representative)
         (sym equality)
         same)
  coverHeadOrTail triad (there member) =
    cover partition triad member

... | orbit-miss miss =
  orbit-representative-partition
    (head ∷ representatives partition)
    subsetHeadOrTail
    coverHeadOrTail
    separateHeadOrTail
  where
  subsetHeadOrTail :
    ∀ representative →
    representative ∈ head ∷ representatives partition →
    representative ∈ head ∷ tail
  subsetHeadOrTail representative (here equality) = here equality
  subsetHeadOrTail representative (there member) =
    there (representativeSubset partition representative member)

  coverHeadOrTail :
    ∀ triad → triad ∈ head ∷ tail →
    Σ Lattice.LatticeTriad
      (λ representative →
        (representative ∈ head ∷ representatives partition) ×
        Orbit.SameCanonicalTriadOrbit triad representative)
  coverHeadOrTail triad (here equality) =
    head ,
      (here refl ,
       subst
         (λ selected → Orbit.SameCanonicalTriadOrbit selected head)
         (sym equality)
         (sameOrbitRefl head))
  coverHeadOrTail triad (there member)
    with cover partition triad member
  ... | representative , representativeMember , same =
      representative , (there representativeMember , same)

  separateHeadOrTail :
    ∀ left right →
    left ∈ head ∷ representatives partition →
    right ∈ head ∷ representatives partition →
    Orbit.SameCanonicalTriadOrbit left right →
    left ≡ right
  separateHeadOrTail left right (here leftEq) (here rightEq) same =
    trans leftEq (sym rightEq)
  separateHeadOrTail left right (here leftEq) (there rightMember) same =
    ⊥-elim
      (miss right rightMember
        (subst
          (λ selected → Orbit.SameCanonicalTriadOrbit selected right)
          leftEq same))
  separateHeadOrTail left right (there leftMember) (here rightEq) same =
    ⊥-elim
      (miss left leftMember
        (sameOrbitSym
          (subst
            (Orbit.SameCanonicalTriadOrbit left)
            rightEq same)))
  separateHeadOrTail left right
      (there leftMember) (there rightMember) same =
    separate partition left right leftMember rightMember same

partitionTriads :
  (source : List Lattice.LatticeTriad) →
  OrbitRepresentativePartition source
partitionTriads [] =
  orbit-representative-partition
    []
    (λ representative ())
    (λ triad ())
    (λ left right ())
partitionTriads (head ∷ tail) =
  insertHead head (partitionTriads tail)

------------------------------------------------------------------------
-- Specialise to the full symmetric cutoff and attach zero-sum evidence.
------------------------------------------------------------------------

fullCutoffPartition :
  (cutoff : Nat) →
  OrbitRepresentativePartition (Orbit.fullCutoffZeroSumTriads cutoff)
fullCutoffPartition cutoff =
  partitionTriads (Orbit.fullCutoffZeroSumTriads cutoff)

zeroSumFromRetained :
  ∀ {cutoff triad} →
  Orbit.FullCutoffZeroSumTriad cutoff triad →
  Lattice.zeroSum? triad ≡ true
zeroSumFromRetained (_ , (_ , (_ , zeroSum))) = zeroSum

representativeRetained :
  (cutoff : Nat) →
  (triad : Lattice.LatticeTriad) →
  triad ∈ representatives (fullCutoffPartition cutoff) →
  Orbit.FullCutoffZeroSumTriad cutoff triad
representativeRetained cutoff triad member =
  Orbit.fullCutoffZeroSumTriadsSound cutoff triad
    (representativeSubset
      (fullCutoffPartition cutoff) triad member)

attachZeroSum :
  (cutoff : Nat) →
  (triads : List Lattice.LatticeTriad) →
  (∀ triad → triad ∈ triads → Orbit.FullCutoffZeroSumTriad cutoff triad) →
  List Energy.ZeroSumTriad
attachZeroSum cutoff [] retained = []
attachZeroSum cutoff (triad ∷ rest) retained =
  Energy.mkZeroSumTriad triad
    (zeroSumFromRetained
      (retained triad (here refl)))
  ∷ attachZeroSum cutoff rest
      (λ selected member → retained selected (there member))

safeZeroSumRepresentatives : Nat → List Energy.ZeroSumTriad
safeZeroSumRepresentatives cutoff =
  attachZeroSum cutoff
    (representatives (fullCutoffPartition cutoff))
    (representativeRetained cutoff)

attachedRetained :
  (cutoff : Nat) →
  (triads : List Lattice.LatticeTriad) →
  (retained : ∀ triad → triad ∈ triads →
    Orbit.FullCutoffZeroSumTriad cutoff triad) →
  ∀ representative →
  representative ∈ attachZeroSum cutoff triads retained →
  Orbit.FullCutoffZeroSumTriad cutoff (Energy.triad representative)
attachedRetained cutoff [] retained representative ()
attachedRetained cutoff (triad ∷ rest) retained representative
    (here equality) =
  subst
    (λ selected → Orbit.FullCutoffZeroSumTriad cutoff (Energy.triad selected))
    (sym equality)
    (retained triad (here refl))
attachedRetained cutoff (triad ∷ rest) retained representative
    (there member) =
  attachedRetained cutoff rest
    (λ selected selectedMember →
      retained selected (there selectedMember))
    representative member

attachedUnderlyingMember :
  (cutoff : Nat) →
  (triads : List Lattice.LatticeTriad) →
  (retained : ∀ triad → triad ∈ triads →
    Orbit.FullCutoffZeroSumTriad cutoff triad) →
  ∀ representative →
  representative ∈ attachZeroSum cutoff triads retained →
  Energy.triad representative ∈ triads
attachedUnderlyingMember cutoff [] retained representative ()
attachedUnderlyingMember cutoff (triad ∷ rest) retained representative
    (here equality) =
  subst
    (λ selected → selected ∈ triad ∷ rest)
    (sym (cong Energy.triad equality))
    (here refl)
attachedUnderlyingMember cutoff (triad ∷ rest) retained representative
    (there member) =
  there
    (attachedUnderlyingMember cutoff rest
      (λ selected selectedMember →
        retained selected (there selectedMember))
      representative member)

attachedForUnderlyingMember :
  (cutoff : Nat) →
  (triads : List Lattice.LatticeTriad) →
  (retained : ∀ triad → triad ∈ triads →
    Orbit.FullCutoffZeroSumTriad cutoff triad) →
  ∀ triad → triad ∈ triads →
  Σ Energy.ZeroSumTriad
    (λ representative →
      (representative ∈ attachZeroSum cutoff triads retained) ×
      (triad ≡ Energy.triad representative))
attachedForUnderlyingMember cutoff [] retained triad ()
attachedForUnderlyingMember cutoff (head ∷ tail) retained triad
    (here equality) =
  Energy.mkZeroSumTriad head
      (zeroSumFromRetained (retained head (here refl))) ,
    (here refl , equality)
attachedForUnderlyingMember cutoff (head ∷ tail) retained triad
    (there member)
  with attachedForUnderlyingMember cutoff tail
    (λ selected selectedMember →
      retained selected (there selectedMember))
    triad member
... | representative , representativeMember , underlyingEq =
  representative , (there representativeMember , underlyingEq)

safeFullCutoffCanonicalTriadOrbitEnumeration :
  (cutoff : Nat) → Orbit.FullCutoffCanonicalTriadOrbitEnumeration cutoff
safeFullCutoffCanonicalTriadOrbitEnumeration cutoff = record
  { Orbit.CanonicalTriadOrbitEnumeration.representatives =
      safeZeroSumRepresentatives cutoff
  ; Orbit.CanonicalTriadOrbitEnumeration.representativeRetained =
      attachedRetained cutoff
        (representatives (fullCutoffPartition cutoff))
        (representativeRetained cutoff)
  ; Orbit.CanonicalTriadOrbitEnumeration.everyRetainedTriadHasRepresentative =
      every
  ; Orbit.CanonicalTriadOrbitEnumeration.representativesSeparateOrbits =
      separateAttached
  }
  where
  partition = fullCutoffPartition cutoff
  rawRepresentatives = representatives partition
  retained = representativeRetained cutoff

  every :
    (triad : Lattice.LatticeTriad) →
    Orbit.FullCutoffZeroSumTriad cutoff triad →
    Σ Energy.ZeroSumTriad
      (λ representative →
        (representative ∈ safeZeroSumRepresentatives cutoff) ×
        Orbit.SameCanonicalTriadOrbit
          triad (Energy.triad representative))
  every triad retainedTriad
    with cover partition triad
      (Orbit.fullCutoffZeroSumTriadsComplete cutoff triad retainedTriad)
  ... | rawRepresentative , rawMember , same
    with attachedForUnderlyingMember cutoff rawRepresentatives retained
      rawRepresentative rawMember
  ... | representative , attachedMember , rawEq =
      representative ,
        (attachedMember ,
         subst
           (Orbit.SameCanonicalTriadOrbit triad)
           rawEq same)

  separateAttached :
    (left right : Energy.ZeroSumTriad) →
    left ∈ safeZeroSumRepresentatives cutoff →
    right ∈ safeZeroSumRepresentatives cutoff →
    Orbit.SameCanonicalTriadOrbit
      (Energy.triad left) (Energy.triad right) →
    Energy.triad left ≡ Energy.triad right
  separateAttached left right leftMember rightMember same =
    separate partition
      (Energy.triad left) (Energy.triad right)
      (attachedUnderlyingMember cutoff rawRepresentatives retained
        left leftMember)
      (attachedUnderlyingMember cutoff rawRepresentatives retained
        right rightMember)
      same

safeCanonicalTriadOrbitQuotientClosed : Bool
safeCanonicalTriadOrbitQuotientClosed = true

literalComplexThreeLegEnergyTransferConstructed : Bool
literalComplexThreeLegEnergyTransferConstructed = false

safeCanonicalTriadOrbitQuotientClosedIsTrue :
  safeCanonicalTriadOrbitQuotientClosed ≡ true
safeCanonicalTriadOrbitQuotientClosedIsTrue = refl

literalComplexThreeLegEnergyTransferConstructedIsFalse :
  literalComplexThreeLegEnergyTransferConstructed ≡ false
literalComplexThreeLegEnergyTransferConstructedIsFalse = refl
