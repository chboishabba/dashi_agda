module DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Complete the finite combinatorial leaf left by the labelled output-fibre
-- conjugation theorem.  The proof respects the repository's proof-bearing
-- triad representation rather than assuming resonance proofs are definitionally
-- identical.
--
-- We first prove every physical incidence is equal to the canonical `pairTriad`
-- determined by its p/q labels.  This yields extensionality by p/q and makes
-- the canonical conjugation map
--
--   (p,q,k) |-> pairTriad(-p,-q)
--
-- an involutive injection.  Custom no-duplicate certificates from the literal
-- physical enumeration are transported to the standard-library `Unique`
-- predicate.
--
-- The final promotion from extensional membership equivalence to a list
-- permutation is constructive and proof-relevant: one chosen membership proof
-- removes exactly one target occurrence, the removal is itself related to the
-- original list by the inductive permutation constructors, and uniqueness
-- proves that all other elements survive.  This avoids the WithK membership
-- irrelevance route entirely.
--
-- The result is the exact reindexing theorem
--
--   map canonicalConjugate (outputFiber k)
--     ↭ outputFiber (-k).
--
-- No ordering convention, K axiom, proof-irrelevance principle, `funext`, or
-- termination waiver is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
import Data.List.Relation.Unary.Unique.Propositional as Unique
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermP
open import Data.List.Relation.Unary.Any as Any using ()
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using
  (_≢_; cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberConjugationRound35Exact as Fibre

------------------------------------------------------------------------
-- Canonicality and extensionality of proof-bearing physical incidences.
------------------------------------------------------------------------

pairExt :
  ∀ {a b c d : Z3.FourierMode} →
  a ≡ c → b ≡ d → Cube.pair a b ≡ Cube.pair c d
pairExt refl refl = refl

physicalIncidenceCanonical :
  (τ : Physical.PhysicalTriadIncidence) →
  Physical.pairTriad (Physical.triadInputPair τ) ≡ τ
physicalIncidenceCanonical
  (Physical.physicalTriad p q .(Z3.addMode p q) refl) = refl

physicalIncidenceExtPQ :
  (left right : Physical.PhysicalTriadIncidence) →
  Physical.p left ≡ Physical.p right →
  Physical.q left ≡ Physical.q right →
  left ≡ right
physicalIncidenceExtPQ left right pEqual qEqual =
  trans
    (sym (physicalIncidenceCanonical left))
    (trans
      (cong Physical.pairTriad (pairExt pEqual qEqual))
      (physicalIncidenceCanonical right))

cancelNegateMode :
  ∀ {left right} →
  Z3.negateMode left ≡ Z3.negateMode right → left ≡ right
cancelNegateMode {left} {right} equality =
  trans
    (sym (Symmetry.negateModeInvolutive left))
    (trans
      (cong Z3.negateMode equality)
      (Symmetry.negateModeInvolutive right))

canonicalConjugate :
  Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence
canonicalConjugate τ =
  Physical.pairTriad
    (Cube.pair
      (Z3.negateMode (Physical.p τ))
      (Z3.negateMode (Physical.q τ)))

canonicalConjugateInjective :
  ∀ {left right} →
  canonicalConjugate left ≡ canonicalConjugate right → left ≡ right
canonicalConjugateInjective {left} {right} equality =
  physicalIncidenceExtPQ left right
    (cancelNegateMode (cong Physical.p equality))
    (cancelNegateMode (cong Physical.q equality))

canonicalConjugateInvolutive :
  ∀ τ → canonicalConjugate (canonicalConjugate τ) ≡ τ
canonicalConjugateInvolutive τ =
  physicalIncidenceExtPQ
    (canonicalConjugate (canonicalConjugate τ)) τ
    (Symmetry.negateModeInvolutive (Physical.p τ))
    (Symmetry.negateModeInvolutive (Physical.q τ))

------------------------------------------------------------------------
-- The canonical conjugate is the exact listed representative supplied by the
-- labelled-bijection theorem.
------------------------------------------------------------------------

canonicalConjugateMember :
  ∀ {cutoff output source} →
  source Cube.∈ Output.physicalOutputFiber cutoff output →
  canonicalConjugate source Cube.∈
    Output.physicalOutputFiber cutoff (Z3.negateMode output)
canonicalConjugateMember member =
  let
    witness = Fibre.conjugateFiberRepresentative member
    labels = Fibre.labelsConjugate witness

    representativeEqual :
      Fibre.representative witness ≡ canonicalConjugate _
    representativeEqual =
      physicalIncidenceExtPQ
        (Fibre.representative witness)
        (canonicalConjugate _)
        (Fibre.sameP labels)
        (Fibre.sameQ labels)
  in
  subst
    (λ selected → selected Cube.∈
      Output.physicalOutputFiber _ _)
    representativeEqual
    (Fibre.representativeMember witness)

canonicalConjugateReverseMember :
  ∀ {cutoff output source} →
  source Cube.∈
    Output.physicalOutputFiber cutoff (Z3.negateMode output) →
  canonicalConjugate source Cube.∈ Output.physicalOutputFiber cutoff output
canonicalConjugateReverseMember {cutoff} {output} {source} member =
  let
    first :
      canonicalConjugate source Cube.∈
        Output.physicalOutputFiber cutoff
          (Z3.negateMode (Z3.negateMode output))
    first = canonicalConjugateMember member
  in
  subst
    (λ selectedOutput → canonicalConjugate source Cube.∈
      Output.physicalOutputFiber cutoff selectedOutput)
    (Symmetry.negateModeInvolutive output)
    first

------------------------------------------------------------------------
-- Convert the repository's structural no-duplicate witness to stdlib Unique.
------------------------------------------------------------------------

cubeMemberToStd :
  ∀ {A : Set} {x : A} {xs : List A} →
  x Cube.∈ xs → x ∈ xs
cubeMemberToStd (Cube.here equality) = Any.here equality
cubeMemberToStd (Cube.there member) = Any.there (cubeMemberToStd member)

stdMemberToCube :
  ∀ {A : Set} {x : A} {xs : List A} →
  x ∈ xs → x Cube.∈ xs
stdMemberToCube (Any.here equality) = Cube.here equality
stdMemberToCube (Any.there member) = Cube.there (stdMemberToCube member)

freshToAll :
  ∀ {A : Set} {x : A} {xs : List A} →
  (x Cube.∈ xs → ⊥) →
  All.All (λ y → x ≢ y) xs
freshToAll {xs = []} fresh = All.[]
freshToAll {xs = y ∷ ys} fresh =
  All._∷_
    (λ equality → fresh (Cube.here equality))
    (freshToAll (λ member → fresh (Cube.there member)))

cubeNoDuplicatesToUnique :
  ∀ {A : Set} {xs : List A} →
  Cube.NoDuplicates xs → Unique.Unique xs
cubeNoDuplicatesToUnique Cube.unique[] = AllPairs.[]
cubeNoDuplicatesToUnique (Cube.unique∷ fresh rest) =
  AllPairs._∷_ (freshToAll fresh) (cubeNoDuplicatesToUnique rest)

filterOutputNoDuplicates :
  ∀ output items → Cube.NoDuplicates items →
  Cube.NoDuplicates (Output.filterOutput output items)
filterOutputNoDuplicates output [] Cube.unique[] = Cube.unique[]
filterOutputNoDuplicates output (head ∷ tail) (Cube.unique∷ fresh rest)
  with Output.modeEqual (Physical.k head) output
... | true =
  Cube.unique∷
    (λ member → fresh (Fibre.filterOutputMemberOriginal member))
    (filterOutputNoDuplicates output tail rest)
... | false = filterOutputNoDuplicates output tail rest

physicalOutputFiberUnique :
  (cutoff : Nat) (output : Z3.FourierMode) →
  Unique.Unique (Output.physicalOutputFiber cutoff output)
physicalOutputFiberUnique cutoff output =
  cubeNoDuplicatesToUnique
    (filterOutputNoDuplicates output
      (Physical.physicalTriadEnumeration cutoff)
      (Physical.physicalTriadEnumerationNoDuplicates cutoff))

mappedCanonicalConjugateUnique :
  (cutoff : Nat) (output : Z3.FourierMode) →
  Unique.Unique
    (map canonicalConjugate (Output.physicalOutputFiber cutoff output))
mappedCanonicalConjugateUnique cutoff output =
  UniqueP.map⁺ canonicalConjugateInjective
    (physicalOutputFiberUnique cutoff output)

------------------------------------------------------------------------
-- Exact standard-list membership equivalence.
------------------------------------------------------------------------

mappedConjugateMemberImpliesTarget :
  ∀ {cutoff output τ} →
  τ ∈ map canonicalConjugate (Output.physicalOutputFiber cutoff output) →
  τ ∈ Output.physicalOutputFiber cutoff (Z3.negateMode output)
mappedConjugateMemberImpliesTarget {cutoff} {output} {τ} member
  with ∈-map⁻ canonicalConjugate member
... | source , sourceMember , sourceMapsToτ =
  subst
    (λ selected → selected ∈
      Output.physicalOutputFiber cutoff (Z3.negateMode output))
    sourceMapsToτ
    (cubeMemberToStd
      (canonicalConjugateMember (stdMemberToCube sourceMember)))

targetMemberImpliesMappedConjugate :
  ∀ {cutoff output τ} →
  τ ∈ Output.physicalOutputFiber cutoff (Z3.negateMode output) →
  τ ∈ map canonicalConjugate (Output.physicalOutputFiber cutoff output)
targetMemberImpliesMappedConjugate {cutoff} {output} {τ} member =
  let
    sourceCube :
      canonicalConjugate τ Cube.∈ Output.physicalOutputFiber cutoff output
    sourceCube = canonicalConjugateReverseMember (stdMemberToCube member)

    mapped :
      canonicalConjugate (canonicalConjugate τ)
        ∈ map canonicalConjugate (Output.physicalOutputFiber cutoff output)
    mapped = ∈-map⁺ canonicalConjugate (cubeMemberToStd sourceCube)
  in
  subst
    (λ selected → selected ∈
      map canonicalConjugate (Output.physicalOutputFiber cutoff output))
    (canonicalConjugateInvolutive τ)
    mapped

------------------------------------------------------------------------
-- K-free promotion: remove one concrete occurrence and recurse on the unique
-- remainder.  Every step is indexed by the actual membership witness.
------------------------------------------------------------------------

removeAt :
  ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → List A
removeAt {xs = _ ∷ xs} (Any.here refl) = xs
removeAt {xs = y ∷ ys} (Any.there member) = y ∷ removeAt member

removeAtPermutation :
  ∀ {A : Set} {x : A} {xs : List A}
    (selected : x ∈ xs) →
  xs Perm.↭ (x ∷ removeAt selected)
removeAtPermutation (Any.here refl) = Perm.refl
removeAtPermutation {x = x} {xs = y ∷ ys} (Any.there selected) =
  Perm.trans
    (Perm.prep y (removeAtPermutation selected))
    (Perm.swap y x Perm.refl)

removeAtMemberOriginal :
  ∀ {A : Set} {x z : A} {xs : List A}
    (selected : x ∈ xs) →
  z ∈ removeAt selected → z ∈ xs
removeAtMemberOriginal (Any.here refl) member = Any.there member
removeAtMemberOriginal (Any.there selected) (Any.here equality) =
  Any.here equality
removeAtMemberOriginal (Any.there selected) (Any.there member) =
  Any.there (removeAtMemberOriginal selected member)

otherMemberSurvivesRemoval :
  ∀ {A : Set} {x z : A} {xs : List A}
    (selected : x ∈ xs) →
  z ∈ xs → z ≢ x → z ∈ removeAt selected
otherMemberSurvivesRemoval (Any.here refl) (Any.here equality) different =
  ⊥-elim (different equality)
otherMemberSurvivesRemoval (Any.here refl) (Any.there member) different =
  member
otherMemberSurvivesRemoval
    (Any.there selected) (Any.here equality) different =
  Any.here equality
otherMemberSurvivesRemoval
    (Any.there selected) (Any.there member) different =
  Any.there (otherMemberSurvivesRemoval selected member different)

allRemoveAt :
  ∀ {A : Set} {P : A → Set} {x : A} {xs : List A} →
  All.All P xs →
  (selected : x ∈ xs) →
  All.All P (removeAt selected)
allRemoveAt (All._∷_ px pxs) (Any.here refl) = pxs
allRemoveAt (All._∷_ px pxs) (Any.there selected) =
  All._∷_ px (allRemoveAt pxs selected)

removeAtUnique :
  ∀ {A : Set} {x : A} {xs : List A} →
  Unique.Unique xs →
  (selected : x ∈ xs) →
  Unique.Unique (removeAt selected)
removeAtUnique (AllPairs._∷_ fresh rest) (Any.here refl) = rest
removeAtUnique (AllPairs._∷_ fresh rest) (Any.there selected) =
  AllPairs._∷_
    (allRemoveAt fresh selected)
    (removeAtUnique rest selected)

removedElementFresh :
  ∀ {A : Set} {x : A} {xs : List A} →
  Unique.Unique xs →
  (selected : x ∈ xs) →
  x ∉ removeAt selected
removedElementFresh (AllPairs._∷_ fresh rest) (Any.here refl) member =
  All.lookup fresh member refl
removedElementFresh
    (AllPairs._∷_ fresh rest) (Any.there selected) (Any.here equality) =
  All.lookup fresh selected (sym equality)
removedElementFresh
    (AllPairs._∷_ fresh rest) (Any.there selected) (Any.there member) =
  removedElementFresh rest selected member

remainderMemberDifferent :
  ∀ {A : Set} {x z : A} {xs : List A} →
  Unique.Unique xs →
  (selected : x ∈ xs) →
  z ∈ removeAt selected →
  z ≢ x
remainderMemberDifferent unique selected member equality =
  removedElementFresh unique selected
    (subst (λ chosen → chosen ∈ removeAt selected) equality member)

consMemberToTailWhenDifferent :
  ∀ {A : Set} {x z : A} {xs : List A} →
  z ∈ (x ∷ xs) → z ≢ x → z ∈ xs
consMemberToTailWhenDifferent (Any.here equality) different =
  ⊥-elim (different equality)
consMemberToTailWhenDifferent (Any.there member) different = member

uniqueMembershipEquivalenceToPermutation :
  ∀ {A : Set} {xs ys : List A} →
  Unique.Unique xs →
  Unique.Unique ys →
  (∀ {z} → z ∈ xs → z ∈ ys) →
  (∀ {z} → z ∈ ys → z ∈ xs) →
  xs Perm.↭ ys
uniqueMembershipEquivalenceToPermutation
    {xs = []} {ys = []} sourceUnique targetUnique forward backward =
  Perm.refl
uniqueMembershipEquivalenceToPermutation
    {xs = []} {ys = y ∷ ys} sourceUnique targetUnique forward backward
  with backward (Any.here refl)
... | ()
uniqueMembershipEquivalenceToPermutation
    {xs = x ∷ xs} {ys = []} sourceUnique targetUnique forward backward
  with forward (Any.here refl)
... | ()
uniqueMembershipEquivalenceToPermutation
    {xs = x ∷ xs} {ys = y ∷ ys}
    (AllPairs._∷_ sourceFresh sourceTailUnique)
    targetUnique forward backward =
  let
    selected : x ∈ (y ∷ ys)
    selected = forward (Any.here refl)

    targetRemainderUnique : Unique.Unique (removeAt selected)
    targetRemainderUnique = removeAtUnique targetUnique selected

    forwardTail :
      ∀ {z} → z ∈ xs → z ∈ removeAt selected
    forwardTail member =
      otherMemberSurvivesRemoval
        selected
        (forward (Any.there member))
        (λ equality → All.lookup sourceFresh member (sym equality))

    backwardTail :
      ∀ {z} → z ∈ removeAt selected → z ∈ xs
    backwardTail member =
      consMemberToTailWhenDifferent
        (backward (removeAtMemberOriginal selected member))
        (remainderMemberDifferent targetUnique selected member)

    tailPermutation : xs Perm.↭ removeAt selected
    tailPermutation =
      uniqueMembershipEquivalenceToPermutation
        sourceTailUnique targetRemainderUnique forwardTail backwardTail
  in
  Perm.trans
    (Perm.prep x tailPermutation)
    (PermP.↭-sym (removeAtPermutation selected))

canonicalConjugateOutputFiberPermutation :
  (cutoff : Nat) (output : Z3.FourierMode) →
  map canonicalConjugate (Output.physicalOutputFiber cutoff output)
    Perm.↭
  Output.physicalOutputFiber cutoff (Z3.negateMode output)
canonicalConjugateOutputFiberPermutation cutoff output =
  uniqueMembershipEquivalenceToPermutation
    (mappedCanonicalConjugateUnique cutoff output)
    (physicalOutputFiberUnique cutoff (Z3.negateMode output))
    mappedConjugateMemberImpliesTarget
    targetMemberImpliesMappedConjugate

outputFiberConjugationListPermutationClosed : Bool
outputFiberConjugationListPermutationClosed = true

outputFiberConjugationListPermutationClosedIsTrue :
  outputFiberConjugationListPermutationClosed ≡ true
outputFiberConjugationListPermutationClosedIsTrue = refl
