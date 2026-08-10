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
-- predicate, allowing set-level membership equivalence to be promoted to an
-- actual propositional list permutation via `Bag.∼bag⇒↭`.
--
-- The result is the exact reindexing theorem
--
--   map canonicalConjugate (outputFiber k)
--     ↭ outputFiber (-k).
--
-- No ordering convention and no proof irrelevance axiom is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Empty using (⊥)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
import Data.List.Relation.Unary.Unique.Propositional as Unique
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
import Data.List.Relation.Binary.BagAndSetEquality as Bag
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.List.Membership.Propositional.Properties.WithK using (unique⇒irrelevant)
open import Data.List.Relation.Unary.Any as Any using ()
open import Data.Product using (Σ; _,_; _×_)
open import Function.Bundles using (mk↔ₛ′)
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
-- Exact standard-list membership equivalence and permutation.
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

outputFiberConjugationBagEquality :
  (cutoff : Nat) (output : Z3.FourierMode) →
  Bag._∼[_]_
    (map canonicalConjugate (Output.physicalOutputFiber cutoff output))
    Bag.bag
    (Output.physicalOutputFiber cutoff (Z3.negateMode output))
outputFiberConjugationBagEquality cutoff output {τ} =
  mk↔ₛ′
    mappedConjugateMemberImpliesTarget
    targetMemberImpliesMappedConjugate
    (λ _ → unique⇒irrelevant
      (physicalOutputFiberUnique cutoff (Z3.negateMode output)) _ _)
    (λ _ → unique⇒irrelevant
      (mappedCanonicalConjugateUnique cutoff output) _ _)

canonicalConjugateOutputFiberPermutation :
  (cutoff : Nat) (output : Z3.FourierMode) →
  map canonicalConjugate (Output.physicalOutputFiber cutoff output)
    Perm.↭
  Output.physicalOutputFiber cutoff (Z3.negateMode output)
canonicalConjugateOutputFiberPermutation cutoff output =
  Bag.∼bag⇒↭ (outputFiberConjugationBagEquality cutoff output)

outputFiberConjugationListPermutationClosed : Bool
outputFiberConjugationListPermutationClosed = true

outputFiberConjugationListPermutationClosedIsTrue :
  outputFiberConjugationListPermutationClosed ≡ true
outputFiberConjugationListPermutationClosedIsTrue = refl
