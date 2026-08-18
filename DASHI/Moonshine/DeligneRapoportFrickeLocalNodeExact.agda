module DASHI.Moonshine.DeligneRapoportFrickeLocalNodeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Pierre Deligne and Michael Rapoport,
-- "Les schemas de modules de courbes elliptiques",
-- Lecture Notes in Mathematics 349 (1973), 143--316.
-- DOI: 10.1007/978-3-540-37855-6_4.
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- DASHI CONTRIBUTION
--
-- Make the local finite branch calculation behind the quotient-node statement
-- explicit.  Before quotienting, a supersingular intersection has two branch
-- labels, one on each Deligne--Rapoport component.  For one quadratic
-- Frobenius pair x0 <-> x1, Fricke simultaneously swaps the components and the
-- pair orientation:
--
--   (C0,   x0) <-> (Cinf, x1)
--   (Cinf, x0) <-> (C0,   x1).
--
-- Hence the four oriented prequotient branches form exactly TWO Fricke branch
-- orbits over ONE paired-orbit node coordinate.  This is the finite local
-- combinatorial signature of the self-node described in the source geometry.
--
-- The theorem does not assert completed-local-ring nodality; identifying this
-- finite branch picture with the actual modular-curve local ring remains part
-- of the Deligne--Rapoport same-object authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

------------------------------------------------------------------------
-- One paired-orbit local branch carrier.
------------------------------------------------------------------------

record PairedLocalBranch (paired : Nat) : Set where
  constructor paired-branch
  field
    nodeIndex : Fin paired
    component : DR.DRComponent
    orientation : Orbit.Bit2

open PairedLocalBranch public

frickeLocalBranch :
  ∀ {paired} → PairedLocalBranch paired → PairedLocalBranch paired
frickeLocalBranch (paired-branch index component orientation) =
  paired-branch index
    (DR.frickeComponent component)
    (Orbit.flipBit orientation)

frickeLocalBranchInvolutive :
  ∀ {paired} (branch : PairedLocalBranch paired) →
  frickeLocalBranch (frickeLocalBranch branch) ≡ branch
frickeLocalBranchInvolutive
  (paired-branch index DR.component0 Orbit.bit0) = refl
frickeLocalBranchInvolutive
  (paired-branch index DR.component0 Orbit.bit1) = refl
frickeLocalBranchInvolutive
  (paired-branch index DR.componentInfinity Orbit.bit0) = refl
frickeLocalBranchInvolutive
  (paired-branch index DR.componentInfinity Orbit.bit1) = refl

frickeLocalBranchFixedPointFree :
  ∀ {paired} (branch : PairedLocalBranch paired) →
  frickeLocalBranch branch ≡ branch → ⊥
frickeLocalBranchFixedPointFree
  (paired-branch index DR.component0 Orbit.bit0) ()
frickeLocalBranchFixedPointFree
  (paired-branch index DR.component0 Orbit.bit1) ()
frickeLocalBranchFixedPointFree
  (paired-branch index DR.componentInfinity Orbit.bit0) ()
frickeLocalBranchFixedPointFree
  (paired-branch index DR.componentInfinity Orbit.bit1) ()

------------------------------------------------------------------------
-- Two quotient branch types.
--
-- branch0 orbit: (C0,0) <-> (Cinf,1)
-- branch1 orbit: (Cinf,0) <-> (C0,1)
------------------------------------------------------------------------

data QuotientBranch2 : Set where
  quotientBranch0 quotientBranch1 : QuotientBranch2

quotientBranch :
  ∀ {paired} → PairedLocalBranch paired → QuotientBranch2
quotientBranch (paired-branch index DR.component0 Orbit.bit0) = quotientBranch0
quotientBranch (paired-branch index DR.componentInfinity Orbit.bit1) = quotientBranch0
quotientBranch (paired-branch index DR.componentInfinity Orbit.bit0) = quotientBranch1
quotientBranch (paired-branch index DR.component0 Orbit.bit1) = quotientBranch1

quotientBranchInvariant :
  ∀ {paired} (branch : PairedLocalBranch paired) →
  quotientBranch (frickeLocalBranch branch) ≡ quotientBranch branch
quotientBranchInvariant
  (paired-branch index DR.component0 Orbit.bit0) = refl
quotientBranchInvariant
  (paired-branch index DR.component0 Orbit.bit1) = refl
quotientBranchInvariant
  (paired-branch index DR.componentInfinity Orbit.bit0) = refl
quotientBranchInvariant
  (paired-branch index DR.componentInfinity Orbit.bit1) = refl

localNode : ∀ {paired} → PairedLocalBranch paired → Fin paired
localNode = nodeIndex

localNodeInvariant :
  ∀ {paired} (branch : PairedLocalBranch paired) →
  localNode (frickeLocalBranch branch) ≡ localNode branch
localNodeInvariant branch = refl

------------------------------------------------------------------------
-- Explicit two branch-orbit sections over every node.
------------------------------------------------------------------------

branch0Section :
  ∀ {paired} → Fin paired → PairedLocalBranch paired
branch0Section index = paired-branch index DR.component0 Orbit.bit0

branch1Section :
  ∀ {paired} → Fin paired → PairedLocalBranch paired
branch1Section index = paired-branch index DR.componentInfinity Orbit.bit0

branch0SectionHasNode :
  ∀ {paired} (index : Fin paired) → localNode (branch0Section index) ≡ index
branch0SectionHasNode index = refl

branch1SectionHasNode :
  ∀ {paired} (index : Fin paired) → localNode (branch1Section index) ≡ index
branch1SectionHasNode index = refl

branch0SectionHasType :
  ∀ {paired} (index : Fin paired) →
  quotientBranch (branch0Section index) ≡ quotientBranch0
branch0SectionHasType index = refl

branch1SectionHasType :
  ∀ {paired} (index : Fin paired) →
  quotientBranch (branch1Section index) ≡ quotientBranch1
branch1SectionHasType index = refl

quotientBranchTypesDistinct : quotientBranch0 ≡ quotientBranch1 → ⊥
quotientBranchTypesDistinct ()

------------------------------------------------------------------------
-- Every oriented branch is in exactly one of these two quotient branch types;
-- each type has an explicit representative over the same node coordinate.
------------------------------------------------------------------------

record FrickeLocalNodeWitness (paired : Nat) : Set where
  field
    node : Fin paired
    firstBranch secondBranch : PairedLocalBranch paired
    firstAtNode : localNode firstBranch ≡ node
    secondAtNode : localNode secondBranch ≡ node
    firstType : quotientBranch firstBranch ≡ quotientBranch0
    secondType : quotientBranch secondBranch ≡ quotientBranch1

open FrickeLocalNodeWitness public

canonicalFrickeLocalNodeWitness :
  ∀ {paired} → Fin paired → FrickeLocalNodeWitness paired
canonicalFrickeLocalNodeWitness index = record
  { node = index
  ; firstBranch = branch0Section index
  ; secondBranch = branch1Section index
  ; firstAtNode = refl
  ; secondAtNode = refl
  ; firstType = refl
  ; secondType = refl
  }

record DeligneRapoportFrickeLocalNodeBoundary : Set where
  field
    fourOrientedBranchesModeled : Bool
    frickeBranchActionFixedPointFree : Bool
    exactlyTwoQuotientBranchTypesConstructed : Bool
    bothBranchTypesShareOneNodeIndex : Bool
    completedLocalRingNodeProvedHere : Bool

canonicalDeligneRapoportFrickeLocalNodeBoundary :
  DeligneRapoportFrickeLocalNodeBoundary
canonicalDeligneRapoportFrickeLocalNodeBoundary = record
  { fourOrientedBranchesModeled = true
  ; frickeBranchActionFixedPointFree = true
  ; exactlyTwoQuotientBranchTypesConstructed = true
  ; bothBranchTypesShareOneNodeIndex = true
  ; completedLocalRingNodeProvedHere = false
  }
