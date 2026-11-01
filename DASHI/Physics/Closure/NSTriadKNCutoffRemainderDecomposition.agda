module DASHI.Physics.Closure.NSTriadKNCutoffRemainderDecomposition where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Bool.Base using (T; _∧_)
open import Data.Bool.Properties using (T-∧)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; map; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Permutation.Propositional as Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermP
import Data.List.Relation.Binary.BagAndSetEquality as Bag
import Data.List.Relation.Unary.Unique.Propositional as Unique
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.List.Membership.Propositional.Properties.WithK using (unique⇒irrelevant)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as ℕP
open import Function.Bundles using (mk↔ₛ′; Equivalence)
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNPhysicalFourierInteraction as Interaction
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Sector
import DASHI.Physics.Closure.NSTriadKNFiniteConvolutionReconstruction as Reconstruction

------------------------------------------------------------------------
-- Finite-window cutoff decomposition.
--
-- `M` is deliberately a finite outer input cutoff.  This module proves no
-- assertion about an infinite Fourier sum: it splits the exact direct
-- convolution inside that finite window into the contribution with both
-- inputs in an inner cutoff `R` and its literal complement.
------------------------------------------------------------------------

insideCutoff? : Nat → Lattice.LatticeTriad → Bool
insideCutoff? R τ =
  Sector.inExactCutoff? R (Lattice.left τ) ∧
  Sector.inExactCutoff? R (Lattice.right τ)

-- The complement of `filterᵇ P`, defined structurally so its finite-sum
-- identity does not rely on any unproved Boolean partition library.
outsideFilter : {A : Set} → (A → Bool) → List A → List A
outsideFilter P [] = []
outsideFilter P (x ∷ xs) with P x
... | true  = outsideFilter P xs
... | false = x ∷ outsideFilter P xs

finiteWindowOrderedTriads : Nat → Nat → List Lattice.LatticeTriad
finiteWindowOrderedTriads N M = Reconstruction.orderedCutoffConvolutionTriads N M

finiteWindowInsideTriads : Nat → Nat → Nat → List Lattice.LatticeTriad
finiteWindowInsideTriads N R M =
  filterᵇ (insideCutoff? R) (finiteWindowOrderedTriads N M)

finiteWindowOutsideTriads : Nat → Nat → Nat → List Lattice.LatticeTriad
finiteWindowOutsideTriads N R M =
  outsideFilter (insideCutoff? R) (finiteWindowOrderedTriads N M)

outsideFilterEmptyWhenAll :
  {A : Set} → (P : A → Bool) → (xs : List A) →
  ((x : A) → x ∈ xs → T (P x)) →
  outsideFilter P xs ≡ []
outsideFilterEmptyWhenAll P [] all = refl
outsideFilterEmptyWhenAll P (x ∷ xs) all with P x in P-x
... | true = outsideFilterEmptyWhenAll P xs (λ y y∈xs → all y (there y∈xs))
... | false = ⊥-elim (falseTElim P-x (all x (here refl)))
  where
  falseTElim : {b : Bool} → b ≡ false → T b → ⊥
  falseTElim refl ()

-- The inner carrier inherits duplicate-freeness from the direct outer
-- convolution carrier.  This lets membership equivalence determine a list
-- permutation, rather than requiring a fragile equality of enumeration
-- orders.
finiteWindowInsideTriadsUnique :
  (N R M : Nat) → Unique.Unique (finiteWindowInsideTriads N R M)
finiteWindowInsideTriadsUnique N R M =
  UniqueP.filter⁺ (T? ∘ insideCutoff? R)
    (Reconstruction.orderedCutoffConvolutionTriadsUnique N M)

-- Generic exact additive split for a finite list.  This is the only algebra
-- needed for the cutoff remainder identity.
sumFilterOutsidePartition :
  {A : Set} →
  {S : Scalar.ExactOrderedScalar} →
  (sumA : Reconstruction.ExactFiniteSumAuthority S) →
  (P : A → Bool) → (f : A → Scalar.Scalar S) → (xs : List A) →
  Reconstruction.sumScalarList S (map f xs) ≡
  Scalar._+_ S
    (Reconstruction.sumScalarList S (map f (filterᵇ P xs)))
    (Reconstruction.sumScalarList S (map f (outsideFilter P xs)))
sumFilterOutsidePartition {S = S} sumA P f [] =
  sym (Reconstruction.additionIdentityLeft sumA (Scalar.zero S))
sumFilterOutsidePartition {S = S} sumA P f (x ∷ xs) with P x
... | true =
  trans
    (cong (Scalar._+_ S (f x))
      (sumFilterOutsidePartition sumA P f xs))
    (sym (Reconstruction.additionAssociative sumA
      (f x)
      (Reconstruction.sumScalarList S (map f (filterᵇ P xs)))
      (Reconstruction.sumScalarList S (map f (outsideFilter P xs)))))
... | false =
  trans
    (cong (Scalar._+_ S (f x))
      (sumFilterOutsidePartition sumA P f xs))
    (trans
      (sym (Reconstruction.additionAssociative sumA
        (f x)
        (Reconstruction.sumScalarList S (map f (filterᵇ P xs)))
        (Reconstruction.sumScalarList S (map f (outsideFilter P xs)))))
      (trans
        (cong (λ z → Scalar._+_ S z
          (Reconstruction.sumScalarList S (map f (outsideFilter P xs))))
          (Reconstruction.additionCommutative sumA
            (f x)
            (Reconstruction.sumScalarList S (map f (filterᵇ P xs)))))
        (Reconstruction.additionAssociative sumA
          (Reconstruction.sumScalarList S (map f (filterᵇ P xs)))
          (f x)
          (Reconstruction.sumScalarList S (map f (outsideFilter P xs))))))

finiteWindowOrderedConvection :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  Interaction.ExactNSFourierInteractionStructure S C →
  (N M : Nat) →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) → Scalar.Scalar S
finiteWindowOrderedConvection {S = S} I N M u =
  Reconstruction.sumScalarList S
    (map (Reconstruction.orderedConvectionTerm I u)
      (finiteWindowOrderedTriads N M))

finiteWindowInsideConvection :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  Interaction.ExactNSFourierInteractionStructure S C →
  (N R M : Nat) →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) → Scalar.Scalar S
finiteWindowInsideConvection {S = S} I N R M u =
  Reconstruction.sumScalarList S
    (map (Reconstruction.orderedConvectionTerm I u)
      (finiteWindowInsideTriads N R M))

finiteWindowCutoffRemainder :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  Interaction.ExactNSFourierInteractionStructure S C →
  (N R M : Nat) →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) → Scalar.Scalar S
finiteWindowCutoffRemainder {S = S} I N R M u =
  Reconstruction.sumScalarList S
    (map (Reconstruction.orderedConvectionTerm I u)
      (finiteWindowOutsideTriads N R M))

finiteWindowConvectionDecomposition :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (sumA : Reconstruction.ExactFiniteSumAuthority S) →
  (N R M : Nat) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  finiteWindowOrderedConvection I N M u ≡
  Scalar._+_ S
    (finiteWindowInsideConvection I N R M u)
    (finiteWindowCutoffRemainder I N R M u)
finiteWindowConvectionDecomposition {S = S} I sumA N R M u =
  sumFilterOutsidePartition sumA (insideCutoff? R)
    (Reconstruction.orderedConvectionTerm I u)
    (finiteWindowOrderedTriads N M)

-- This is intentionally a separately named obligation.  The two finite
-- enumerators need not use the same list order, so agreement is a
-- permutation rather than literal list equality.  It is true only after
-- proving exact cube inclusion for `R ≤ M`; the finite partition theorem
-- above does not assume it.
--
-- The next record isolates the only non-list content of that result.  Its
-- two fields are precisely the geometric carrier equivalence: the first
-- uses `R ≤ M` to embed the inner cube in the outer cube, and the second
-- recognises that both filtered carriers impose the same output-shell,
-- zero-sum, and nonzero conditions.
record InnerCutoffCarrierMembership
    (N R M : Nat) : Set where
  field
    innerMemberImpliesDirect :
      (τ : Lattice.LatticeTriad) →
      τ ∈ finiteWindowInsideTriads N R M →
      τ ∈ Reconstruction.orderedCutoffConvolutionTriads N R
    directMemberImpliesInner :
      (τ : Lattice.LatticeTriad) →
      τ ∈ Reconstruction.orderedCutoffConvolutionTriads N R →
      τ ∈ finiteWindowInsideTriads N R M

-- Once the generated mode list is proved sound and complete for its exact
-- signed-coordinate predicate, the two triad-membership implications are
-- routine filter/candidate transport.  This is the concrete reduction of
-- the global carrier theorem to the local decoder theorem plus `R ≤ M`.
innerCutoffCarrierMembershipFromExactCutoffModes :
  (N R M : Nat) → R ≤ M →
  Sector.ExactCutoffModeEnumeration R →
  Sector.ExactCutoffModeEnumeration M →
  InnerCutoffCarrierMembership N R M
innerCutoffCarrierMembershipFromExactCutoffModes N R M R≤M enumR enumM = record
  { innerMemberImpliesDirect = innerToDirect
  ; directMemberImpliesInner = directToInner
  }
  where
  innerToDirect :
    (τ : Lattice.LatticeTriad) →
    τ ∈ finiteWindowInsideTriads N R M →
    τ ∈ Reconstruction.orderedCutoffConvolutionTriads N R
  innerToDirect τ τ∈inner =
    Reconstruction.filterMemberComplete Lattice.zeroSum? τ
      (Sector.physicalOutputSectorCandidates N R)
      (Reconstruction.rawCutoffCandidateMember N R τ rawR)
      zeroSum
    where
    innerFacts :
      (τ ∈ Reconstruction.orderedCutoffConvolutionTriads N M) ×
      T (insideCutoff? R τ)
    innerFacts = Reconstruction.filterMemberSound (insideCutoff? R) τ
      (finiteWindowOrderedTriads N M) τ∈inner

    outerFacts :
      (τ ∈ Sector.physicalOutputSectorCandidates N M) × T (Lattice.zeroSum? τ)
    outerFacts = Reconstruction.filterMemberSound Lattice.zeroSum? τ
      (Sector.physicalOutputSectorCandidates N M) (proj₁ innerFacts)

    rawM : Reconstruction.RawCutoffCandidate N M τ
    rawM = proj₂ (Reconstruction.rawCutoffCandidateMembership N M τ)
      (proj₁ outerFacts)

    insideFacts :
      T (Sector.inExactCutoff? R (Lattice.left τ)) ×
      T (Sector.inExactCutoff? R (Lattice.right τ))
    insideFacts = Equivalence.to T-∧ (proj₂ innerFacts)

    rawR : Reconstruction.RawCutoffCandidate N R τ
    rawR =
      Sector.ExactCutoffModeEnumeration.memberComplete enumR
        (Lattice.left τ) (proj₁ insideFacts)
      , (Sector.ExactCutoffModeEnumeration.memberComplete enumR
          (Lattice.right τ) (proj₂ insideFacts)
        , proj₂ (proj₂ rawM))

    zeroSum : T (Lattice.zeroSum? τ)
    zeroSum = proj₂ outerFacts

  directToInner :
    (τ : Lattice.LatticeTriad) →
    τ ∈ Reconstruction.orderedCutoffConvolutionTriads N R →
    τ ∈ finiteWindowInsideTriads N R M
  directToInner τ τ∈direct =
    Reconstruction.filterMemberComplete (insideCutoff? R) τ
      (finiteWindowOrderedTriads N M)
      (Reconstruction.filterMemberComplete Lattice.zeroSum? τ
        (Sector.physicalOutputSectorCandidates N M)
        (Reconstruction.rawCutoffCandidateMember N M τ rawM)
        zeroSum)
      insideR
    where
    directFacts :
      (τ ∈ Sector.physicalOutputSectorCandidates N R) × T (Lattice.zeroSum? τ)
    directFacts = Reconstruction.filterMemberSound Lattice.zeroSum? τ
      (Sector.physicalOutputSectorCandidates N R) τ∈direct

    rawR : Reconstruction.RawCutoffCandidate N R τ
    rawR = proj₂ (Reconstruction.rawCutoffCandidateMembership N R τ)
      (proj₁ directFacts)

    rawM : Reconstruction.RawCutoffCandidate N M τ
    rawM =
      Sector.cutoffModesMonotone R M R≤M enumR enumM
        (Lattice.left τ) (proj₁ rawR)
      , (Sector.cutoffModesMonotone R M R≤M enumR enumM
          (Lattice.right τ) (proj₁ (proj₂ rawR))
        , proj₂ (proj₂ rawR))

    zeroSum : T (Lattice.zeroSum? τ)
    zeroSum = proj₂ directFacts

    insideR : T (insideCutoff? R τ)
    insideR = Equivalence.from T-∧
      (Sector.ExactCutoffModeEnumeration.memberSound enumR
        (Lattice.left τ) (proj₁ rawR)
      , Sector.ExactCutoffModeEnumeration.memberSound enumR
          (Lattice.right τ) (proj₁ (proj₂ rawR)))

innerCutoffCarrierBagEquality :
  (N R M : Nat) → InnerCutoffCarrierMembership N R M →
  Bag._∼[_]_
    (finiteWindowInsideTriads N R M) Bag.bag
    (Reconstruction.orderedCutoffConvolutionTriads N R)
innerCutoffCarrierBagEquality N R M membership {τ} =
  mk↔ₛ′
    (InnerCutoffCarrierMembership.innerMemberImpliesDirect membership τ)
    (InnerCutoffCarrierMembership.directMemberImpliesInner membership τ)
    (λ _ → unique⇒irrelevant
      (Reconstruction.orderedCutoffConvolutionTriadsUnique N R) _ _)
    (λ _ → unique⇒irrelevant
      (finiteWindowInsideTriadsUnique N R M) _ _)

innerCutoffCarrierPermutationFromMembership :
  (N R M : Nat) → InnerCutoffCarrierMembership N R M →
  finiteWindowInsideTriads N R M ↭
  Reconstruction.orderedCutoffConvolutionTriads N R
innerCutoffCarrierPermutationFromMembership N R M membership =
  Bag.∼bag⇒↭ (innerCutoffCarrierBagEquality N R M membership)

record InnerCutoffAgreesWithDirectEnumeration
    (N R M : Nat) : Set where
  field
    insidePermutesDirectCutoff :
      finiteWindowInsideTriads N R M ↭
      Reconstruction.orderedCutoffConvolutionTriads N R

innerCutoffAgreementFromCarrierMembership :
  (N R M : Nat) → InnerCutoffCarrierMembership N R M →
  InnerCutoffAgreesWithDirectEnumeration N R M
innerCutoffAgreementFromCarrierMembership N R M membership = record
  { insidePermutesDirectCutoff =
      innerCutoffCarrierPermutationFromMembership N R M membership
  }

-- Canonical assembly of the requested inner/direct enumeration agreement.
-- The only still-uninhabited input is the local theorem that `cutoffModes`
-- enumerates its signed-coordinate predicate exactly; all triad filtering,
-- duplicate handling, permutation, and sum transport are now derived.
innerCutoffAgreementFromExactCutoffModes :
  (N R M : Nat) → R ≤ M →
  Sector.ExactCutoffModeEnumeration R →
  Sector.ExactCutoffModeEnumeration M →
  InnerCutoffAgreesWithDirectEnumeration N R M
innerCutoffAgreementFromExactCutoffModes N R M R≤M enumR enumM =
  innerCutoffAgreementFromCarrierMembership N R M
    (innerCutoffCarrierMembershipFromExactCutoffModes
      N R M R≤M enumR enumM)

-- At its own cutoff radius every raw ordered convolution triad has both
-- inputs inside the signed-coordinate cube.  Consequently the literal
-- outside carrier is empty; this is the exact finite-support endpoint.
rawTriadInsideOwnCutoff :
  (N R : Nat) → (τ : Lattice.LatticeTriad) →
  τ ∈ finiteWindowOrderedTriads N R → T (insideCutoff? R τ)
rawTriadInsideOwnCutoff N R τ τ∈raw =
  Equivalence.from T-∧
    (Sector.ExactCutoffModeEnumeration.memberSound enum
      (Lattice.left τ) (proj₁ raw)
    , Sector.ExactCutoffModeEnumeration.memberSound enum
        (Lattice.right τ) (proj₁ (proj₂ raw)))
  where
  enum : Sector.ExactCutoffModeEnumeration R
  enum = Sector.exactCutoffModeEnumeration R

  rawFacts :
    (τ ∈ Sector.physicalOutputSectorCandidates N R) × T (Lattice.zeroSum? τ)
  rawFacts = Reconstruction.filterMemberSound Lattice.zeroSum? τ
    (Sector.physicalOutputSectorCandidates N R) τ∈raw

  raw : Reconstruction.RawCutoffCandidate N R τ
  raw = proj₂ (Reconstruction.rawCutoffCandidateMembership N R τ) (proj₁ rawFacts)

finiteWindowOutsideOwnCutoffEmpty :
  (N R : Nat) → finiteWindowOutsideTriads N R R ≡ []
finiteWindowOutsideOwnCutoffEmpty N R =
  outsideFilterEmptyWhenAll (insideCutoff? R) (finiteWindowOrderedTriads N R)
    (rawTriadInsideOwnCutoff N R)

finiteWindowOwnCutoffRemainderZero :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (N R : Nat) → (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  finiteWindowCutoffRemainder I N R R u ≡ Scalar.zero S
finiteWindowOwnCutoffRemainderZero {S = S} I N R u
  rewrite finiteWindowOutsideOwnCutoffEmpty N R = refl

-- The cutoff-mode decoder is now an exact finite enumeration, so the
-- inner/direct carrier agreement has no remaining enumeration premise.
canonicalInnerCutoffAgreement :
  (N R M : Nat) → R ≤ M →
  InnerCutoffAgreesWithDirectEnumeration N R M
canonicalInnerCutoffAgreement N R M R≤M =
  innerCutoffAgreementFromExactCutoffModes N R M R≤M
    (Sector.exactCutoffModeEnumeration R)
    (Sector.exactCutoffModeEnumeration M)

-- The carrier permutation is the only enumerative input needed to transport
-- the inner finite convolution.  The weighted summand is arbitrary here,
-- which keeps the cube-inclusion proof separate from Fourier algebra.
innerCutoffConvectionAgreesWithDirectEnumeration :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (sumA : Reconstruction.ExactFiniteSumAuthority S) →
  (N R M : Nat) →
  InnerCutoffAgreesWithDirectEnumeration N R M →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  finiteWindowInsideConvection I N R M u ≡
  Reconstruction.cutoffShellConvection I N R u
innerCutoffConvectionAgreesWithDirectEnumeration
  {S = S} I sumA N R M agreement u =
  Reconstruction.sumScalarList-resp-↭ S sumA
    (PermP.map⁺ (Reconstruction.orderedConvectionTerm I u)
      (InnerCutoffAgreesWithDirectEnumeration.insidePermutesDirectCutoff
        agreement))

-- Combining the structural finite-window partition with carrier agreement
-- gives the exact direct-inner-cutoff plus literal outer-cutoff remainder.
finiteWindowConvectionEqualsDirectCutoffPlusRemainder :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (sumA : Reconstruction.ExactFiniteSumAuthority S) →
  (N R M : Nat) →
  InnerCutoffAgreesWithDirectEnumeration N R M →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  finiteWindowOrderedConvection I N M u ≡
  Scalar._+_ S
    (Reconstruction.cutoffShellConvection I N R u)
    (finiteWindowCutoffRemainder I N R M u)
finiteWindowConvectionEqualsDirectCutoffPlusRemainder
  {S = S} I sumA N R M agreement u =
  trans
    (finiteWindowConvectionDecomposition I sumA N R M u)
    (cong (λ inner → Scalar._+_ S inner
      (finiteWindowCutoffRemainder I N R M u))
      (innerCutoffConvectionAgreesWithDirectEnumeration
        I sumA N R M agreement u))

-- The direct cutoff term has already been reindexed by canonical swap
-- orbits.  This is the finite physical bridge from an outer convolution
-- window to the coefficient source used by the orbit Gram assembly.
finiteWindowConvectionEqualsCanonicalOrbitPlusRemainder :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (sumA : Reconstruction.ExactFiniteSumAuthority S) →
  (N R M : Nat) →
  InnerCutoffAgreesWithDirectEnumeration N R M →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  finiteWindowOrderedConvection I N M u ≡
  Scalar._+_ S
    (Reconstruction.canonicalUnorderedTriadInteractionSum I N R u)
    (finiteWindowCutoffRemainder I N R M u)
finiteWindowConvectionEqualsCanonicalOrbitPlusRemainder
  {S = S} I sumA N R M agreement u =
  trans
    (finiteWindowConvectionEqualsDirectCutoffPlusRemainder
      I sumA N R M agreement u)
    (cong (λ cutoff → Scalar._+_ S cutoff
      (finiteWindowCutoffRemainder I N R M u))
      (Reconstruction.finiteTriadExpansionReconstructsCutoffConvection
        I sumA N R u))

-- Fully concrete finite-cutoff bridge: the outer convolution window splits
-- into the canonical orbit interaction sum at radius R plus the literal
-- outside-R remainder, with no enumeration witness supplied by callers.
canonicalFiniteWindowConvectionEqualsCanonicalOrbitPlusRemainder :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (sumA : Reconstruction.ExactFiniteSumAuthority S) →
  (N R M : Nat) → R ≤ M →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  finiteWindowOrderedConvection I N M u ≡
  Scalar._+_ S
    (Reconstruction.canonicalUnorderedTriadInteractionSum I N R u)
    (finiteWindowCutoffRemainder I N R M u)
canonicalFiniteWindowConvectionEqualsCanonicalOrbitPlusRemainder
  I sumA N R M R≤M u =
  finiteWindowConvectionEqualsCanonicalOrbitPlusRemainder I sumA N R M
    (canonicalInnerCutoffAgreement N R M R≤M) u

-- For a Fourier polynomial whose outer window is R itself, no cutoff tail
-- remains.  This is the exact finite-support reconstruction theorem; the
-- later M → ∞ passage is deliberately a separate analytic obligation.
finiteSupportConvectionEqualsCanonicalOrbitSum :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (sumA : Reconstruction.ExactFiniteSumAuthority S) →
  (N R : Nat) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  finiteWindowOrderedConvection I N R u ≡
  Reconstruction.canonicalUnorderedTriadInteractionSum I N R u
finiteSupportConvectionEqualsCanonicalOrbitSum {S = S} I sumA N R u =
  trans
    (canonicalFiniteWindowConvectionEqualsCanonicalOrbitPlusRemainder
      I sumA N R R (ℕP.≤-refl {x = R}) u)
    (trans
      (cong (Scalar._+_ S
        (Reconstruction.canonicalUnorderedTriadInteractionSum I N R u))
        (finiteWindowOwnCutoffRemainderZero I N R u))
      (trans
        (Reconstruction.additionCommutative sumA
          (Reconstruction.canonicalUnorderedTriadInteractionSum I N R u)
          (Scalar.zero S))
        (Reconstruction.additionIdentityLeft sumA
          (Reconstruction.canonicalUnorderedTriadInteractionSum I N R u))))
