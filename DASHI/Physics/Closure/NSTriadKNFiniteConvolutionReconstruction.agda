module DASHI.Physics.Closure.NSTriadKNFiniteConvolutionReconstruction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Bool.Base using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; concat; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using
  (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻; ∈-filter⁺; ∈-filter⁻; ∈-map⁺; ∈-map⁻
  ; ∈-concat⁺′; ∈-concat⁻′)
open import Data.List.Relation.Unary.All as All using (tabulate)
import Data.List.Relation.Unary.Unique.Propositional as Unique
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermP
import Data.List.Relation.Binary.BagAndSetEquality as Bag
open import Data.List.Membership.Propositional.Properties.WithK using (unique⇒irrelevant)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Integer.Properties as ℤP using (+-comm)
open import Function.Base using (_∘_)
open import Function.Bundles using (mk↔ₛ′)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalFourierInteraction as Interaction
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffModeSupport as Support
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Sector

------------------------------------------------------------------------
-- Exact finite cutoff convolution, before any reindexing.
--
-- A list element `(p , q , r)` has `p + q + r = 0`.  Its Fourier output
-- is `k = - r`, so this list is exactly the ordered-pair carrier for output
-- modes in shell N and inputs in the cube cutoff R.  Crucially, this raw
-- carrier does *not* mention a retained-sector law: it is the direct finite
-- convolution expression which a physical retained sector must reconstruct.
------------------------------------------------------------------------

orderedCutoffConvolutionTriads : Nat → Nat → List Lattice.LatticeTriad
orderedCutoffConvolutionTriads N R =
  filterᵇ Lattice.zeroSum? (Sector.physicalOutputSectorCandidates N R)

-- The proposition behind the raw finite candidate list.  Keeping it beside
-- the list definition lets the eventual filtered-list theorem separate the
-- integer geometry from list bookkeeping.
RawCutoffCandidate : Nat → Nat → Lattice.LatticeTriad → Set
RawCutoffCandidate N R τ =
  (Lattice.left τ ∈ Sector.cutoffModes R) ×
  ((Lattice.right τ ∈ Sector.cutoffModes R) ×
   (Lattice.out τ ∈ Lattice.exactShellModes N))

rawCutoffCandidateSwapClosed :
  (N R : Nat) → (τ : Lattice.LatticeTriad) →
  RawCutoffCandidate N R τ → RawCutoffCandidate N R (Lattice.triadSwap τ)
rawCutoffCandidateSwapClosed N R (Lattice.mkLatticeTriad p q r)
  (p∈ , q∈ , r∈) = q∈ , p∈ , r∈

rawCutoffCandidateMember :
  (N R : Nat) → (τ : Lattice.LatticeTriad) →
  RawCutoffCandidate N R τ → τ ∈ Sector.physicalOutputSectorCandidates N R
rawCutoffCandidateMember N R (Lattice.mkLatticeTriad p q r) (p∈ , q∈ , r∈) =
  ∈-cartesianProductWith⁺
    (λ left pair → Lattice.mkLatticeTriad left
      (Data.Product.proj₁ pair) (Data.Product.proj₂ pair))
    p∈
    (∈-cartesianProductWith⁺ _,_ q∈ r∈)

rawCutoffCandidateMembership :
  (N R : Nat) → (τ : Lattice.LatticeTriad) →
  (RawCutoffCandidate N R τ → τ ∈ Sector.physicalOutputSectorCandidates N R) ×
  (τ ∈ Sector.physicalOutputSectorCandidates N R → RawCutoffCandidate N R τ)
rawCutoffCandidateMembership N R τ =
  rawCutoffCandidateMember N R τ , candidateMember→RawCandidate N R τ
  where
  candidateMember→RawCandidate :
    (N R : Nat) → (τ : Lattice.LatticeTriad) →
    τ ∈ Sector.physicalOutputSectorCandidates N R → RawCutoffCandidate N R τ
  candidateMember→RawCandidate N R τ τ∈candidates
    with ∈-cartesianProductWith⁻
      (λ left pair → Lattice.mkLatticeTriad left
        (Data.Product.proj₁ pair) (Data.Product.proj₂ pair))
      (Sector.cutoffModes R)
      (Data.List.Base.cartesianProductWith _,_ (Sector.cutoffModes R)
        (Lattice.exactShellModes N))
      τ∈candidates
  ... | p , pair , p∈ , pair∈ , τ≡
    with ∈-cartesianProductWith⁻ _,_ (Sector.cutoffModes R)
      (Lattice.exactShellModes N) pair∈
  ... | q , r , q∈ , r∈ , pair≡
    rewrite τ≡ | pair≡ = p∈ , q∈ , r∈

modePairConstructorInjective :
  {p q r s : Lattice.LatticeMode3} →
  (p , q) ≡ (r , s) → (p ≡ r) × (q ≡ s)
modePairConstructorInjective refl = refl , refl

triadCandidateConstructorInjective :
  {p q r p′ q′ r′ : Lattice.LatticeMode3} →
  Lattice.mkLatticeTriad p q r ≡ Lattice.mkLatticeTriad p′ q′ r′ →
  (p ≡ p′) × ((q , r) ≡ (q′ , r′))
triadCandidateConstructorInjective τ≡ =
  cong Lattice.left τ≡ ,
  cong₂ _,_ (cong Lattice.right τ≡) (cong Lattice.out τ≡)

-- All multiplicity in the raw convolution list comes from the two mode
-- enumerations.  The nested Cartesian products and the zero-sum filter do
-- not introduce it.  This isolates the remaining enumeration theorem to
-- injectivity of `decodeCubeCode` and its two filtered mode lists.
physicalOutputSectorCandidatesUniqueFromModes :
  (N R : Nat) →
  Unique.Unique (Sector.cutoffModes R) →
  Unique.Unique (Lattice.exactShellModes N) →
  Unique.Unique (Sector.physicalOutputSectorCandidates N R)
physicalOutputSectorCandidatesUniqueFromModes N R cutoffUnique shellUnique =
  UniqueP.cartesianProductWith⁺
    (λ left pair → Lattice.mkLatticeTriad left
      (Data.Product.proj₁ pair) (Data.Product.proj₂ pair))
    triadCandidateConstructorInjective
    cutoffUnique
    (UniqueP.cartesianProductWith⁺ _,_ modePairConstructorInjective
      cutoffUnique shellUnique)

orderedCutoffConvolutionTriadsUniqueFromModes :
  (N R : Nat) →
  Unique.Unique (Sector.cutoffModes R) →
  Unique.Unique (Lattice.exactShellModes N) →
  Unique.Unique (orderedCutoffConvolutionTriads N R)
orderedCutoffConvolutionTriadsUniqueFromModes N R cutoffUnique shellUnique =
  UniqueP.filter⁺ (T? ∘ Lattice.zeroSum?)
    (physicalOutputSectorCandidatesUniqueFromModes N R cutoffUnique shellUnique)

orderedCutoffConvolutionTriadsUnique :
  (N R : Nat) → Unique.Unique (orderedCutoffConvolutionTriads N R)
orderedCutoffConvolutionTriadsUnique N R =
  orderedCutoffConvolutionTriadsUniqueFromModes N R
    (Sector.cutoffModesUnique R)
    (Lattice.exactShellModesUnique N)

filterMemberSound :
  {A : Set} → (P : A → Bool) → (x : A) → (xs : List A) →
  x ∈ filterᵇ P xs → (x ∈ xs) × T (P x)
filterMemberSound P x xs member with ∈-filter⁻ (T? ∘ P) member
... | x∈xs , Px = x∈xs , Px

filterMemberComplete :
  {A : Set} → (P : A → Bool) → (x : A) → (xs : List A) →
  x ∈ xs → T (P x) → x ∈ filterᵇ P xs
filterMemberComplete P x xs = ∈-filter⁺ (T? ∘ P)

zeroSumSwapInvariant :
  (τ : Lattice.LatticeTriad) →
  Lattice.zeroSum? (Lattice.triadSwap τ) ≡ Lattice.zeroSum? τ
zeroSumSwapInvariant (Lattice.mkLatticeTriad p q r)
  rewrite ℤP.+-comm (Lattice.k₁ q) (Lattice.k₁ p)
        | ℤP.+-comm (Lattice.k₂ q) (Lattice.k₂ p)
        | ℤP.+-comm (Lattice.k₃ q) (Lattice.k₃ p) = refl

rawCutoffConvolutionSwapClosed :
  (N R : Nat) → (τ : Lattice.LatticeTriad) →
  τ ∈ orderedCutoffConvolutionTriads N R →
  Lattice.triadSwap τ ∈ orderedCutoffConvolutionTriads N R
rawCutoffConvolutionSwapClosed N R τ τ∈raw =
  filterMemberComplete Lattice.zeroSum? (Lattice.triadSwap τ)
    (Sector.physicalOutputSectorCandidates N R)
    (rawCutoffCandidateMember N R (Lattice.triadSwap τ)
      (rawCutoffCandidateSwapClosed N R τ rawCandidate))
    (zeroSumSwap τ zeroSum)
  where
  filteredFacts :
    (τ ∈ Sector.physicalOutputSectorCandidates N R) × T (Lattice.zeroSum? τ)
  filteredFacts =
    filterMemberSound Lattice.zeroSum? τ
      (Sector.physicalOutputSectorCandidates N R) τ∈raw

  candidateMember : τ ∈ Sector.physicalOutputSectorCandidates N R
  candidateMember = Data.Product.proj₁ filteredFacts

  zeroSum : T (Lattice.zeroSum? τ)
  zeroSum = Data.Product.proj₂ filteredFacts

  rawCandidate : RawCutoffCandidate N R τ
  rawCandidate = Data.Product.proj₂ (rawCutoffCandidateMembership N R τ)
    candidateMember

  zeroSumSwap :
    (σ : Lattice.LatticeTriad) → T (Lattice.zeroSum? σ) →
    T (Lattice.zeroSum? (Lattice.triadSwap σ))
  zeroSumSwap σ h rewrite zeroSumSwapInvariant σ = h

convolutionOutput : Lattice.LatticeTriad → Lattice.LatticeMode3
convolutionOutput τ = Lattice.modeNeg (Lattice.out τ)

-- The raw carrier is stored in the same `(left , right , out)` record as a
-- physical zero-sum triad.  Its Fourier output is `- out`; spelling out the
-- two directions here prevents later code from confusing that output with the
-- third member of the zero-sum triple.
rawToPhysicalTriad : Lattice.LatticeTriad → Lattice.LatticeTriad
rawToPhysicalTriad τ = τ

physicalTriadToRaw : Lattice.LatticeTriad → Lattice.LatticeTriad
physicalTriadToRaw τ = τ

rawToPhysicalToRaw :
  (τ : Lattice.LatticeTriad) → physicalTriadToRaw (rawToPhysicalTriad τ) ≡ τ
rawToPhysicalToRaw τ = refl

physicalToRawToPhysical :
  (τ : Lattice.LatticeTriad) → rawToPhysicalTriad (physicalTriadToRaw τ) ≡ τ
physicalToRawToPhysical τ = refl

-- One *ordered* Fourier-convolution summand.  The two ordered inputs have
-- deliberately not been combined here; that is the content of the later
-- swap-orbit theorem.
orderedConvectionTerm :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  Interaction.ExactNSFourierInteractionStructure S C →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) →
  Lattice.LatticeTriad → Scalar.Scalar S
orderedConvectionTerm {S = S} {C = C} I u τ =
  Scalar.neg S
    (Interaction.realPart I
      (Interaction.complexInner I
        (Fourier.conjugateVector C
          (u (Lattice.modeNeg (Lattice.out τ))))
        (Interaction.lerayProject I (convolutionOutput τ)
          (Interaction.scaleFourierVector I
            (Interaction.complexMultiply I (Interaction.imaginaryUnit I)
              (Fourier.dotModeCoefficient C (Lattice.right τ)
                (u (Lattice.left τ))))
            (u (Lattice.right τ))))))

sumScalarList :
  (S : Scalar.ExactOrderedScalar) → List (Scalar.Scalar S) → Scalar.Scalar S
sumScalarList S [] = Scalar.zero S
sumScalarList S (x ∷ xs) = Scalar._+_ S x (sumScalarList S xs)

-- Finite regrouping only needs the additive commutative-monoid fragment of
-- the scalar authority.  It is deliberately separate from order, Fourier,
-- and Gram assumptions: this is the exact algebra consumed by a list
-- permutation proof.
record ExactFiniteSumAuthority (S : Scalar.ExactOrderedScalar) : Set₁ where
  field
    additionIdentityLeft :
      (a : Scalar.Scalar S) → Scalar._+_ S (Scalar.zero S) a ≡ a
    additionAssociative :
      (a b c : Scalar.Scalar S) →
      Scalar._+_ S (Scalar._+_ S a b) c ≡
      Scalar._+_ S a (Scalar._+_ S b c)
    additionCommutative :
      (a b : Scalar.Scalar S) → Scalar._+_ S a b ≡ Scalar._+_ S b a

open ExactFiniteSumAuthority public

sumScalarList-resp-↭ :
  (S : Scalar.ExactOrderedScalar) → ExactFiniteSumAuthority S →
  {xs ys : List (Scalar.Scalar S)} → xs Perm.↭ ys →
  sumScalarList S xs ≡ sumScalarList S ys
sumScalarList-resp-↭ S A Perm.refl = refl
sumScalarList-resp-↭ S A (Perm.prep x xs↭ys) =
  cong (λ z → Scalar._+_ S x z) (sumScalarList-resp-↭ S A xs↭ys)
sumScalarList-resp-↭ S A (Perm.swap {xs = xs} x y xs↭ys) =
  trans
    (sym (additionAssociative A x y (sumScalarList S xs)))
    (trans
      (cong (λ z → Scalar._+_ S z (sumScalarList S xs))
        (additionCommutative A x y))
      (trans
        (additionAssociative A y x (sumScalarList S xs))
        (cong (λ z → Scalar._+_ S y (Scalar._+_ S x z))
          (sumScalarList-resp-↭ S A xs↭ys))))
sumScalarList-resp-↭ S A (Perm.trans xs↭ys ys↭zs) =
  trans (sumScalarList-resp-↭ S A xs↭ys)
    (sumScalarList-resp-↭ S A ys↭zs)

cutoffShellConvection :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  Interaction.ExactNSFourierInteractionStructure S C →
  (N R : Nat) →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) → Scalar.Scalar S
cutoffShellConvection {S = S} I N R u =
  sumScalarList S
    (map (orderedConvectionTerm I u) (orderedCutoffConvolutionTriads N R))

------------------------------------------------------------------------
-- The exact algebra authority used by convolution reindexing.
--
-- This is intentionally distinct from the ordered commutative ring used by
-- the Gram carrier.  These four laws are the finite Fourier facts needed to
-- turn the two ordered convolution terms into the symmetrised interaction.
------------------------------------------------------------------------

record ExactFiniteFourierConvolutionAuthority
    {S : Scalar.ExactOrderedScalar} {C : Fourier.ComplexFourierInterface S}
    (I : Interaction.ExactNSFourierInteractionStructure S C) : Set₁ where
  field
    lerayProjectAdd :
      (k : Lattice.LatticeMode3) →
      (v w : Fourier.FourierVector C) →
      Interaction.lerayProject I k (Interaction.addFourierVector I v w) ≡
      Interaction.addFourierVector I
        (Interaction.lerayProject I k v) (Interaction.lerayProject I k w)
    complexInnerAddRight :
      (v w x : Fourier.FourierVector C) →
      Interaction.complexInner I v (Interaction.addFourierVector I w x) ≡
      Fourier._+ᶜ_ C (Interaction.complexInner I v w)
        (Interaction.complexInner I v x)
    realPartAdd :
      (z w : Fourier.Complex C) →
      Interaction.realPart I (Fourier._+ᶜ_ C z w) ≡
      Scalar._+_ S (Interaction.realPart I z) (Interaction.realPart I w)
    negAdd :
      (a b : Scalar.Scalar S) →
      Scalar.neg S (Scalar._+_ S a b) ≡
      Scalar._+_ S (Scalar.neg S a) (Scalar.neg S b)

open ExactFiniteFourierConvolutionAuthority public

orderedPairSymmetrisation :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : ExactFiniteFourierConvolutionAuthority I) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  (τ : Lattice.LatticeTriad) →
  Interaction.offDiagonalSymmetrizedInteraction I u τ ≡
  Scalar._+_ S
    (orderedConvectionTerm I u τ)
    (orderedConvectionTerm I u (Lattice.triadSwap τ))
orderedPairSymmetrisation {S = S} {C = C} I A u
  (Lattice.mkLatticeTriad p q r) =
  negativeRealInnerLerayAdd I A
    (Fourier.conjugateVector C (u (Lattice.modeNeg r)))
    (Lattice.modeNeg r)
    (Interaction.scaleFourierVector I
      (Interaction.complexMultiply I (Interaction.imaginaryUnit I)
        (Fourier.dotModeCoefficient C q (u p))) (u q))
    (Interaction.scaleFourierVector I
      (Interaction.complexMultiply I (Interaction.imaginaryUnit I)
        (Fourier.dotModeCoefficient C p (u q))) (u p))
  where
  projectedInner :
    (J : Interaction.ExactNSFourierInteractionStructure S C) →
    Fourier.FourierVector C → Lattice.LatticeMode3 → Fourier.FourierVector C →
    Fourier.Complex C
  projectedInner J v k w =
    Interaction.complexInner J v (Interaction.lerayProject J k w)

  realProjectedInner :
    (J : Interaction.ExactNSFourierInteractionStructure S C) →
    Fourier.FourierVector C → Lattice.LatticeMode3 → Fourier.FourierVector C →
    Scalar.Scalar S
  realProjectedInner J v k w = Interaction.realPart J (projectedInner J v k w)

  negativeRealInnerLerayAdd :
    (J : Interaction.ExactNSFourierInteractionStructure S C) →
    ExactFiniteFourierConvolutionAuthority J →
    (v : Fourier.FourierVector C) → (k : Lattice.LatticeMode3) →
    (w x : Fourier.FourierVector C) →
    Scalar.neg S (realProjectedInner J v k (Interaction.addFourierVector J w x)) ≡
    Scalar._+_ S
      (Scalar.neg S (realProjectedInner J v k w))
      (Scalar.neg S (realProjectedInner J v k x))
  negativeRealInnerLerayAdd J B v k w x rewrite lerayProjectAdd B k w x
          | complexInnerAddRight B v
              (Interaction.lerayProject J k w)
              (Interaction.lerayProject J k x)
          | realPartAdd B
              (projectedInner J v k w)
              (projectedInner J v k x)
          | negAdd B
              (realProjectedInner J v k w)
              (realProjectedInner J v k x) =
    refl

------------------------------------------------------------------------
-- Canonical unordered input-pair orbits.
--
-- The diagonal `p = q` cannot use the usual two-term symmetrisation.  The
-- orbit witness carries its multiplicity explicitly: one ordered summand on
-- the diagonal and two off it.  This is deliberately a theorem datum rather
-- than an unproved Boolean test on lattice modes.
------------------------------------------------------------------------

data SwapOrbitKind : Set where
  diagonal offDiagonal : SwapOrbitKind

orderedPairMultiplicity : SwapOrbitKind → Nat
orderedPairMultiplicity diagonal = 1
orderedPairMultiplicity offDiagonal = 2

latticeTriadDecEq :
  (τ σ : Lattice.LatticeTriad) → Dec (τ ≡ σ)
latticeTriadDecEq
  (Lattice.mkLatticeTriad p q r)
  (Lattice.mkLatticeTriad p′ q′ r′)
  with Support.latticeModeDecEq p p′
... | no p≢ = no λ { refl → p≢ refl }
... | yes refl with Support.latticeModeDecEq q q′
... | no q≢ = no λ { refl → q≢ refl }
... | yes refl with Support.latticeModeDecEq r r′
... | no r≢ = no λ { refl → r≢ refl }
... | yes refl = yes refl

triadEqual? : Lattice.LatticeTriad → Lattice.LatticeTriad → Bool
triadEqual? τ σ with latticeTriadDecEq τ σ
... | yes _ = true
... | no _ = false

triadEqual?-sound :
  (τ σ : Lattice.LatticeTriad) → triadEqual? τ σ ≡ true → τ ≡ σ
triadEqual?-sound τ σ h with latticeTriadDecEq τ σ
... | yes τ≡σ = τ≡σ
... | no _ with h
... | ()

triadEqual?-complete :
  (τ σ : Lattice.LatticeTriad) → τ ≡ σ → triadEqual? τ σ ≡ true
triadEqual?-complete τ .τ refl with latticeTriadDecEq τ τ
... | yes _ = refl
... | no τ≢τ = ⊥-elim (τ≢τ refl)

swapOrbitKind : Lattice.LatticeTriad → SwapOrbitKind
swapOrbitKind τ with Support.latticeModeDecEq (Lattice.left τ) (Lattice.right τ)
... | yes _ = diagonal
... | no _ = offDiagonal

swapOrbitKindDiagonalWhenInputsEqual :
  (τ : Lattice.LatticeTriad) →
  Lattice.left τ ≡ Lattice.right τ →
  swapOrbitKind τ ≡ diagonal
swapOrbitKindDiagonalWhenInputsEqual τ refl
  with Support.latticeModeDecEq (Lattice.right τ) (Lattice.right τ)
... | yes _ = refl
... | no notRefl = ⊥-elim (notRefl refl)

triadSwapInvolutive :
  (τ : Lattice.LatticeTriad) →
  Lattice.triadSwap (Lattice.triadSwap τ) ≡ τ
triadSwapInvolutive (Lattice.mkLatticeTriad p q r) = refl

triadSwapFixedWhenInputsEqual :
  (τ : Lattice.LatticeTriad) →
  Lattice.left τ ≡ Lattice.right τ →
  Lattice.triadSwap τ ≡ τ
triadSwapFixedWhenInputsEqual (Lattice.mkLatticeTriad p q r) refl = refl

swapOrbitKindDiagonalImpliesInputsEqual :
  (τ : Lattice.LatticeTriad) →
  swapOrbitKind τ ≡ diagonal →
  Lattice.left τ ≡ Lattice.right τ
swapOrbitKindDiagonalImpliesInputsEqual τ h
  with Support.latticeModeDecEq (Lattice.left τ) (Lattice.right τ)
... | yes p≡q = p≡q
... | no _ with h
... | ()

record UnorderedInputOrbit : Set where
  constructor mkUnorderedInputOrbit
  field
    representative : Lattice.LatticeTriad

open UnorderedInputOrbit public

orbitKind : UnorderedInputOrbit → SwapOrbitKind
orbitKind o = swapOrbitKind (representative o)

triadMember? : Lattice.LatticeTriad → List Lattice.LatticeTriad → Bool
triadMember? τ [] = false
triadMember? τ (σ ∷ σs) with triadEqual? τ σ
... | true = true
... | false = triadMember? τ σs

triadMember?-sound :
  (τ : Lattice.LatticeTriad) → (ts : List Lattice.LatticeTriad) →
  triadMember? τ ts ≡ true → τ ∈ ts
triadMember?-sound τ [] ()
triadMember?-sound τ (σ ∷ σs) member with triadEqual? τ σ in h
... | true = here (triadEqual?-sound τ σ h)
... | false = there (triadMember?-sound τ σs member)

triadMember?-complete :
  (τ : Lattice.LatticeTriad) → (ts : List Lattice.LatticeTriad) →
  τ ∈ ts → triadMember? τ ts ≡ true
triadMember?-complete τ [] ()
triadMember?-complete τ (σ ∷ σs) (here τ≡σ)
  rewrite triadEqual?-complete τ σ τ≡σ = refl
triadMember?-complete τ (σ ∷ σs) (there τ∈σs) with triadEqual? τ σ
... | true = refl
... | false = triadMember?-complete τ σs τ∈σs

triadMember?Iff :
  (τ : Lattice.LatticeTriad) → (ts : List Lattice.LatticeTriad) →
  (triadMember? τ ts ≡ true → τ ∈ ts) ×
  (τ ∈ ts → triadMember? τ ts ≡ true)
triadMember?Iff τ ts = triadMember?-sound τ ts , triadMember?-complete τ ts

triadMember?-falseSound :
  (τ : Lattice.LatticeTriad) → (ts : List Lattice.LatticeTriad) →
  triadMember? τ ts ≡ false → τ ∈ ts → ⊥
triadMember?-falseSound τ ts τ∉ tsMember
  with triadMember?-complete τ ts tsMember
... | τ∈ = falseNotTrue (trans (sym τ∉) τ∈)
  where
  falseNotTrue : false ≡ true → ⊥
  falseNotTrue ()

insertSwapOrbitRepresentative :
  Lattice.LatticeTriad → List Lattice.LatticeTriad → List Lattice.LatticeTriad
insertSwapOrbitRepresentative τ reps
  with triadMember? τ reps | triadMember? (Lattice.triadSwap τ) reps
... | true | _ = reps
... | false | true = reps
... | false | false = τ ∷ reps

representativeMembershipPreservedByInsert :
  (τ σ : Lattice.LatticeTriad) → (reps : List Lattice.LatticeTriad) →
  σ ∈ reps → σ ∈ insertSwapOrbitRepresentative τ reps
representativeMembershipPreservedByInsert τ σ reps σ∈reps
  with triadMember? τ reps | triadMember? (Lattice.triadSwap τ) reps
... | true | _ = σ∈reps
... | false | true = σ∈reps
... | false | false = there σ∈reps

insertRepresentativeMemberOrigin :
  (τ σ : Lattice.LatticeTriad) → (reps : List Lattice.LatticeTriad) →
  σ ∈ insertSwapOrbitRepresentative τ reps →
  (σ ≡ τ) ⊎ (σ ∈ reps)
insertRepresentativeMemberOrigin τ σ reps σ∈insert
  with triadMember? τ reps | triadMember? (Lattice.triadSwap τ) reps | σ∈insert
... | true | _ | σ∈reps = inj₂ σ∈reps
... | false | true | σ∈reps = inj₂ σ∈reps
... | false | false | here σ≡τ = inj₁ σ≡τ
... | false | false | there σ∈reps = inj₂ σ∈reps

insertRepresentativeCoversHead :
  (τ : Lattice.LatticeTriad) → (reps : List Lattice.LatticeTriad) →
  (τ ∈ insertSwapOrbitRepresentative τ reps) ⊎
  (Lattice.triadSwap τ ∈ insertSwapOrbitRepresentative τ reps)
insertRepresentativeCoversHead τ reps
  with triadMember? τ reps in hτ | triadMember? (Lattice.triadSwap τ) reps in hswap
... | true | _ = inj₁ (triadMember?-sound τ reps hτ)
... | false | true = inj₂ (triadMember?-sound (Lattice.triadSwap τ) reps hswap)
... | false | false = inj₁ (here refl)

canonicalUnorderedInputRepresentatives :
  List Lattice.LatticeTriad → List Lattice.LatticeTriad
canonicalUnorderedInputRepresentatives [] = []
canonicalUnorderedInputRepresentatives (τ ∷ τs) =
  insertSwapOrbitRepresentative τ (canonicalUnorderedInputRepresentatives τs)

canonicalRepresentativesCover :
  (x : Lattice.LatticeTriad) → (xs : List Lattice.LatticeTriad) →
  x ∈ xs →
  (x ∈ canonicalUnorderedInputRepresentatives xs) ⊎
  (Lattice.triadSwap x ∈ canonicalUnorderedInputRepresentatives xs)
canonicalRepresentativesCover x [] ()
canonicalRepresentativesCover x (τ ∷ τs) (here x≡τ)
  rewrite x≡τ = insertRepresentativeCoversHead τ
    (canonicalUnorderedInputRepresentatives τs)
canonicalRepresentativesCover x (τ ∷ τs) (there x∈τs)
  with canonicalRepresentativesCover x τs x∈τs
... | inj₁ x∈reps =
  inj₁
    (representativeMembershipPreservedByInsert τ x
      (canonicalUnorderedInputRepresentatives τs) x∈reps)
... | inj₂ swapx∈reps =
  inj₂
    (representativeMembershipPreservedByInsert τ (Lattice.triadSwap x)
      (canonicalUnorderedInputRepresentatives τs) swapx∈reps)

-- No representative list may contain the same swap orbit twice.  This is
-- stronger than ordinary duplicate-freeness: it excludes both `r` and
-- `swap r` as distinct representatives.
data OrbitSeparatedRepresentatives : List Lattice.LatticeTriad → Set where
  []-separated : OrbitSeparatedRepresentatives []
  _∷-separated_ :
    {r : Lattice.LatticeTriad} {rs : List Lattice.LatticeTriad} →
    ((s : Lattice.LatticeTriad) → s ∈ rs → (r ≡ s → ⊥) ×
      (Lattice.triadSwap r ≡ s → ⊥)) →
    OrbitSeparatedRepresentatives rs →
    OrbitSeparatedRepresentatives (r ∷ rs)

insertRepresentativePreservesSeparation :
  (τ : Lattice.LatticeTriad) → (reps : List Lattice.LatticeTriad) →
  OrbitSeparatedRepresentatives reps →
  OrbitSeparatedRepresentatives (insertSwapOrbitRepresentative τ reps)
insertRepresentativePreservesSeparation τ reps separated
  with triadMember? τ reps in hτ | triadMember? (Lattice.triadSwap τ) reps in hswap
... | true | _ = separated
... | false | true = separated
... | false | false = _∷-separated_ headSeparated separated
  where
  substMember :
    {a b : Lattice.LatticeTriad} → a ≡ b → b ∈ reps → a ∈ reps
  substMember refl b∈reps = b∈reps

  headSeparated :
    (s : Lattice.LatticeTriad) → s ∈ reps → (τ ≡ s → ⊥) ×
    (Lattice.triadSwap τ ≡ s → ⊥)
  headSeparated s s∈reps =
    (λ τ≡s → triadMember?-falseSound τ reps hτ
      (substMember τ≡s s∈reps)) ,
    (λ swapτ≡s → triadMember?-falseSound (Lattice.triadSwap τ) reps hswap
      (substMember swapτ≡s s∈reps))

canonicalRepresentativesSeparated :
  (raw : List Lattice.LatticeTriad) →
  OrbitSeparatedRepresentatives (canonicalUnorderedInputRepresentatives raw)
canonicalRepresentativesSeparated [] = []-separated
canonicalRepresentativesSeparated (τ ∷ τs) =
  insertRepresentativePreservesSeparation τ
    (canonicalUnorderedInputRepresentatives τs)
    (canonicalRepresentativesSeparated τs)

-- Separation is stronger than ordinary duplicate-freeness, but the latter is
-- the exact multiplicity fact required by finite scalar regrouping.  Proving
-- it here closes the canonical-orbit side independently of the still-open
-- injectivity proof for the raw integer-cube enumeration.
orbitSeparatedRepresentativesUnique :
  (rs : List Lattice.LatticeTriad) →
  OrbitSeparatedRepresentatives rs → Unique.Unique rs
orbitSeparatedRepresentativesUnique [] []-separated = Unique.[]
orbitSeparatedRepresentativesUnique (r ∷ rs)
  (headSeparated ∷-separated separated) =
  Unique._∷_
    (All.tabulate
      (λ {s} s∈rs r≡s →
        Data.Product.proj₁ (headSeparated s s∈rs) r≡s))
    (orbitSeparatedRepresentativesUnique rs separated)

canonicalUnorderedInputRepresentativesUnique :
  (raw : List Lattice.LatticeTriad) →
  Unique.Unique (canonicalUnorderedInputRepresentatives raw)
canonicalUnorderedInputRepresentativesUnique raw =
  orbitSeparatedRepresentativesUnique
    (canonicalUnorderedInputRepresentatives raw)
    (canonicalRepresentativesSeparated raw)

representativesEquivalentImpliesEqual :
  (reps : List Lattice.LatticeTriad) →
  OrbitSeparatedRepresentatives reps →
  (r s : Lattice.LatticeTriad) → r ∈ reps → s ∈ reps →
  (r ≡ s) ⊎ (r ≡ Lattice.triadSwap s) → r ≡ s
representativesEquivalentImpliesEqual [] []-separated r s () _ _
representativesEquivalentImpliesEqual (h ∷ hs) (headSeparated ∷-separated separated)
  r s r∈ s∈ equivalent with r∈ | s∈ | equivalent
... | here r≡h | here s≡h | _ = trans r≡h (sym s≡h)
... | here r≡h | there s∈hs | inj₁ r≡s =
  ⊥-elim (Data.Product.proj₁ (headSeparated s s∈hs)
    (trans (sym r≡h) r≡s))
... | here r≡h | there s∈hs | inj₂ r≡swapS =
  ⊥-elim (Data.Product.proj₂ (headSeparated s s∈hs)
    (trans (cong Lattice.triadSwap (sym r≡h))
      (trans (cong Lattice.triadSwap r≡swapS) (triadSwapInvolutive s))))
... | there r∈hs | here s≡h | inj₁ r≡s =
  ⊥-elim (Data.Product.proj₁ (headSeparated r r∈hs)
    (trans (sym s≡h) (sym r≡s)))
... | there r∈hs | here s≡h | inj₂ r≡swapS =
  ⊥-elim (Data.Product.proj₂ (headSeparated r r∈hs)
    (trans (cong Lattice.triadSwap (sym s≡h)) (sym r≡swapS)))
... | there r∈hs | there s∈hs | equivalent =
  representativesEquivalentImpliesEqual hs separated r s r∈hs s∈hs equivalent

canonicalRepresentativeOrigin :
  (r : Lattice.LatticeTriad) → (raw : List Lattice.LatticeTriad) →
  r ∈ canonicalUnorderedInputRepresentatives raw → r ∈ raw
canonicalRepresentativeOrigin r [] ()
canonicalRepresentativeOrigin r (τ ∷ τs) r∈canonical
  with insertRepresentativeMemberOrigin τ r
    (canonicalUnorderedInputRepresentatives τs) r∈canonical
... | inj₁ r≡τ rewrite r≡τ = here refl
... | inj₂ r∈tail = there (canonicalRepresentativeOrigin r τs r∈tail)

canonicalUnorderedInputOrbits : Nat → Nat → List UnorderedInputOrbit
canonicalUnorderedInputOrbits N R =
  map mkUnorderedInputOrbit
    (canonicalUnorderedInputRepresentatives
      (orderedCutoffConvolutionTriads N R))

unorderedInputOrbitConstructorInjective :
  {r s : Lattice.LatticeTriad} →
  mkUnorderedInputOrbit r ≡ mkUnorderedInputOrbit s → r ≡ s
unorderedInputOrbitConstructorInjective refl = refl

canonicalUnorderedInputOrbitsUnique :
  (N R : Nat) → Unique.Unique (canonicalUnorderedInputOrbits N R)
canonicalUnorderedInputOrbitsUnique N R =
  UniqueP.map⁺ unorderedInputOrbitConstructorInjective
    (canonicalUnorderedInputRepresentativesUnique
      (orderedCutoffConvolutionTriads N R))

orbitOfRepresentativeIsCanonical :
  (r : Lattice.LatticeTriad) → (reps : List Lattice.LatticeTriad) →
  r ∈ reps → mkUnorderedInputOrbit r ∈ map mkUnorderedInputOrbit reps
orbitOfRepresentativeIsCanonical r reps r∈reps =
  ∈-map⁺ mkUnorderedInputOrbit r∈reps

data InSwapOrbit (o : UnorderedInputOrbit) : Lattice.LatticeTriad → Set where
  representativeMember :
    InSwapOrbit o (representative o)
  swappedMember :
    orbitKind o ≡ offDiagonal →
    InSwapOrbit o (Lattice.triadSwap (representative o))

-- The actual finite fibre of an input-swap orbit.  It is deliberately a
-- list, because the later reindexing theorem is a finite-sum regrouping
-- result.  On the diagonal the swapped term is not repeated.
orbitMembers : UnorderedInputOrbit → List Lattice.LatticeTriad
orbitMembers o with orbitKind o
... | diagonal = representative o ∷ []
... | offDiagonal = representative o ∷ Lattice.triadSwap (representative o) ∷ []

inOrbitMembers→InSwapOrbit :
  (o : UnorderedInputOrbit) → (τ : Lattice.LatticeTriad) →
  τ ∈ orbitMembers o → InSwapOrbit o τ
inOrbitMembers→InSwapOrbit o τ member with orbitKind o in h | member
... | diagonal | here refl = representativeMember
... | diagonal | there ()
... | offDiagonal | here refl = representativeMember
... | offDiagonal | there (here refl) = swappedMember h
... | offDiagonal | there (there ())

inSwapOrbit→InOrbitMembers :
  (o : UnorderedInputOrbit) → (τ : Lattice.LatticeTriad) →
  InSwapOrbit o τ → τ ∈ orbitMembers o
inSwapOrbit→InOrbitMembers o τ representativeMember with orbitKind o
... | diagonal = here refl
... | offDiagonal = here refl
inSwapOrbit→InOrbitMembers o τ (swappedMember h) with orbitKind o | h
... | diagonal | ()
... | offDiagonal | refl = there (here refl)

orbitMembersIff :
  (o : UnorderedInputOrbit) → (τ : Lattice.LatticeTriad) →
  (τ ∈ orbitMembers o → InSwapOrbit o τ) ×
  (InSwapOrbit o τ → τ ∈ orbitMembers o)
orbitMembersIff o τ =
  inOrbitMembers→InSwapOrbit o τ , inSwapOrbit→InOrbitMembers o τ

diagonalOrbitFibreSingleton :
  (o : UnorderedInputOrbit) → orbitKind o ≡ diagonal →
  orbitMembers o ≡ representative o ∷ []
diagonalOrbitFibreSingleton o h with orbitKind o | h
... | diagonal | refl = refl
... | offDiagonal | ()

offDiagonalOrbitFibrePair :
  (o : UnorderedInputOrbit) → orbitKind o ≡ offDiagonal →
  orbitMembers o ≡ representative o ∷ Lattice.triadSwap (representative o) ∷ []
offDiagonalOrbitFibrePair o h with orbitKind o | h
... | diagonal | ()
... | offDiagonal | refl = refl

triadSwapFixedImpliesInputsEqual :
  (τ : Lattice.LatticeTriad) → Lattice.triadSwap τ ≡ τ →
  Lattice.left τ ≡ Lattice.right τ
triadSwapFixedImpliesInputsEqual τ fixed = sym (cong Lattice.left fixed)

offDiagonal≠diagonal : offDiagonal ≡ diagonal → ⊥
offDiagonal≠diagonal ()

offDiagonalRepresentativeDistinctFromSwap :
  (o : UnorderedInputOrbit) → orbitKind o ≡ offDiagonal →
  representative o ≡ Lattice.triadSwap (representative o) → ⊥
offDiagonalRepresentativeDistinctFromSwap o offDiagonalKind fixed =
  offDiagonal≠diagonal
    (trans (sym offDiagonalKind)
      (swapOrbitKindDiagonalWhenInputsEqual (representative o)
        (triadSwapFixedImpliesInputsEqual (representative o) (sym fixed))))

orbitMembersUnique : (o : UnorderedInputOrbit) → Unique.Unique (orbitMembers o)
orbitMembersUnique o with orbitKind o in kind
... | diagonal = Unique._∷_ All.[] Unique.[]
... | offDiagonal =
  Unique._∷_
    (All._∷_
      (offDiagonalRepresentativeDistinctFromSwap o kind)
      All.[])
    (Unique._∷_ All.[] Unique.[])

canonicalOrbitRepresentativeMember :
  (N R : Nat) → (o : UnorderedInputOrbit) →
  o ∈ canonicalUnorderedInputOrbits N R →
  representative o ∈ canonicalUnorderedInputRepresentatives
    (orderedCutoffConvolutionTriads N R)
canonicalOrbitRepresentativeMember N R o o∈canonical
  with ∈-map⁻ mkUnorderedInputOrbit o∈canonical
... | r , r∈reps , o≡r rewrite o≡r = r∈reps

orbitRepresentativesEqual :
  {o₁ o₂ : UnorderedInputOrbit} → representative o₁ ≡ representative o₂ → o₁ ≡ o₂
orbitRepresentativesEqual {mkUnorderedInputOrbit r₁} {mkUnorderedInputOrbit r₂} refl = refl

orbitOverlapEquivalent :
  (o₁ o₂ : UnorderedInputOrbit) → (τ : Lattice.LatticeTriad) →
  InSwapOrbit o₁ τ → InSwapOrbit o₂ τ →
  (representative o₁ ≡ representative o₂) ⊎
  (representative o₁ ≡ Lattice.triadSwap (representative o₂))
orbitOverlapEquivalent o₁ o₂ τ representativeMember representativeMember = inj₁ refl
orbitOverlapEquivalent o₁ o₂ τ representativeMember (swappedMember _) = inj₂ refl
orbitOverlapEquivalent o₁ o₂ τ (swappedMember _) representativeMember =
  inj₂ (trans (sym (triadSwapInvolutive (representative o₁))) refl)
orbitOverlapEquivalent o₁ o₂ τ (swappedMember _) (swappedMember _) =
  inj₁ (trans (sym (triadSwapInvolutive (representative o₁)))
    (triadSwapInvolutive (representative o₂)))

canonicalOrbitOverlapImpliesEqual :
  (N R : Nat) → {o₁ o₂ : UnorderedInputOrbit} →
  o₁ ∈ canonicalUnorderedInputOrbits N R →
  o₂ ∈ canonicalUnorderedInputOrbits N R →
  (τ : Lattice.LatticeTriad) → InSwapOrbit o₁ τ → InSwapOrbit o₂ τ → o₁ ≡ o₂
canonicalOrbitOverlapImpliesEqual N R {o₁} {o₂} o₁∈ o₂∈ τ member₁ member₂ =
  orbitRepresentativesEqual representativeEquality
  where
  reps = canonicalUnorderedInputRepresentatives
    (orderedCutoffConvolutionTriads N R)

  separated : OrbitSeparatedRepresentatives reps
  separated = canonicalRepresentativesSeparated
    (orderedCutoffConvolutionTriads N R)

  representativeEquality : representative o₁ ≡ representative o₂
  representativeEquality =
    representativesEquivalentImpliesEqual reps separated
      (representative o₁) (representative o₂)
      (canonicalOrbitRepresentativeMember N R o₁ o₁∈)
      (canonicalOrbitRepresentativeMember N R o₂ o₂∈)
      (orbitOverlapEquivalent o₁ o₂ τ member₁ member₂)

swappedRepresentativeMapsToOrbit :
  (τ : Lattice.LatticeTriad) → (reps : List Lattice.LatticeTriad) →
  Lattice.triadSwap τ ∈ reps →
  Σ UnorderedInputOrbit λ o →
    (o ∈ map mkUnorderedInputOrbit reps) × InSwapOrbit o τ
swappedRepresentativeMapsToOrbit τ reps swapτ∈reps
  with swapOrbitKind (Lattice.triadSwap τ) in h
... | diagonal =
  mkUnorderedInputOrbit (Lattice.triadSwap τ) ,
  orbitOfRepresentativeIsCanonical (Lattice.triadSwap τ) reps swapτ∈reps ,
  diagonalMember
  where
  fixed : Lattice.triadSwap (Lattice.triadSwap τ) ≡ Lattice.triadSwap τ
  fixed = triadSwapFixedWhenInputsEqual (Lattice.triadSwap τ)
    (swapOrbitKindDiagonalImpliesInputsEqual (Lattice.triadSwap τ) h)

  representativeIsTarget : Lattice.triadSwap τ ≡ τ
  representativeIsTarget = trans (sym fixed) (triadSwapInvolutive τ)

  diagonalMember : InSwapOrbit (mkUnorderedInputOrbit (Lattice.triadSwap τ)) τ
  diagonalMember rewrite representativeIsTarget = representativeMember
... | offDiagonal =
  mkUnorderedInputOrbit (Lattice.triadSwap τ) ,
  orbitOfRepresentativeIsCanonical (Lattice.triadSwap τ) reps swapτ∈reps ,
  offDiagonalMember
  where
  offDiagonalMember : InSwapOrbit (mkUnorderedInputOrbit (Lattice.triadSwap τ)) τ
  offDiagonalMember rewrite triadSwapInvolutive τ = swappedMember h

rawMemberMapsToCanonicalOrbit :
  (N R : Nat) → (τ : Lattice.LatticeTriad) →
  τ ∈ orderedCutoffConvolutionTriads N R →
  Σ UnorderedInputOrbit λ o →
    (o ∈ canonicalUnorderedInputOrbits N R) × InSwapOrbit o τ
rawMemberMapsToCanonicalOrbit N R τ τ∈raw
  with canonicalRepresentativesCover τ (orderedCutoffConvolutionTriads N R) τ∈raw
... | inj₁ τ∈reps =
  mkUnorderedInputOrbit τ ,
  orbitOfRepresentativeIsCanonical τ
    (canonicalUnorderedInputRepresentatives
      (orderedCutoffConvolutionTriads N R)) τ∈reps ,
  representativeMember
... | inj₂ swapτ∈reps =
  swappedRepresentativeMapsToOrbit τ
    (canonicalUnorderedInputRepresentatives
      (orderedCutoffConvolutionTriads N R)) swapτ∈reps

canonicalOrbitRepresentativeRaw :
  (N R : Nat) → (o : UnorderedInputOrbit) →
  o ∈ canonicalUnorderedInputOrbits N R →
  representative o ∈ orderedCutoffConvolutionTriads N R
canonicalOrbitRepresentativeRaw N R o o∈canonical
  with ∈-map⁻ mkUnorderedInputOrbit o∈canonical
... | r , r∈reps , o≡r rewrite o≡r =
  canonicalRepresentativeOrigin r
    (orderedCutoffConvolutionTriads N R) r∈reps

canonicalOrbitFibreRaw :
  (N R : Nat) → (o : UnorderedInputOrbit) →
  o ∈ canonicalUnorderedInputOrbits N R →
  (τ : Lattice.LatticeTriad) → InSwapOrbit o τ →
  τ ∈ orderedCutoffConvolutionTriads N R
canonicalOrbitFibreRaw N R o o∈canonical τ representativeMember =
  canonicalOrbitRepresentativeRaw N R o o∈canonical
canonicalOrbitFibreRaw N R o o∈canonical τ (swappedMember _) =
  rawCutoffConvolutionSwapClosed N R (representative o)
    (canonicalOrbitRepresentativeRaw N R o o∈canonical)

-- The flattened orbit fibres are the exact multiset target for the finite
-- reindexing.  At this point both sides are already duplicate-free carriers;
-- the two membership directions below leave only the constructive list
-- permutation itself.
flattenCanonicalOrbitMembers : Nat → Nat → List Lattice.LatticeTriad
flattenCanonicalOrbitMembers N R =
  concat (map orbitMembers (canonicalUnorderedInputOrbits N R))

rawCarrierMemberImpliesFlattenedOrbitMember :
  (N R : Nat) → (τ : Lattice.LatticeTriad) →
  τ ∈ orderedCutoffConvolutionTriads N R →
  τ ∈ flattenCanonicalOrbitMembers N R
rawCarrierMemberImpliesFlattenedOrbitMember N R τ τ∈raw
  with rawMemberMapsToCanonicalOrbit N R τ τ∈raw
... | o , o∈canonical , τ∈orbit =
  ∈-concat⁺′
    (Data.Product.proj₂ (orbitMembersIff o τ) τ∈orbit)
    (∈-map⁺ orbitMembers o∈canonical)

flattenedOrbitMemberImpliesRawCarrierMember :
  (N R : Nat) → (τ : Lattice.LatticeTriad) →
  τ ∈ flattenCanonicalOrbitMembers N R →
  τ ∈ orderedCutoffConvolutionTriads N R
flattenedOrbitMemberImpliesRawCarrierMember N R τ τ∈flattened
  with ∈-concat⁻′ (map orbitMembers (canonicalUnorderedInputOrbits N R)) τ∈flattened
... | fibre , τ∈fibre , fibre∈mapped
  with ∈-map⁻ orbitMembers fibre∈mapped
... | o , o∈canonical , fibre≡
  rewrite fibre≡ =
    canonicalOrbitFibreRaw N R o o∈canonical τ
      (Data.Product.proj₁ (orbitMembersIff o τ) τ∈fibre)

canonicalOrbitFibresPairwiseDisjoint :
  (N R : Nat) →
  AllPairs.AllPairs Disjoint
    (map orbitMembers (canonicalUnorderedInputOrbits N R))
canonicalOrbitFibresPairwiseDisjoint N R =
  go (canonicalUnorderedInputOrbits N R)
    (All.tabulate (λ o∈canonical → o∈canonical))
    (canonicalUnorderedInputOrbitsUnique N R)
  where
  canonical = canonicalUnorderedInputOrbits N R

  go :
    (os : List UnorderedInputOrbit) →
    All.All (λ o → o ∈ canonical) os →
    Unique.Unique os →
    AllPairs.AllPairs Disjoint (map orbitMembers os)
  go [] All.[] Unique.[] = AllPairs.[]
  go (o ∷ os) (o∈canonical All.∷ os∈canonical)
    unique@(headUnique Unique.∷ tailUnique) =
    AllPairs._∷_ headDisjoint
      (go os os∈canonical tailUnique)
    where
    headNotInTail : o ∉ os
    headNotInTail = UniqueP.Unique[x∷xs]⇒x∉xs unique

    proveDisjoint :
      {fibre : List Lattice.LatticeTriad} →
      fibre ∈ map orbitMembers os → Disjoint (orbitMembers o) fibre
    proveDisjoint fibre∈mapped
      with ∈-map⁻ orbitMembers fibre∈mapped
    ... | o′ , o′∈tail , fibre≡
      rewrite fibre≡ = disjointProof
      where
      o′∈canonical : o′ ∈ canonical
      o′∈canonical = All.lookup os∈canonical o′∈tail

      disjointProof : Disjoint (orbitMembers o) (orbitMembers o′)
      disjointProof {τ} (τ∈o , τ∈o′) =
        headNotInTail
          (subst (λ o″ → o″ ∈ os)
            (sym (canonicalOrbitOverlapImpliesEqual N R
              o∈canonical o′∈canonical τ
              (Data.Product.proj₁ (orbitMembersIff o τ) τ∈o)
              (Data.Product.proj₁ (orbitMembersIff o′ τ) τ∈o′)))
            o′∈tail)

    headDisjoint : All.All (Disjoint (orbitMembers o))
      (map orbitMembers os)
    headDisjoint = All.tabulate proveDisjoint

canonicalFlattenedOrbitMembersUnique :
  (N R : Nat) → Unique.Unique (flattenCanonicalOrbitMembers N R)
canonicalFlattenedOrbitMembersUnique N R =
  UniqueP.concat⁺ fibreUnique (canonicalOrbitFibresPairwiseDisjoint N R)
  where
  fibreUnique : All.All Unique.Unique
    (map orbitMembers (canonicalUnorderedInputOrbits N R))
  fibreUnique = All.tabulate proveUnique
    where
    proveUnique :
      {fibre : List Lattice.LatticeTriad} →
      fibre ∈ map orbitMembers (canonicalUnorderedInputOrbits N R) →
      Unique.Unique fibre
    proveUnique fibre∈mapped with ∈-map⁻ orbitMembers fibre∈mapped
    ... | o , _ , fibre≡ rewrite fibre≡ = orbitMembersUnique o

rawFlattenedOrbitCarrierBagEquality :
  (N R : Nat) →
  Bag._∼[_]_
    (orderedCutoffConvolutionTriads N R) Bag.bag
    (flattenCanonicalOrbitMembers N R)
rawFlattenedOrbitCarrierBagEquality N R {τ} =
  mk↔ₛ′
    (rawCarrierMemberImpliesFlattenedOrbitMember N R τ)
    (flattenedOrbitMemberImpliesRawCarrierMember N R τ)
    (λ _ → unique⇒irrelevant (canonicalFlattenedOrbitMembersUnique N R) _ _)
    (λ _ → unique⇒irrelevant (orderedCutoffConvolutionTriadsUnique N R) _ _)

rawOrderedCarrierPermutesToFlattenedOrbitCarrier :
  (N R : Nat) →
  orderedCutoffConvolutionTriads N R Perm.↭
  flattenCanonicalOrbitMembers N R
rawOrderedCarrierPermutesToFlattenedOrbitCarrier N R =
  Bag.∼bag⇒↭ (rawFlattenedOrbitCarrierBagEquality N R)

flattenedOrbitCutoffConvection :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  Interaction.ExactNSFourierInteractionStructure S C →
  (N R : Nat) →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) → Scalar.Scalar S
flattenedOrbitCutoffConvection {S = S} I N R u =
  sumScalarList S
    (map (orderedConvectionTerm I u) (flattenCanonicalOrbitMembers N R))

rawOrderedCutoffConvolutionEqualsFlattenedOrbitConvolution :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : ExactFiniteSumAuthority S) →
  (N R : Nat) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  cutoffShellConvection I N R u ≡
  flattenedOrbitCutoffConvection I N R u
rawOrderedCutoffConvolutionEqualsFlattenedOrbitConvolution
  {S = S} I A N R u =
  sumScalarList-resp-↭ S A
    (PermP.map⁺ (orderedConvectionTerm I u)
      (rawOrderedCarrierPermutesToFlattenedOrbitCarrier N R))

additionIdentityRight :
  (S : Scalar.ExactOrderedScalar) → ExactFiniteSumAuthority S →
  (a : Scalar.Scalar S) → Scalar._+_ S a (Scalar.zero S) ≡ a
additionIdentityRight S A a =
  trans
    (additionCommutative A a (Scalar.zero S))
    (additionIdentityLeft A a)

sumScalarList-++ :
  (S : Scalar.ExactOrderedScalar) → (A : ExactFiniteSumAuthority S) →
  (xs ys : List (Scalar.Scalar S)) →
  sumScalarList S (xs ++ ys) ≡
  Scalar._+_ S (sumScalarList S xs) (sumScalarList S ys)
sumScalarList-++ S A [] ys = sym (additionIdentityLeft A (sumScalarList S ys))
sumScalarList-++ S A (x ∷ xs) ys =
  trans
    (cong (λ z → Scalar._+_ S x z) (sumScalarList-++ S A xs ys))
    (sym (additionAssociative A x (sumScalarList S xs) (sumScalarList S ys)))

map-++ :
  {X Y : Set} → (f : X → Y) → (xs ys : List X) →
  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f [] ys = refl
map-++ f (x ∷ xs) ys = cong (λ zs → f x ∷ zs) (map-++ f xs ys)

map-∘ :
  {X Y Z : Set} → (f : Y → Z) → (g : X → Y) → (xs : List X) →
  map f (map g xs) ≡ map (λ x → f (g x)) xs
map-∘ f g [] = refl
map-∘ f g (x ∷ xs) = cong (λ zs → f (g x) ∷ zs) (map-∘ f g xs)

sumOrderedTermsOverConcat :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : ExactFiniteSumAuthority S) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  (fibres : List (List Lattice.LatticeTriad)) →
  sumScalarList S
    (map (orderedConvectionTerm I u) (concat fibres)) ≡
  sumScalarList S
    (map (λ fibre →
      sumScalarList S (map (orderedConvectionTerm I u) fibre)) fibres)
sumOrderedTermsOverConcat I A u [] = refl
sumOrderedTermsOverConcat {S = S} I A u (fibre ∷ fibres) =
  trans
    (cong (sumScalarList S)
      (map-++ (orderedConvectionTerm I u) fibre (concat fibres)))
    (trans
      (sumScalarList-++ S A
        (map (orderedConvectionTerm I u) fibre)
        (map (orderedConvectionTerm I u) (concat fibres)))
      (cong
        (λ z → Scalar._+_ S
          (sumScalarList S (map (orderedConvectionTerm I u) fibre)) z)
        (sumOrderedTermsOverConcat I A u fibres)))

sumScalarList-resp-pointwise :
  (S : Scalar.ExactOrderedScalar) → (A : ExactFiniteSumAuthority S) →
  {X : Set} → (f g : X → Scalar.Scalar S) →
  ((x : X) → f x ≡ g x) → (xs : List X) →
  sumScalarList S (map f xs) ≡ sumScalarList S (map g xs)
sumScalarList-resp-pointwise S A f g f≡g [] = refl
sumScalarList-resp-pointwise S A f g f≡g (x ∷ xs) =
  cong₂ (Scalar._+_ S) (f≡g x)
    (sumScalarList-resp-pointwise S A f g f≡g xs)

canonicalOrbitInteraction :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  Interaction.ExactNSFourierInteractionStructure S C →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) →
  UnorderedInputOrbit → Scalar.Scalar S
canonicalOrbitInteraction {S = S} I u o with orbitKind o
... | diagonal = orderedConvectionTerm I u (representative o)
... | offDiagonal =
  Scalar._+_ S
    (orderedConvectionTerm I u (representative o))
    (orderedConvectionTerm I u (Lattice.triadSwap (representative o)))

canonicalOrbitInteractionDiagonal :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  (o : UnorderedInputOrbit) →
  orbitKind o ≡ diagonal →
  canonicalOrbitInteraction I u o ≡
  orderedConvectionTerm I u (representative o)
canonicalOrbitInteractionDiagonal I u o h with orbitKind o | h
... | diagonal | refl = refl
... | offDiagonal | ()

canonicalOrbitInteractionOffDiagonal :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  (o : UnorderedInputOrbit) →
  orbitKind o ≡ offDiagonal →
  canonicalOrbitInteraction I u o ≡
  Scalar._+_ S
    (orderedConvectionTerm I u (representative o))
    (orderedConvectionTerm I u (Lattice.triadSwap (representative o)))
canonicalOrbitInteractionOffDiagonal {S = S} I u o h with orbitKind o | h
... | diagonal | ()
... | offDiagonal | refl = refl

canonicalUnorderedTriadInteractionSum :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  Interaction.ExactNSFourierInteractionStructure S C →
  (N R : Nat) →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) → Scalar.Scalar S
canonicalUnorderedTriadInteractionSum {S = S} I N R u =
  sumScalarList S
    (map (canonicalOrbitInteraction I u) (canonicalUnorderedInputOrbits N R))

orbitMemberOrderedSumEqualsCanonicalInteraction :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : ExactFiniteSumAuthority S) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  (o : UnorderedInputOrbit) →
  sumScalarList S (map (orderedConvectionTerm I u) (orbitMembers o)) ≡
  canonicalOrbitInteraction I u o
orbitMemberOrderedSumEqualsCanonicalInteraction {S = S} I A u o
  with orbitKind o
... | diagonal =
  additionIdentityRight S A (orderedConvectionTerm I u (representative o))
... | offDiagonal =
  cong
    (λ z → Scalar._+_ S (orderedConvectionTerm I u (representative o)) z)
    (additionIdentityRight S A
      (orderedConvectionTerm I u (Lattice.triadSwap (representative o))))

flattenedOrbitConvolutionEqualsCanonicalOrbitConvolution :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : ExactFiniteSumAuthority S) →
  (N R : Nat) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  flattenedOrbitCutoffConvection I N R u ≡
  canonicalUnorderedTriadInteractionSum I N R u
flattenedOrbitConvolutionEqualsCanonicalOrbitConvolution
  {S = S} I A N R u =
  trans
    (sumOrderedTermsOverConcat I A u
      (map orbitMembers (canonicalUnorderedInputOrbits N R)))
    (trans
      (cong (sumScalarList S)
        (map-∘
          (λ fibre → sumScalarList S (map (orderedConvectionTerm I u) fibre))
          orbitMembers
          (canonicalUnorderedInputOrbits N R)))
      (sumScalarList-resp-pointwise S A
        (λ o → sumScalarList S (map (orderedConvectionTerm I u) (orbitMembers o)))
        (canonicalOrbitInteraction I u)
        (orbitMemberOrderedSumEqualsCanonicalInteraction I A u)
        (canonicalUnorderedInputOrbits N R)))

rawOrderedCutoffConvolutionEqualsCanonicalOrbitConvolution :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : ExactFiniteSumAuthority S) →
  (N R : Nat) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  cutoffShellConvection I N R u ≡
  canonicalUnorderedTriadInteractionSum I N R u
rawOrderedCutoffConvolutionEqualsCanonicalOrbitConvolution I A N R u =
  trans
    (rawOrderedCutoffConvolutionEqualsFlattenedOrbitConvolution I A N R u)
    (flattenedOrbitConvolutionEqualsCanonicalOrbitConvolution I A N R u)

-- The completed finite reconstruction theorem.  Its right-hand side is
-- indexed by canonical swap orbits, so diagonal input pairs occur once while
-- off-diagonal input pairs contribute their two ordered convolution terms.
finiteTriadExpansionReconstructsCutoffConvection :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : ExactFiniteSumAuthority S) →
  (N R : Nat) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  cutoffShellConvection I N R u ≡
  canonicalUnorderedTriadInteractionSum I N R u
finiteTriadExpansionReconstructsCutoffConvection =
  rawOrderedCutoffConvolutionEqualsCanonicalOrbitConvolution

offDiagonalOrbitMatchesPhysicalInteraction :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : ExactFiniteFourierConvolutionAuthority I) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  (o : UnorderedInputOrbit) →
  orbitKind o ≡ offDiagonal →
  canonicalOrbitInteraction I u o ≡
  Interaction.offDiagonalSymmetrizedInteraction I u (representative o)
offDiagonalOrbitMatchesPhysicalInteraction I A u o h with orbitKind o | h
... | diagonal | ()
... | offDiagonal | refl = sym (orderedPairSymmetrisation I A u (representative o))

-- This is the exact bridge still to be inhabited by the integer-mode
-- enumeration.  `orbitExpansion` is intentionally stated in terms of the
-- raw ordered summand above, so it cannot be satisfied by silently changing
-- the Fourier interaction convention.  In particular, the current two-input
-- formula may only be used off diagonal.  A diagonal interaction is supplied
-- separately and must be one ordered summand, not a doubled bracket.
record OrderedConvolutionOrbitPartition
    {S : Scalar.ExactOrderedScalar} {C : Fourier.ComplexFourierInterface S}
    (I : Interaction.ExactNSFourierInteractionStructure S C)
    (N R : Nat) : Set₁ where
  field
    orbits : List UnorderedInputOrbit
    orbitsAreCanonical :
      orbits ≡ canonicalUnorderedInputOrbits N R
    rawCarrierNoDuplicates :
      Unique.Unique (orderedCutoffConvolutionTriads N R)
    canonicalOrbitsNoDuplicates :
      Unique.Unique (canonicalUnorderedInputOrbits N R)
    representativesInRawCarrier :
      (o : UnorderedInputOrbit) →
      o ∈ canonicalUnorderedInputOrbits N R →
      representative o ∈ orderedCutoffConvolutionTriads N R
    rawCarrierPartition :
      (τ : Lattice.LatticeTriad) →
      τ ∈ orderedCutoffConvolutionTriads N R →
      Σ UnorderedInputOrbit (λ o → InSwapOrbit o τ)
    rawCarrierMapsToCanonicalOrbit :
      (τ : Lattice.LatticeTriad) →
      τ ∈ orderedCutoffConvolutionTriads N R →
      Σ UnorderedInputOrbit (λ o →
        (o ∈ canonicalUnorderedInputOrbits N R) × InSwapOrbit o τ)
    orbitDisjoint :
      {o₁ o₂ : UnorderedInputOrbit} →
      o₁ ∈ canonicalUnorderedInputOrbits N R →
      o₂ ∈ canonicalUnorderedInputOrbits N R →
      (τ : Lattice.LatticeTriad) →
      InSwapOrbit o₁ τ → InSwapOrbit o₂ τ → o₁ ≡ o₂
open OrderedConvolutionOrbitPartition public

canonicalOrderedConvolutionOrbitPartition :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (N R : Nat) → OrderedConvolutionOrbitPartition I N R
canonicalOrderedConvolutionOrbitPartition I N R =
  record
    { orbits = canonicalUnorderedInputOrbits N R
    ; orbitsAreCanonical = refl
    ; rawCarrierNoDuplicates = orderedCutoffConvolutionTriadsUnique N R
    ; canonicalOrbitsNoDuplicates = canonicalUnorderedInputOrbitsUnique N R
    ; representativesInRawCarrier = canonicalOrbitRepresentativeRaw N R
    ; rawCarrierPartition = rawPartition
    ; rawCarrierMapsToCanonicalOrbit = rawMemberMapsToCanonicalOrbit N R
    ; orbitDisjoint = canonicalOrbitOverlapImpliesEqual N R
    }
  where
  rawPartition :
    (τ : Lattice.LatticeTriad) →
    τ ∈ orderedCutoffConvolutionTriads N R →
    Σ UnorderedInputOrbit (λ o → InSwapOrbit o τ)
  rawPartition τ τ∈raw
    with rawMemberMapsToCanonicalOrbit N R τ τ∈raw
  ... | o , o∈canonical , τ∈fibre = o , τ∈fibre

------------------------------------------------------------------------
-- Reindexing target.  The target is fail-closed until the raw-list partition,
-- its orbit-disjointness, and the diagonal/off-diagonal identities are
-- actually constructed.  It is deliberately separate from the later
-- z-weighted Stage-3 energy inequality.
------------------------------------------------------------------------

record FiniteConvolutionReconstruction
    {S : Scalar.ExactOrderedScalar} {C : Fourier.ComplexFourierInterface S}
    (I : Interaction.ExactNSFourierInteractionStructure S C)
    (N R : Nat)
    (sector : Sector.ExactOutputRetainedSectorLaw N R)
    (enumeration : Sector.ExactCutoffRetainedTriadEnumeration N R sector) : Set₁ where
  field
    fourierAlgebra : ExactFiniteFourierConvolutionAuthority I
    orbitPartition : OrderedConvolutionOrbitPartition I N R
    -- This is an equality of finite carriers, expressed as two directions.
    -- The reverse direction is essential: without it a sector could add
    -- interactions which are absent from the direct cutoff convolution.
    retainedSectorMatchesRawConvolution :
      (τ : Lattice.LatticeTriad) →
      τ ∈ orderedCutoffConvolutionTriads N R →
      Sector.retained? sector τ ≡ true
    retainedSectorContainedInRawConvolution :
      (τ : Lattice.LatticeTriad) →
      τ ∈ Sector.exactCutoffRetainedTriads N R sector →
      τ ∈ orderedCutoffConvolutionTriads N R
    reconstruction :
      (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
      cutoffShellConvection I N R u ≡
      canonicalUnorderedTriadInteractionSum I N R u

finiteConvolutionReconstructionClosed : Bool
finiteConvolutionReconstructionClosed = false
