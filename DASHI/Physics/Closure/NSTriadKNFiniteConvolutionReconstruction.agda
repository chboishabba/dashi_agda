module DASHI.Physics.Closure.NSTriadKNFiniteConvolutionReconstruction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; map; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Integer.Properties as ℤP using (+-comm)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans)

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

filterMemberSound :
  {A : Set} → (P : A → Bool) → (x : A) → (xs : List A) →
  x ∈ filterᵇ P xs → (P x ≡ true) × (x ∈ xs)
filterMemberSound P x [] ()
filterMemberSound P x (y ∷ ys) x∈ with P y in Py | x∈
... | true | here refl = Py , here refl
... | true | there x∈tail =
  Data.Product.proj₁ tailFacts , there (Data.Product.proj₂ tailFacts)
  where
  tailFacts = filterMemberSound P x ys x∈tail
... | false | here ()
... | false | there x∈tail =
  Data.Product.proj₁ tailFacts , there (Data.Product.proj₂ tailFacts)
  where
  tailFacts = filterMemberSound P x ys x∈tail

filterMemberComplete :
  {A : Set} → (P : A → Bool) → (x : A) → (xs : List A) →
  x ∈ xs → P x ≡ true → x ∈ filterᵇ P xs
filterMemberComplete P x [] () _
filterMemberComplete P x (y ∷ ys) (here x≡y) Px
  with P y
... | true = here x≡y
... | false = ⊥-elim (λ ())
filterMemberComplete P x (y ∷ ys) (there x∈ys) Px with P y
... | true = there (filterMemberComplete P x ys x∈ys Px)
... | false = filterMemberComplete P x ys x∈ys Px

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
    (trans (zeroSumSwapInvariant τ) zeroSum)
  where
  rawFacts :
    (Lattice.zeroSum? τ ≡ true) × RawCutoffCandidate N R τ
  rawFacts =
    filterMemberSound Lattice.zeroSum? τ
      (Sector.physicalOutputSectorCandidates N R) τ∈raw

  zeroSum : Lattice.zeroSum? τ ≡ true
  zeroSum = Data.Product.proj₁ rawFacts

  rawCandidate : RawCutoffCandidate N R τ
  rawCandidate = Data.Product.proj₂ rawFacts

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
        (Fourier.conjugateVector C (u (Lattice.out τ)))
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
  Interaction.physicalInteractionCoefficient I u τ ≡
  Scalar._+_ S
    (orderedConvectionTerm I u τ)
    (orderedConvectionTerm I u (Lattice.triadSwap τ))
orderedPairSymmetrisation {S = S} {C = C} I A u
  (Lattice.mkLatticeTriad p q r) =
  negativeRealInnerLerayAdd I A
    (Fourier.conjugateVector C (u r))
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

insertSwapOrbitRepresentative :
  Lattice.LatticeTriad → List Lattice.LatticeTriad → List Lattice.LatticeTriad
insertSwapOrbitRepresentative τ reps
  with triadMember? τ reps | triadMember? (Lattice.triadSwap τ) reps
... | true | _ = reps
... | false | true = reps
... | false | false = τ ∷ reps

canonicalUnorderedInputRepresentatives :
  List Lattice.LatticeTriad → List Lattice.LatticeTriad
canonicalUnorderedInputRepresentatives [] = []
canonicalUnorderedInputRepresentatives (τ ∷ τs) =
  insertSwapOrbitRepresentative τ (canonicalUnorderedInputRepresentatives τs)

canonicalUnorderedInputOrbits : Nat → Nat → List UnorderedInputOrbit
canonicalUnorderedInputOrbits N R =
  map mkUnorderedInputOrbit
    (canonicalUnorderedInputRepresentatives
      (orderedCutoffConvolutionTriads N R))

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

canonicalUnorderedTriadInteractionSum :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  Interaction.ExactNSFourierInteractionStructure S C →
  (N R : Nat) →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) → Scalar.Scalar S
canonicalUnorderedTriadInteractionSum {S = S} I N R u =
  sumScalarList S
    (map (canonicalOrbitInteraction I u) (canonicalUnorderedInputOrbits N R))

offDiagonalOrbitMatchesPhysicalInteraction :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : ExactFiniteFourierConvolutionAuthority I) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  (o : UnorderedInputOrbit) →
  orbitKind o ≡ offDiagonal →
  canonicalOrbitInteraction I u o ≡
  Interaction.physicalInteractionCoefficient I u (representative o)
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
    representativesInRawCarrier :
      (o : UnorderedInputOrbit) →
      representative o ∈ orderedCutoffConvolutionTriads N R
    rawCarrierPartition :
      (τ : Lattice.LatticeTriad) →
      τ ∈ orderedCutoffConvolutionTriads N R →
      Σ UnorderedInputOrbit (λ o → InSwapOrbit o τ)
    orbitDisjoint :
      {o₁ o₂ : UnorderedInputOrbit} →
      (τ : Lattice.LatticeTriad) →
      InSwapOrbit o₁ τ → InSwapOrbit o₂ τ → o₁ ≡ o₂
open OrderedConvolutionOrbitPartition public

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
