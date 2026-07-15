module DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Bool.Base using (T; _∧_)
open import Data.Bool.Properties using (T-∧)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_; _<_; _∸_; z≤n; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Fin.Base as Fin using (Fin; toℕ; fromℕ<)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.List.Base using (List; cartesianProductWith; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-filter⁺; ∈-filter⁻; ∈-map⁺; ∈-map⁻; ∈-cartesianProductWith⁺; ∈-allFin)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Function.Bundles using (Equivalence)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice

------------------------------------------------------------------------
-- Exact labelled-output retained sector for the periodic Fourier
-- convolution.  Unlike a same-shell triad sector, this is deliberately not
-- cycle invariant: `out` is the distinguished output mode in shell N and
-- `left`, `right` are the two cutoff input modes.  Input swap and reality are
-- the relevant symmetries for the unordered-pair interaction convention.
------------------------------------------------------------------------

cutoffModes : Nat → List Lattice.LatticeMode3
cutoffModes R =
  filterᵇ Lattice.nonzeroMode?
    (Data.List.Base.map (Lattice.decodeCubeCode R) (Lattice.cubeCodes R))

cutoffModesUnique : (R : Nat) → Unique (cutoffModes R)
cutoffModesUnique R =
  UniqueP.filter⁺ (T? ∘ Lattice.nonzeroMode?)
    (UniqueP.map⁺ (Lattice.decodeCubeCodeInjective R)
      (Lattice.cubeCodesUnique R))

-- Membership in `cutoffModes R` is the computational cutoff predicate.  It
-- is deliberately list-based here: a coordinate inequality formulation must
-- include both lower and upper signed bounds.
coordinateInCutoff? : Nat → ℤ → Bool
coordinateInCutoff? R z =
  ((ℤ.- (+ R)) ℤ.≤ᵇ z) ∧ (z ℤ.≤ᵇ (+ R))

inExactCutoff? : Nat → Lattice.LatticeMode3 → Bool
inExactCutoff? R k =
  Lattice.nonzeroMode? k ∧
  (coordinateInCutoff? R (Lattice.k₁ k) ∧
   (coordinateInCutoff? R (Lattice.k₂ k) ∧
    coordinateInCutoff? R (Lattice.k₃ k)))

------------------------------------------------------------------------
-- The signed coordinate decoder is the finite core of the cutoff model.
-- A code in `Fin (2R + 1)` decodes to `code - R`, hence lies in [-R , R].
-- This deliberately works at the integer-order level rather than relying on
-- a cardinality argument, so the inverse enumeration proof can reuse it.
------------------------------------------------------------------------

decodeCoordinateInCutoff :
  (R : Nat) → (i : Fin (Lattice.coordinateCodeBound R)) →
  T (coordinateInCutoff? R (Lattice.decodeCoordinate R i))
decodeCoordinateInCutoff R i =
  Equivalence.from T-∧ (lowerBound , upperBound)
  where
  code≤doubleRadius : Fin.toℕ i ≤ R + R
  code≤doubleRadius = ℕP.m<1+n⇒m≤n (FinP.toℕ<n i)

  substLeft :
    {a b c : ℤ} → a ≡ b → a ℤ.≤ c → b ℤ.≤ c
  substLeft refl p = p

  substRight :
    {a b c : ℤ} → b ≡ c → a ℤ.≤ b → a ℤ.≤ c
  substRight refl p = p

  lowerInteger : (ℤ.- (+ R)) ℤ.≤ (Fin.toℕ i ℤ.⊖ R)
  lowerInteger =
    substRight
      (ℤP.-m+n≡n⊖m R (Fin.toℕ i))
      (substLeft
        (ℤP.+-identityʳ (ℤ.- (+ R)))
        (ℤP.+-monoʳ-≤ (ℤ.- (+ R)) (ℤ.+≤+ z≤n)))

  endpoint : (R + R ℤ.⊖ R) ≡ (+ R)
  endpoint =
    trans
      (ℤP.⊖-≥ (ℕP.m≤m+n R R))
      (cong +_ (ℕP.m+n∸m≡n R R))

  upperEndpoint : (ℤ.- (+ R)) ℤ.+ (+ (R + R)) ≡ (+ R)
  upperEndpoint = trans (ℤP.-m+n≡n⊖m R (R + R)) endpoint

  upperInteger : (Fin.toℕ i ℤ.⊖ R) ℤ.≤ (+ R)
  upperInteger =
    substRight upperEndpoint
      (substLeft
        (ℤP.-m+n≡n⊖m R (Fin.toℕ i))
        (ℤP.+-monoʳ-≤ (ℤ.- (+ R)) (ℤ.+≤+ code≤doubleRadius)))

  lowerBound : T ((ℤ.- (+ R)) ℤ.≤ᵇ (Lattice.decodeCoordinate R i))
  lowerBound = ℤP.≤⇒≤ᵇ lowerInteger

  upperBound : T ((Lattice.decodeCoordinate R i) ℤ.≤ᵇ (+ R))
  upperBound = ℤP.≤⇒≤ᵇ upperInteger

decodeCubeCodeInExactCutoff :
  (R : Nat) → (c : Lattice.CubeCode R) →
  T (Lattice.nonzeroMode? (Lattice.decodeCubeCode R c)) →
  T (inExactCutoff? R (Lattice.decodeCubeCode R c))
decodeCubeCodeInExactCutoff R (i , j , k) nonzero =
  Equivalence.from T-∧
    (nonzero , Equivalence.from T-∧
      (decodeCoordinateInCutoff R i , Equivalence.from T-∧
        (decodeCoordinateInCutoff R j , decodeCoordinateInCutoff R k)))

cutoffModesSound :
  (R : Nat) → (k : Lattice.LatticeMode3) →
  k ∈ cutoffModes R → T (inExactCutoff? R k)
cutoffModesSound R k k∈cutoff
  with ∈-filter⁻ (T? ∘ Lattice.nonzeroMode?)
         {xs = Data.List.Base.map (Lattice.decodeCubeCode R) (Lattice.cubeCodes R)}
         k∈cutoff
... | k∈decoded , nonzero
  with ∈-map⁻ (Lattice.decodeCubeCode R) {xs = Lattice.cubeCodes R} k∈decoded
... | c , c∈cube , k≡decoded
  rewrite k≡decoded = decodeCubeCodeInExactCutoff R c nonzero

-- Constructive inverse of the signed decoder.  Positive coordinates are
-- encoded as `n + R`; negative `-[1+n]` coordinates as `R - (1+n)`.  The
-- bound proof rules out the negative branch at radius zero.
decodeCoordinateComplete :
  (R : Nat) → (z : ℤ) → T (coordinateInCutoff? R z) →
  Σ (Fin (Lattice.coordinateCodeBound R))
    (λ i → Lattice.decodeCoordinate R i ≡ z)
decodeCoordinateComplete R (+ n) z∈ =
  Fin.fromℕ< codeInRange , decoded
  where
  bounds : T ((ℤ.- (+ R)) ℤ.≤ᵇ (+ n)) × T ((+ n) ℤ.≤ᵇ (+ R))
  bounds = Equivalence.to T-∧ z∈

  n≤R : n ≤ R
  n≤R = upperNat (ℤP.≤ᵇ⇒≤ (proj₂ bounds))
    where
    upperNat : (+ n) ℤ.≤ (+ R) → n ≤ R
    upperNat (ℤ.+≤+ p) = p

  code≤doubleRadius : n + R ≤ R + R
  code≤doubleRadius = ℕP.+-monoˡ-≤ R n≤R

  codeInRange : n + R < Lattice.coordinateCodeBound R
  codeInRange = s≤s code≤doubleRadius

  decoded : Lattice.decodeCoordinate R (Fin.fromℕ< codeInRange) ≡ (+ n)
  decoded =
    trans
      (cong (λ m → m ℤ.⊖ R) (FinP.toℕ-fromℕ< codeInRange))
      (trans
        (ℤP.⊖-≥ (ℕP.m≤n+m R n))
        (cong +_ (ℕP.m+n∸n≡m n R)))
decodeCoordinateComplete zero (-[1+ n ]) z∈ =
  ⊥-elim (zeroCannotBoundNegative z∈)
  where
  noZeroLeNegative : (+ zero) ℤ.≤ -[1+ n ] → ⊥
  noZeroLeNegative ()

  zeroCannotBoundNegative :
    T (coordinateInCutoff? zero (-[1+ n ])) → ⊥
  zeroCannotBoundNegative bounded = noZeroLeNegative (ℤP.≤ᵇ⇒≤ lower)
    where
    bounds :
      T ((ℤ.- (+ zero)) ℤ.≤ᵇ -[1+ n ]) ×
      T (-[1+ n ] ℤ.≤ᵇ (+ zero))
    bounds = Equivalence.to T-∧ bounded

    lower : T ((+ zero) ℤ.≤ᵇ -[1+ n ])
    lower = proj₁ bounds
decodeCoordinateComplete (suc R) (-[1+ n ]) z∈ =
  Fin.fromℕ< codeInRange , decoded
  where
  bounds :
    T ((ℤ.- (+ (suc R))) ℤ.≤ᵇ -[1+ n ]) ×
    T (-[1+ n ] ℤ.≤ᵇ (+ (suc R)))
  bounds = Equivalence.to T-∧ z∈

  n≤R : n ≤ R
  n≤R = lowerNat (ℤP.≤ᵇ⇒≤ (proj₁ bounds))
    where
    lowerNat : (ℤ.- (+ (suc R))) ℤ.≤ -[1+ n ] → n ≤ R
    lowerNat (ℤ.-≤- p) = p

  code≤radius : R ∸ n ≤ suc R
  code≤radius = ℕP.≤-trans (ℕP.m∸n≤m R n) (ℕP.n≤1+n R)

  codeInRange : R ∸ n < Lattice.coordinateCodeBound (suc R)
  codeInRange = s≤s (ℕP.≤-trans code≤radius (ℕP.m≤m+n (suc R) (suc R)))

  restoredMagnitude : suc R ∸ (R ∸ n) ≡ suc n
  restoredMagnitude =
    trans
      (cong (λ m → m ∸ (R ∸ n))
        (sym (ℕP.m∸n+n≡m (s≤s n≤R))))
      (ℕP.m+n∸m≡n (R ∸ n) (suc n))

  decoded : Lattice.decodeCoordinate (suc R) (Fin.fromℕ< codeInRange) ≡ -[1+ n ]
  decoded =
    trans
      (cong (λ m → m ℤ.⊖ (suc R)) (FinP.toℕ-fromℕ< codeInRange))
      (trans
        (ℤP.⊖-≤ code≤radius)
        (cong (λ m → ℤ.- (+ m)) restoredMagnitude))

decodeCubeCodeComplete :
  (R : Nat) → (k : Lattice.LatticeMode3) →
  T (coordinateInCutoff? R (Lattice.k₁ k)) →
  T (coordinateInCutoff? R (Lattice.k₂ k)) →
  T (coordinateInCutoff? R (Lattice.k₃ k)) →
  Σ (Lattice.CubeCode R) (λ c → Lattice.decodeCubeCode R c ≡ k)
decodeCubeCodeComplete R (Lattice.mkLatticeMode3 k₁ k₂ k₃) k₁∈ k₂∈ k₃∈
  with decodeCoordinateComplete R k₁ k₁∈
     | decodeCoordinateComplete R k₂ k₂∈
     | decodeCoordinateComplete R k₃ k₃∈
... | i , i≡ | j , j≡ | k , k≡
  rewrite sym i≡ | sym j≡ | sym k≡ = (i , j , k) , refl

cutoffModesComplete :
  (R : Nat) → (k : Lattice.LatticeMode3) →
  T (inExactCutoff? R k) → k ∈ cutoffModes R
cutoffModesComplete R k k∈exact =
  finish firstCoordinate secondCoordinate thirdCoordinate nonzero
  where
  splitOuter :
    T (Lattice.nonzeroMode? k) ×
    T (coordinateInCutoff? R (Lattice.k₁ k) ∧
      (coordinateInCutoff? R (Lattice.k₂ k) ∧
       coordinateInCutoff? R (Lattice.k₃ k)))
  splitOuter = Equivalence.to T-∧ k∈exact

  nonzero : T (Lattice.nonzeroMode? k)
  nonzero = proj₁ splitOuter

  splitCoordinates :
    T (coordinateInCutoff? R (Lattice.k₁ k)) ×
    T (coordinateInCutoff? R (Lattice.k₂ k) ∧ coordinateInCutoff? R (Lattice.k₃ k))
  splitCoordinates = Equivalence.to T-∧ (proj₂ splitOuter)

  firstCoordinate : T (coordinateInCutoff? R (Lattice.k₁ k))
  firstCoordinate = proj₁ splitCoordinates

  finalCoordinates :
    T (coordinateInCutoff? R (Lattice.k₂ k)) × T (coordinateInCutoff? R (Lattice.k₃ k))
  finalCoordinates = Equivalence.to T-∧ (proj₂ splitCoordinates)

  secondCoordinate : T (coordinateInCutoff? R (Lattice.k₂ k))
  secondCoordinate = proj₁ finalCoordinates

  thirdCoordinate : T (coordinateInCutoff? R (Lattice.k₃ k))
  thirdCoordinate = proj₂ finalCoordinates

  substMembership :
    {a b : Lattice.LatticeMode3} → a ≡ b → b ∈ cutoffModes R → a ∈ cutoffModes R
  substMembership refl p = p

  cubeMember : (c : Lattice.CubeCode R) → c ∈ Lattice.cubeCodes R
  cubeMember c = ∈-cartesianProductWith⁺ _,_ (∈-allFin (proj₁ c))
    (∈-cartesianProductWith⁺ _,_ (∈-allFin (proj₁ (proj₂ c)))
      (∈-allFin (proj₂ (proj₂ c))))

  decoded∈cube : (c : Lattice.CubeCode R) → Lattice.decodeCubeCode R c ∈
    Data.List.Base.map (Lattice.decodeCubeCode R) (Lattice.cubeCodes R)
  decoded∈cube c = ∈-map⁺ (Lattice.decodeCubeCode R) (cubeMember c)

  nonzeroAtDecoded :
    (c : Lattice.CubeCode R) → Lattice.decodeCubeCode R c ≡ k →
    T (Lattice.nonzeroMode? k) → T (Lattice.nonzeroMode? (Lattice.decodeCubeCode R c))
  nonzeroAtDecoded c refl p = p

  finish :
    T (coordinateInCutoff? R (Lattice.k₁ k)) →
    T (coordinateInCutoff? R (Lattice.k₂ k)) →
    T (coordinateInCutoff? R (Lattice.k₃ k)) →
    T (Lattice.nonzeroMode? k) → k ∈ cutoffModes R
  finish k₁∈ k₂∈ k₃∈ nonzero
    with decodeCubeCodeComplete R k k₁∈ k₂∈ k₃∈
  ... | c , decoded =
    substMembership (sym decoded)
      (∈-filter⁺ (T? ∘ Lattice.nonzeroMode?) (decoded∈cube c)
        (nonzeroAtDecoded c decoded nonzero))

-- Geometric monotonicity of the exact integer cube.  This is independent of
-- its finite decoder/list representation and is the order-theoretic part of
-- the `R ≤ M` cutoff inclusion needed by the outer-window decomposition.
coordinateInCutoffMonotone :
  (R M : Nat) → R ≤ M → (z : ℤ) →
  T (coordinateInCutoff? R z) → T (coordinateInCutoff? M z)
coordinateInCutoffMonotone R M R≤M z z∈R =
  Equivalence.from T-∧
    (ℤP.≤⇒≤ᵇ lowerBound , ℤP.≤⇒≤ᵇ upperBound)
  where
  boundsR : T ((ℤ.- (+ R)) ℤ.≤ᵇ z) × T (z ℤ.≤ᵇ (+ R))
  boundsR = Equivalence.to T-∧ z∈R

  radiusMonotone : (+ R) ℤ.≤ (+ M)
  radiusMonotone = ℤ.+≤+ R≤M

  negativeRadiusAntitone : (ℤ.- (+ M)) ℤ.≤ (ℤ.- (+ R))
  negativeRadiusAntitone =
    ℤP.neg-mono-≤ {x = + R} {y = + M} radiusMonotone

  lowerBound : (ℤ.- (+ M)) ℤ.≤ z
  lowerBound = ℤP.≤-trans negativeRadiusAntitone (ℤP.≤ᵇ⇒≤ (proj₁ boundsR))

  upperBound : z ℤ.≤ (+ M)
  upperBound = ℤP.≤-trans (ℤP.≤ᵇ⇒≤ (proj₂ boundsR)) radiusMonotone

inExactCutoffMonotone :
  (R M : Nat) → R ≤ M → (k : Lattice.LatticeMode3) →
  T (inExactCutoff? R k) → T (inExactCutoff? M k)
inExactCutoffMonotone R M R≤M k k∈R =
  Equivalence.from T-∧
    (nonzero , Equivalence.from T-∧
      (coordinateInCutoffMonotone R M R≤M (Lattice.k₁ k) firstCoordinate
      , Equivalence.from T-∧
        (coordinateInCutoffMonotone R M R≤M (Lattice.k₂ k) secondCoordinate
        , coordinateInCutoffMonotone R M R≤M (Lattice.k₃ k) thirdCoordinate)))
  where
  splitOuter :
    T (Lattice.nonzeroMode? k) ×
    T (coordinateInCutoff? R (Lattice.k₁ k) ∧
      (coordinateInCutoff? R (Lattice.k₂ k) ∧
       coordinateInCutoff? R (Lattice.k₃ k)))
  splitOuter = Equivalence.to T-∧ k∈R

  nonzero : T (Lattice.nonzeroMode? k)
  nonzero = proj₁ splitOuter

  splitCoordinates :
    T (coordinateInCutoff? R (Lattice.k₁ k)) ×
    T (coordinateInCutoff? R (Lattice.k₂ k) ∧
      coordinateInCutoff? R (Lattice.k₃ k))
  splitCoordinates = Equivalence.to T-∧ (proj₂ splitOuter)

  firstCoordinate : T (coordinateInCutoff? R (Lattice.k₁ k))
  firstCoordinate = proj₁ splitCoordinates

  finalCoordinates :
    T (coordinateInCutoff? R (Lattice.k₂ k)) ×
    T (coordinateInCutoff? R (Lattice.k₃ k))
  finalCoordinates = Equivalence.to T-∧ (proj₂ splitCoordinates)

  secondCoordinate : T (coordinateInCutoff? R (Lattice.k₂ k))
  secondCoordinate = proj₁ finalCoordinates

  thirdCoordinate : T (coordinateInCutoff? R (Lattice.k₃ k))
  thirdCoordinate = proj₂ finalCoordinates

-- The finite decoder/list theorem is deliberately separate from geometric
-- monotonicity.  Its two directions are exactly what is needed to move a
-- physical mode between the list carrier and the signed-coordinate cube.
-- Keeping this fail-closed prevents `cutoffModes` from being treated as an
-- exact cube enumeration merely by its definition.
record ExactCutoffModeEnumeration (R : Nat) : Set where
  field
    memberSound :
      (k : Lattice.LatticeMode3) → k ∈ cutoffModes R →
      T (inExactCutoff? R k)
    memberComplete :
      (k : Lattice.LatticeMode3) → T (inExactCutoff? R k) →
      k ∈ cutoffModes R

-- Soundness is now internal to the concrete decoder/list construction.  The
-- only outstanding half of exact enumeration is the inverse signed encoder
-- used to discharge `memberComplete`.
exactCutoffModeEnumerationFromComplete :
  (R : Nat) →
  ((k : Lattice.LatticeMode3) → T (inExactCutoff? R k) → k ∈ cutoffModes R) →
  ExactCutoffModeEnumeration R
exactCutoffModeEnumerationFromComplete R complete = record
  { memberSound = cutoffModesSound R
  ; memberComplete = complete
  }

exactCutoffModeEnumeration : (R : Nat) → ExactCutoffModeEnumeration R
exactCutoffModeEnumeration R =
  exactCutoffModeEnumerationFromComplete R (cutoffModesComplete R)

cutoffModesMonotone :
  (R M : Nat) → R ≤ M →
  ExactCutoffModeEnumeration R → ExactCutoffModeEnumeration M →
  (k : Lattice.LatticeMode3) → k ∈ cutoffModes R → k ∈ cutoffModes M
cutoffModesMonotone R M R≤M enumR enumM k k∈R =
  ExactCutoffModeEnumeration.memberComplete enumM k
    (inExactCutoffMonotone R M R≤M k
      (ExactCutoffModeEnumeration.memberSound enumR k k∈R))

physicalRetainedSector? : Nat → Nat → Lattice.LatticeTriad → Bool
physicalRetainedSector? N R τ =
  Lattice.zeroSum? τ ∧
  (Lattice.inExactShell? N (Lattice.out τ) ∧
   (inExactCutoff? R (Lattice.left τ) ∧ inExactCutoff? R (Lattice.right τ)))

record ExactOutputRetainedSectorLaw (N R : Nat) : Set₁ where
  field
    retained? : Lattice.LatticeTriad → Bool
    inputSwapInvariant :
      (τ : Lattice.LatticeTriad) → retained? (Lattice.triadSwap τ) ≡ retained? τ
    realityInvariant :
      (τ : Lattice.LatticeTriad) → retained? (Lattice.triadNeg τ) ≡ retained? τ
    zeroSumRequired :
      (τ : Lattice.LatticeTriad) → retained? τ ≡ true → Lattice.zeroSum? τ ≡ true
    outputShellRequired :
      (τ : Lattice.LatticeTriad) → retained? τ ≡ true →
      Lattice.inExactShell? N (Lattice.out τ) ≡ true

open ExactOutputRetainedSectorLaw public

physicalOutputSectorCandidates : Nat → Nat → List Lattice.LatticeTriad
physicalOutputSectorCandidates N R =
  cartesianProductWith
    (λ left pair → Lattice.mkLatticeTriad left
      (Data.Product.proj₁ pair) (Data.Product.proj₂ pair))
    (cutoffModes R)
    (cartesianProductWith _,_ (cutoffModes R) (Lattice.exactShellModes N))

exactCutoffRetainedTriads :
  (N R : Nat) → ExactOutputRetainedSectorLaw N R → List Lattice.LatticeTriad
exactCutoffRetainedTriads N R sector =
  filterᵇ (retained? sector) (physicalOutputSectorCandidates N R)

OutputRetainedTriadMember :
  (N R : Nat) → ExactOutputRetainedSectorLaw N R → Lattice.LatticeTriad → Set
OutputRetainedTriadMember N R sector τ =
  τ ∈ exactCutoffRetainedTriads N R sector

-- The following is the exact PDE-facing enumeration obligation.  It includes
-- the completeness statement within a finite cutoff and leaves the R → ∞
-- passage explicitly downstream.
record ExactCutoffRetainedTriadEnumeration
    (N R : Nat) (sector : ExactOutputRetainedSectorLaw N R) : Set₁ where
  field
    triads : List Lattice.LatticeTriad
    triadsAreExact : triads ≡ exactCutoffRetainedTriads N R sector
    sound : (τ : Lattice.LatticeTriad) → τ ∈ triads → retained? sector τ ≡ true
    completeWithinCutoff :
      (τ : Lattice.LatticeTriad) →
      τ ∈ physicalOutputSectorCandidates N R → retained? sector τ ≡ true → τ ∈ triads

physicalOutputSectorClosed : Bool
physicalOutputSectorClosed = false
