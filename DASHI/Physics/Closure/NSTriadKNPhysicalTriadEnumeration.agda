module DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
open Cube using (_∈_; _∉_; NoDuplicates; unique[]; unique∷)

------------------------------------------------------------------------
-- Actual finite resonant triads over the literal cutoff cube.
--
-- The primitive incidence contains only the lattice modes and exact
-- resonance.  Cutoff membership, nonzero conditions and reality policy are
-- separate derived layers; this prevents one lattice triad from being
-- silently identified with a phase- or polarisation-resolved state.
------------------------------------------------------------------------

infixr 6 _&&_

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

data BoolInspection (b : Bool) : Set where
  inspected : (value : Bool) → b ≡ value → BoolInspection b

inspectBool : (b : Bool) → BoolInspection b
inspectBool b = inspected b refl

andTrueLeft : ∀ {a b} → a && b ≡ true → a ≡ true
andTrueLeft {true} proof = refl
andTrueLeft {false} ()

andTrueRight : ∀ {a b} → a && b ≡ true → b ≡ true
andTrueRight {true} proof = proof
andTrueRight {false} ()

andTrueMiddle : ∀ {a b c} → a && (b && c) ≡ true → b ≡ true
andTrueMiddle {a = a} {b = b} {c = c} proof =
  andTrueLeft {a = b} {b = c}
    (andTrueRight {a = a} {b = b && c} proof)

andTrueLast : ∀ {a b c} → a && (b && c) ≡ true → c ≡ true
andTrueLast {a = a} {b = b} {c = c} proof =
  andTrueRight {a = b} {b = c}
    (andTrueRight {a = a} {b = b && c} proof)

natLeBool : Nat → Nat → Bool
natLeBool zero n = true
natLeBool (suc m) zero = false
natLeBool (suc m) (suc n) = natLeBool m n

natLeBoolSound :
  ∀ {m n} → natLeBool m n ≡ true → m Cube.≤ᴺ n
natLeBoolSound {zero} proof = Cube.z≤n
natLeBoolSound {suc m} {zero} ()
natLeBoolSound {suc m} {suc n} proof =
  Cube.s≤s (natLeBoolSound proof)

natLeBoolComplete :
  ∀ {m n} → m Cube.≤ᴺ n → natLeBool m n ≡ true
natLeBoolComplete Cube.z≤n = refl
natLeBoolComplete (Cube.s≤s proof) = natLeBoolComplete proof

modeWithinCutoff : Nat → Z3.FourierMode → Bool
modeWithinCutoff N k =
  natLeBool (Cube.integerMagnitude (Z3.kx k)) N
  &&
  (natLeBool (Cube.integerMagnitude (Z3.ky k)) N
  && natLeBool (Cube.integerMagnitude (Z3.kz k)) N)

modeWithinCutoffSound :
  ∀ N k → modeWithinCutoff N k ≡ true → Cube.InCutoffCube N k
modeWithinCutoffSound N k proof =
  Cube.cutoff-membership
    (Cube.intervalComplete
      (natLeBoolSound (andTrueLeft proof)))
    (Cube.intervalComplete
      (natLeBoolSound
        (andTrueMiddle
          {a = natLeBool (Cube.integerMagnitude (Z3.kx k)) N}
          {b = natLeBool (Cube.integerMagnitude (Z3.ky k)) N}
          {c = natLeBool (Cube.integerMagnitude (Z3.kz k)) N}
          proof)))
    (Cube.intervalComplete
      (natLeBoolSound
        (andTrueLast
          {a = natLeBool (Cube.integerMagnitude (Z3.kx k)) N}
          {b = natLeBool (Cube.integerMagnitude (Z3.ky k)) N}
          {c = natLeBool (Cube.integerMagnitude (Z3.kz k)) N}
          proof)))

modeWithinCutoffComplete :
  ∀ {N k} → Cube.InCutoffCube N k → modeWithinCutoff N k ≡ true
modeWithinCutoffComplete membership
  rewrite natLeBoolComplete
    (Cube.intervalMagnitudeBound (Cube.x-member membership))
        | natLeBoolComplete
    (Cube.intervalMagnitudeBound (Cube.y-member membership))
        | natLeBoolComplete
    (Cube.intervalMagnitudeBound (Cube.z-member membership))
  = refl

record PhysicalTriadIncidence : Set where
  constructor physicalTriad
  field
    p q k : Z3.FourierMode
    resonance : Z3.addMode p q ≡ k

open PhysicalTriadIncidence public

record PhysicalTriadInCutoff
    (N : Nat) (τ : PhysicalTriadIncidence) : Set where
  constructor triad-in-cutoff
  field
    pBounded : p τ ∈ Cube.cutoffModes N
    qBounded : q τ ∈ Cube.cutoffModes N
    kBounded : k τ ∈ Cube.cutoffModes N

open PhysicalTriadInCutoff public

record NonZeroPhysicalTriad (τ : PhysicalTriadIncidence) : Set where
  constructor nonzero-triad
  field
    pNonzero : Z3.NonZeroMode (p τ)
    qNonzero : Z3.NonZeroMode (q τ)
    kNonzero : Z3.NonZeroMode (k τ)

open NonZeroPhysicalTriad public

nonZeroPhysicalTriadExcludesPZero :
  ∀ {τ} → NonZeroPhysicalTriad τ → p τ ≡ Z3.zeroMode → ⊥
nonZeroPhysicalTriadExcludesPZero proof =
  Z3.NonZeroMode.notZero (pNonzero proof)

nonZeroPhysicalTriadExcludesQZero :
  ∀ {τ} → NonZeroPhysicalTriad τ → q τ ≡ Z3.zeroMode → ⊥
nonZeroPhysicalTriadExcludesQZero proof =
  Z3.NonZeroMode.notZero (qNonzero proof)

nonZeroPhysicalTriadExcludesKZero :
  ∀ {τ} → NonZeroPhysicalTriad τ → k τ ≡ Z3.zeroMode → ⊥
nonZeroPhysicalTriadExcludesKZero proof =
  Z3.NonZeroMode.notZero (kNonzero proof)

triadInputPair :
  PhysicalTriadIncidence →
  Cube.Pair Z3.FourierMode Z3.FourierMode
triadInputPair τ = Cube.pair (p τ) (q τ)

pairTriad :
  Cube.Pair Z3.FourierMode Z3.FourierMode →
  PhysicalTriadIncidence
pairTriad pair =
  physicalTriad
    (Cube.first pair)
    (Cube.second pair)
    (Z3.addMode (Cube.first pair) (Cube.second pair))
    refl

pairTriadRoundtrip :
  ∀ pair → triadInputPair (pairTriad pair) ≡ pair
pairTriadRoundtrip (Cube.pair p q) = refl

enumerateFromPairs :
  Nat →
  List (Cube.Pair Z3.FourierMode Z3.FourierMode) →
  List PhysicalTriadIncidence
enumerateFromPairs N [] = []
enumerateFromPairs N (pair ∷ pairs)
  with modeWithinCutoff N
    (Z3.addMode (Cube.first pair) (Cube.second pair))
... | true = pairTriad pair ∷ enumerateFromPairs N pairs
... | false = enumerateFromPairs N pairs

physicalTriadEnumeration : Nat → List PhysicalTriadIncidence
physicalTriadEnumeration N =
  enumerateFromPairs N
    (Cube.cartesian (Cube.cutoffModes N) (Cube.cutoffModes N))

enumeratedPairMember :
  ∀ {N pairs τ} →
  τ ∈ enumerateFromPairs N pairs →
  triadInputPair τ ∈ pairs
enumeratedPairMember {pairs = []} ()
enumeratedPairMember {N} {pairs = pair ∷ pairs} member
  with modeWithinCutoff N
    (Z3.addMode (Cube.first pair) (Cube.second pair)) | member
... | true | Cube.here equality =
      Cube.here (cong triadInputPair equality)
... | true | Cube.there tail =
      Cube.there (enumeratedPairMember tail)
... | false | member =
      Cube.there (enumeratedPairMember member)

mutual
  enumeratedOutputWithin :
    ∀ {N pairs τ} →
    τ ∈ enumerateFromPairs N pairs →
    modeWithinCutoff N (k τ) ≡ true
  enumeratedOutputWithin {pairs = []} ()
  enumeratedOutputWithin {N} {pairs = pair ∷ pairs} {τ = τ} member
    with modeWithinCutoff N
        (Z3.addMode (Cube.first pair) (Cube.second pair)) in cutoffProof
  ... | true = trueOutputMember N pair pairs cutoffProof member
  ... | false = falseOutputMember N pair pairs member

  trueOutputMember :
    (N : Nat)
    (pair : Cube.Pair Z3.FourierMode Z3.FourierMode)
    (pairs : List (Cube.Pair Z3.FourierMode Z3.FourierMode))
    (proof : modeWithinCutoff N
    (Z3.addMode (Cube.first pair) (Cube.second pair)) ≡ true) →
    ∀ {τ} →
    τ ∈ (pairTriad pair ∷ enumerateFromPairs N pairs) →
    modeWithinCutoff N (k τ) ≡ true
  trueOutputMember N pair pairs proof (Cube.here equality) =
    subst
      (λ output → modeWithinCutoff N output ≡ true)
      (sym (cong k equality))
      proof
  trueOutputMember N pair pairs proof (Cube.there tail) =
    enumeratedOutputWithin {N = N} tail

  falseOutputMember :
    (N : Nat)
    (pair : Cube.Pair Z3.FourierMode Z3.FourierMode)
    (pairs : List (Cube.Pair Z3.FourierMode Z3.FourierMode)) →
    ∀ {τ} →
    τ ∈ enumerateFromPairs N pairs →
    modeWithinCutoff N (k τ) ≡ true
  falseOutputMember N pair pairs member =
    enumeratedOutputWithin {N = N} member

enumerateFromPairsComplete :
  ∀ {N pairs pair} →
  pair ∈ pairs →
  modeWithinCutoff N
    (Z3.addMode (Cube.first pair) (Cube.second pair)) ≡ true →
  pairTriad pair ∈ enumerateFromPairs N pairs
enumerateFromPairsComplete {pairs = []} () within
enumerateFromPairsComplete {N} {pairs = head ∷ tails}
  (Cube.here refl) within
  with modeWithinCutoff N
    (Z3.addMode (Cube.first head) (Cube.second head))
... | true = Cube.here refl
... | false with within
...   | ()
enumerateFromPairsComplete {N} {pairs = head ∷ tails}
  (Cube.there member) within
  with modeWithinCutoff N
    (Z3.addMode (Cube.first head) (Cube.second head))
... | true = Cube.there (enumerateFromPairsComplete member within)
... | false = enumerateFromPairsComplete member within

enumerateFromPairsNoDuplicates :
  ∀ N {pairs} →
  NoDuplicates pairs →
  NoDuplicates (enumerateFromPairs N pairs)
enumerateFromPairsNoDuplicates N unique[] = unique[]
enumerateFromPairsNoDuplicates N
  (unique∷ {x = pair} {xs = pairs} pairFresh rest)
  with modeWithinCutoff N
    (Z3.addMode (Cube.first pair) (Cube.second pair))
... | true =
  unique∷ headFresh (enumerateFromPairsNoDuplicates N rest)
  where
  headFresh : pairTriad pair ∉ enumerateFromPairs N pairs
  headFresh member =
    pairFresh
      (subst
        (λ inputPair → inputPair ∈ pairs)
        (pairTriadRoundtrip pair)
        (enumeratedPairMember member))
... | false = enumerateFromPairsNoDuplicates N rest

physicalTriadEnumerationNoDuplicates :
  ∀ N → NoDuplicates (physicalTriadEnumeration N)
physicalTriadEnumerationNoDuplicates N =
  enumerateFromPairsNoDuplicates N
    (Cube.cartesianNoDuplicates
      (Cube.cutoffModeEnumerationNoDuplicates N)
      (Cube.cutoffModeEnumerationNoDuplicates N))

physicalTriadEnumerationResonanceSound :
  ∀ {N τ} → τ ∈ physicalTriadEnumeration N →
  Z3.addMode (p τ) (q τ) ≡ k τ
physicalTriadEnumerationResonanceSound {τ = τ} member =
  resonance τ

physicalTriadEnumerationCutoffSound :
  ∀ {N τ} → τ ∈ physicalTriadEnumeration N →
  PhysicalTriadInCutoff N τ
physicalTriadEnumerationCutoffSound {N} {τ} member =
  triad-in-cutoff
    (Cube.cartesianFirstMember pairMember)
    (Cube.cartesianSecondMember pairMember)
    (Cube.cutoffModeEnumerationComplete N (k τ)
      (modeWithinCutoffSound N (k τ)
        (enumeratedOutputWithin {N = N} {τ = τ} member)))
  where
  pairMember :
    triadInputPair τ ∈
      Cube.cartesian (Cube.cutoffModes N) (Cube.cutoffModes N)
  pairMember = enumeratedPairMember member

record PhysicalTriadEnumerationHit
    (N : Nat) (τ : PhysicalTriadIncidence) : Set where
  constructor enumeration-hit
  field
    representative : PhysicalTriadIncidence
    representativeListed :
      representative ∈ physicalTriadEnumeration N
    sameP : p representative ≡ p τ
    sameQ : q representative ≡ q τ
    sameK : k representative ≡ k τ

open PhysicalTriadEnumerationHit public

physicalTriadEnumerationComplete :
  ∀ {N τ} →
  PhysicalTriadInCutoff N τ →
  PhysicalTriadEnumerationHit N τ
physicalTriadEnumerationComplete {N} {τ} bounded =
  enumeration-hit
    representativeValue
    representativeValueIsListed
    refl
    refl
    (resonance τ)
  where
  inputPair : Cube.Pair Z3.FourierMode Z3.FourierMode
  inputPair = Cube.pair (p τ) (q τ)

  inputPairListed :
    inputPair ∈
      Cube.cartesian (Cube.cutoffModes N) (Cube.cutoffModes N)
  inputPairListed =
    Cube.cartesianComplete (pBounded bounded) (qBounded bounded)

  outputWithin :
    modeWithinCutoff N (Z3.addMode (p τ) (q τ)) ≡ true
  outputWithin =
    subst
      (λ output → modeWithinCutoff N output ≡ true)
      (sym (resonance τ))
      (modeWithinCutoffComplete
        (Cube.cutoffModeEnumerationSound N (k τ) (kBounded bounded)))

  representativeValue : PhysicalTriadIncidence
  representativeValue = pairTriad inputPair

  representativeValueIsListed :
    representativeValue ∈ physicalTriadEnumeration N
  representativeValueIsListed =
    enumerateFromPairsComplete inputPairListed outputWithin

------------------------------------------------------------------------
-- Reality is handled at the lattice-carrier layer.  The cutoff cube is closed
-- under k ↦ -k and contains the fixed zero mode exactly once.  A later
-- phase/polarisation state may quotient or orient these conjugate orbits, but
-- the primitive triad enumeration does not silently choose such a quotient.
------------------------------------------------------------------------

record PhysicalTriadRealityPolicy (N : Nat) : Set where
  constructor physical-reality-policy
  field
    carrierNegationClosed :
      ∀ mode → mode ∈ Cube.cutoffModes N →
      Z3.negateMode mode ∈ Cube.cutoffModes N
    zeroModeHandledExactlyOnce :
      Cube.ZeroModeHandledExactlyOnce N

open PhysicalTriadRealityPolicy public

literalCutoffRealityPolicy :
  ∀ N → PhysicalTriadRealityPolicy N
literalCutoffRealityPolicy N =
  physical-reality-policy
    (Cube.cutoffClosedUnderNegation N)
    (Cube.zeroModeHandledExactlyOnce N)

physicalTriadEnumerationImplemented : Bool
physicalTriadEnumerationImplemented = true

physicalTriadEnumerationImplementedIsTrue :
  physicalTriadEnumerationImplemented ≡ true
physicalTriadEnumerationImplementedIsTrue = refl

physicalTriadEnumerationDuplicateFree : Bool
physicalTriadEnumerationDuplicateFree = true

physicalTriadEnumerationDuplicateFreeIsTrue :
  physicalTriadEnumerationDuplicateFree ≡ true
physicalTriadEnumerationDuplicateFreeIsTrue = refl

physicalTriadRealityPolicyImplemented : Bool
physicalTriadRealityPolicyImplemented = true

physicalTriadRealityPolicyImplementedIsTrue :
  physicalTriadRealityPolicyImplemented ≡ true
physicalTriadRealityPolicyImplementedIsTrue = refl
