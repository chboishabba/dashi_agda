module DASHI.Analysis.RiemannPrimePowerCounting where

-- Riemann's symmetric prime-power counting function J₀(x) / Π₀(x).
--
-- Every prime power p^k contributes 1/k.  At a discontinuity x = p^k the
-- endpoint contribution is halved.  The finite enumerator is proof-bearing:
-- strict and endpoint occurrences must be sound, complete, and duplicate-free.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (_<_)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.PrimeCountingFunction
open import DASHI.Analysis.RiemannVonMangoldtSpecification
open import DASHI.Analysis.ChebyshevPrimeCounting using (IntegerRootFloor)

data PrimePowerOccurrence
  (space : WeilTestSpace)
  (arithmetic : AllPrimeArithmetic space) : Set where
  occurrence :
    AllPrimeArithmetic.Prime arithmetic →
    Nat →
    PrimePowerOccurrence space arithmetic

occurrencePrime :
  {space : WeilTestSpace} →
  {arithmetic : AllPrimeArithmetic space} →
  PrimePowerOccurrence space arithmetic →
  AllPrimeArithmetic.Prime arithmetic
occurrencePrime (occurrence p exponentIndex) = p

occurrenceExponentIndex :
  {space : WeilTestSpace} →
  {arithmetic : AllPrimeArithmetic space} →
  PrimePowerOccurrence space arithmetic →
  Nat
occurrenceExponentIndex (occurrence p exponentIndex) = exponentIndex

occurrenceValue :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  PrimePowerOccurrence space arithmetic →
  Nat
occurrenceValue space arithmetic (occurrence p exponentIndex) =
  primePowerNat space arithmetic p exponentIndex

data OccurrenceMember
  {space : WeilTestSpace}
  {arithmetic : AllPrimeArithmetic space}
  (power : PrimePowerOccurrence space arithmetic) :
  List (PrimePowerOccurrence space arithmetic) → Set where
  occurrenceHere :
    {powers : List (PrimePowerOccurrence space arithmetic)} →
    OccurrenceMember power (power ∷ powers)
  occurrenceThere :
    {other : PrimePowerOccurrence space arithmetic} →
    {powers : List (PrimePowerOccurrence space arithmetic)} →
    OccurrenceMember power powers →
    OccurrenceMember power (other ∷ powers)

record PrimePowerCountingScalar (space : WeilTestSpace) : Set₁ where
  open WeilTestSpace space
  field
    _*S_ : Scalar → Scalar → Scalar
    halfS : Scalar → Scalar
    natLift : Nat → Scalar
    unitFraction : Nat → Scalar

occurrenceWeight :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  PrimePowerCountingScalar space →
  PrimePowerOccurrence space arithmetic →
  WeilTestSpace.Scalar space
occurrenceWeight space arithmetic scalar (occurrence p exponentIndex) =
  PrimePowerCountingScalar.unitFraction scalar (suc exponentIndex)

sumOccurrenceWeights :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  PrimePowerCountingScalar space →
  List (PrimePowerOccurrence space arithmetic) →
  WeilTestSpace.Scalar space
sumOccurrenceWeights space arithmetic scalar [] =
  WeilTestSpace.zeroS space
sumOccurrenceWeights space arithmetic scalar (power ∷ powers) =
  WeilTestSpace._+S_ space
    (occurrenceWeight space arithmetic scalar power)
    (sumOccurrenceWeights space arithmetic scalar powers)

record SymmetricPrimePowerEnumeration
  (space : WeilTestSpace)
  (arithmetic : AllPrimeArithmetic space)
  (bound : Nat) : Set₁ where
  field
    strictOccurrences :
      List (PrimePowerOccurrence space arithmetic)
    endpointOccurrences :
      List (PrimePowerOccurrence space arithmetic)

    strictSound :
      (power : PrimePowerOccurrence space arithmetic) →
      OccurrenceMember power strictOccurrences →
      occurrenceValue space arithmetic power < bound

    endpointSound :
      (power : PrimePowerOccurrence space arithmetic) →
      OccurrenceMember power endpointOccurrences →
      occurrenceValue space arithmetic power ≡ bound

    strictComplete :
      (power : PrimePowerOccurrence space arithmetic) →
      occurrenceValue space arithmetic power < bound →
      OccurrenceMember power strictOccurrences

    endpointComplete :
      (power : PrimePowerOccurrence space arithmetic) →
      occurrenceValue space arithmetic power ≡ bound →
      OccurrenceMember power endpointOccurrences

    NoDuplicateOccurrences :
      List (PrimePowerOccurrence space arithmetic) → Set
    noDuplicateStrict :
      NoDuplicateOccurrences strictOccurrences
    noDuplicateEndpoint :
      NoDuplicateOccurrences endpointOccurrences

    UniquePrimePowerRepresentation : Set
    uniquePrimePowerRepresentation : UniquePrimePowerRepresentation

record PrimePowerEnumerationFamily
  (space : WeilTestSpace)
  (arithmetic : AllPrimeArithmetic space) : Set₁ where
  field
    enumerate :
      (bound : Nat) →
      SymmetricPrimePowerEnumeration space arithmetic bound

riemannPrimePowerCount0 :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  PrimePowerCountingScalar space →
  PrimePowerEnumerationFamily space arithmetic →
  Nat →
  WeilTestSpace.Scalar space
riemannPrimePowerCount0 space arithmetic scalar family bound =
  let enumeration = PrimePowerEnumerationFamily.enumerate family bound
      strict =
        sumOccurrenceWeights space arithmetic scalar
          (SymmetricPrimePowerEnumeration.strictOccurrences enumeration)
      endpoint =
        sumOccurrenceWeights space arithmetic scalar
          (SymmetricPrimePowerEnumeration.endpointOccurrences enumeration)
  in
  WeilTestSpace._+S_ space strict
    (PrimePowerCountingScalar.halfS scalar endpoint)

------------------------------------------------------------------------
-- Identity with Σₖ π₀(x^(1/k))/k
------------------------------------------------------------------------

primeCount0Scalar :
  (space : WeilTestSpace) →
  PrimePowerCountingScalar space →
  PrimePredicate →
  Nat →
  WeilTestSpace.Scalar space
primeCount0Scalar space scalar primes n =
  PrimePowerCountingScalar.halfS scalar
    (PrimePowerCountingScalar.natLift scalar
      (primeCountSymmetricTwice primes n))

primeCountRootWeightedSum :
  (space : WeilTestSpace) →
  (scalar : PrimePowerCountingScalar space) →
  (primes : PrimePredicate) →
  IntegerRootFloor →
  Nat →
  Nat →
  WeilTestSpace.Scalar space
primeCountRootWeightedSum space scalar primes roots zero x =
  WeilTestSpace.zeroS space
primeCountRootWeightedSum space scalar primes roots
  (suc exponentCutoff) x =
  WeilTestSpace._+S_ space
    (PrimePowerCountingScalar._*S_ scalar
      (PrimePowerCountingScalar.unitFraction scalar (suc exponentCutoff))
      (primeCount0Scalar space scalar primes
        (IntegerRootFloor.rootFloor roots x (suc exponentCutoff))))
    (primeCountRootWeightedSum
      space scalar primes roots exponentCutoff x)

record RiemannPrimePowerCountIdentity
  (space : WeilTestSpace)
  (arithmetic : AllPrimeArithmetic space)
  (scalar : PrimePowerCountingScalar space)
  (family : PrimePowerEnumerationFamily space arithmetic)
  (primes : PrimePredicate)
  (roots : IntegerRootFloor) : Set₁ where
  field
    exponentCutoff : Nat → Nat
    cutoffCoversAllRootTerms : Nat → Set
    cutoffCoverage :
      (x : Nat) →
      cutoffCoversAllRootTerms x

    primePowerCountAsPrimeRootSum :
      (x : Nat) →
      riemannPrimePowerCount0 space arithmetic scalar family x
      ≡
      primeCountRootWeightedSum space scalar primes roots
        (exponentCutoff x) x

------------------------------------------------------------------------
-- Möbius inversion π₀(x) = Σ μ(k)/k J₀(x^(1/k))
------------------------------------------------------------------------

record MobiusScalarKernel (space : WeilTestSpace) : Set₁ where
  open WeilTestSpace space
  field
    mobiusOverIndex : Nat → Scalar
    _*S_ : Scalar → Scalar → Scalar

mobiusPrimeCountSum :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  (scalar : PrimePowerCountingScalar space) →
  (family : PrimePowerEnumerationFamily space arithmetic) →
  MobiusScalarKernel space →
  IntegerRootFloor →
  Nat →
  Nat →
  WeilTestSpace.Scalar space
mobiusPrimeCountSum space arithmetic scalar family mobius roots zero x =
  WeilTestSpace.zeroS space
mobiusPrimeCountSum space arithmetic scalar family mobius roots
  (suc cutoff) x =
  WeilTestSpace._+S_ space
    (MobiusScalarKernel._*S_ mobius
      (MobiusScalarKernel.mobiusOverIndex mobius (suc cutoff))
      (riemannPrimePowerCount0 space arithmetic scalar family
        (IntegerRootFloor.rootFloor roots x (suc cutoff))))
    (mobiusPrimeCountSum
      space arithmetic scalar family mobius roots cutoff x)

record MobiusPrimeCountInversion
  (space : WeilTestSpace)
  (arithmetic : AllPrimeArithmetic space)
  (scalar : PrimePowerCountingScalar space)
  (family : PrimePowerEnumerationFamily space arithmetic)
  (primes : PrimePredicate)
  (mobius : MobiusScalarKernel space)
  (roots : IntegerRootFloor) : Set₁ where
  field
    inversionCutoff : Nat → Nat
    inversionTailVanishes : Nat → Set
    inversionTailProof :
      (x : Nat) →
      inversionTailVanishes x

    mobiusInversion :
      (x : Nat) →
      primeCount0Scalar space scalar primes x
      ≡
      mobiusPrimeCountSum
        space arithmetic scalar family mobius roots
        (inversionCutoff x) x

record RiemannPrimePowerCountingBoundary : Set where
  field
    primePowerJumpsWeightedByReciprocalExponent : ⊤
    endpointJumpsAreHalved : ⊤
    enumerationCompletenessRequired : ⊤
    rootSumNeedsFiniteCoverage : ⊤
    mobiusInversionNeedsTailProof : ⊤
    noAnalyticExplicitFormulaClaim : ⊤

riemannPrimePowerCountingBoundary :
  RiemannPrimePowerCountingBoundary
riemannPrimePowerCountingBoundary = record
  { primePowerJumpsWeightedByReciprocalExponent = tt
  ; endpointJumpsAreHalved = tt
  ; enumerationCompletenessRequired = tt
  ; rootSumNeedsFiniteCoverage = tt
  ; mobiusInversionNeedsTailProof = tt
  ; noAnalyticExplicitFormulaClaim = tt
  }
