module DASHI.Physics.YangMills.BalabanDyadicQuantitativeRegionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- A kernel-computable integer certificate for the quantitative search.
--
-- If r = 2^-N and δ(r) = A r + B r², then
--
--   δ(r) < c
--
-- is equivalent to
--
--   A 2^N + B < c 2^(2N)
--
-- when A, B and c are integral majorants.  The physical derivation of the
-- coefficients is deliberately separate; this module verifies candidate
-- regions exactly once such coefficients have been selected.
------------------------------------------------------------------------

infix 4 _≤N_ _<N_

data _≤N_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤N n
  suc≤suc : ∀ {m n} → m ≤N n → suc m ≤N suc n

_<N_ : Nat → Nat → Set
m <N n = suc m ≤N n

leBool : Nat → Nat → Bool
leBool zero n = true
leBool (suc m) zero = false
leBool (suc m) (suc n) = leBool m n

ltBool : Nat → Nat → Bool
ltBool m n = leBool (suc m) n

leBoolSound : ∀ m n → leBool m n ≡ true → m ≤N n
leBoolSound zero n refl = zero≤
leBoolSound (suc m) zero ()
leBoolSound (suc m) (suc n) proof =
  suc≤suc (leBoolSound m n proof)

ltBoolSound : ∀ m n → ltBool m n ≡ true → m <N n
ltBoolSound m n = leBoolSound (suc m) n

andBool : Bool → Bool → Bool
andBool true right = right
andBool false right = false

pow2 : Nat → Nat
pow2 zero = suc zero
pow2 (suc n) = (suc (suc zero)) * pow2 n

record QuadraticMajorant : Set where
  constructor quadraticMajorant
  field
    linearCoefficient quadraticCoefficient : Nat

open QuadraticMajorant public

zeroMajorant : QuadraticMajorant
zeroMajorant = quadraticMajorant zero zero

addMajorant : QuadraticMajorant → QuadraticMajorant → QuadraticMajorant
addMajorant left right =
  quadraticMajorant
    (linearCoefficient left + linearCoefficient right)
    (quadraticCoefficient left + quadraticCoefficient right)

evaluateDyadicNumerator : QuadraticMajorant → Nat → Nat
evaluateDyadicNumerator majorant exponent =
  linearCoefficient majorant * pow2 exponent
  + quadraticCoefficient majorant

sumMajorants : List QuadraticMajorant → QuadraticMajorant
sumMajorants [] = zeroMajorant
sumMajorants (majorant ∷ rest) =
  addMajorant majorant (sumMajorants rest)

scaledThreshold : Nat → Nat → Nat
scaledThreshold threshold exponent =
  threshold * (pow2 exponent * pow2 exponent)

DyadicBelow : QuadraticMajorant → Nat → Nat → Set
DyadicBelow majorant threshold exponent =
  evaluateDyadicNumerator majorant exponent
  <N scaledThreshold threshold exponent

dyadicBelowBool : QuadraticMajorant → Nat → Nat → Bool
dyadicBelowBool majorant threshold exponent =
  ltBool
    (evaluateDyadicNumerator majorant exponent)
    (scaledThreshold threshold exponent)

dyadicBelowBoolSound : ∀ majorant threshold exponent →
  dyadicBelowBool majorant threshold exponent ≡ true →
  DyadicBelow majorant threshold exponent
dyadicBelowBoolSound majorant threshold exponent =
  ltBoolSound
    (evaluateDyadicNumerator majorant exponent)
    (scaledThreshold threshold exponent)

------------------------------------------------------------------------
-- Candidate five-component Hessian budget.
--
-- These are deliberately coarse integer majorants for the formulas proposed
-- in the analytic design.  Their exact physical derivation from the literal
-- Wilson Hessian remains a separate, fail-closed obligation.
------------------------------------------------------------------------

curvatureCandidate : QuadraticMajorant
curvatureCandidate = quadraticMajorant 64 64

transportCandidate : QuadraticMajorant
transportCandidate = quadraticMajorant 8 4

chartCandidate : QuadraticMajorant
chartCandidate = quadraticMajorant 16 32

gaugeFixingCandidate : QuadraticMajorant
gaugeFixingCandidate = quadraticMajorant 32 64

blockConstraintCandidate : QuadraticMajorant
blockConstraintCandidate = quadraticMajorant 16 64

fiveComponentCandidate : QuadraticMajorant
fiveComponentCandidate =
  sumMajorants
    (curvatureCandidate
    ∷ transportCandidate
    ∷ chartCandidate
    ∷ gaugeFixingCandidate
    ∷ blockConstraintCandidate
    ∷ [])

candidateRadiusExponent : Nat
candidateRadiusExponent = 8

-- The Boolean-cell gap is 2.  Reserving half of it gives threshold 1.
hessianReservedThreshold : Nat
hessianReservedThreshold = 1

hessianCandidateComputation :
  dyadicBelowBool fiveComponentCandidate
    hessianReservedThreshold candidateRadiusExponent
  ≡ true
hessianCandidateComputation = refl

hessianCandidateBudget :
  DyadicBelow fiveComponentCandidate
    hessianReservedThreshold candidateRadiusExponent
hessianCandidateBudget =
  dyadicBelowBoolSound fiveComponentCandidate
    hessianReservedThreshold candidateRadiusExponent
    hessianCandidateComputation

------------------------------------------------------------------------
-- Exact common patch allocation: 0.45 < 1 in thousandths.
------------------------------------------------------------------------

record FivePatchNumerators : Set where
  constructor patchNumerators
  field
    bulkNumerator boundaryNumerator interfaceNumerator
      cornerNumerator nestedNumerator : Nat

open FivePatchNumerators public

patchNumeratorSum : FivePatchNumerators → Nat
patchNumeratorSum budget =
  bulkNumerator budget
  + (boundaryNumerator budget
  + (interfaceNumerator budget
  + (cornerNumerator budget + nestedNumerator budget)))

candidatePatchBudget : FivePatchNumerators
candidatePatchBudget = patchNumerators 80 90 95 90 95

patchDenominator : Nat
patchDenominator = 1000

patchCandidateComputation :
  ltBool (patchNumeratorSum candidatePatchBudget) patchDenominator ≡ true
patchCandidateComputation = refl

patchCandidateStrict :
  patchNumeratorSum candidatePatchBudget <N patchDenominator
patchCandidateStrict =
  ltBoolSound
    (patchNumeratorSum candidatePatchBudget)
    patchDenominator
    patchCandidateComputation

------------------------------------------------------------------------
-- Seven-component nonlinear majorant at the same dyadic radius.
------------------------------------------------------------------------

bchCandidate commutatorCandidate nonlinearTransportCandidate
  backgroundDerivativeCandidate nonlinearGaugeCandidate
  nonlinearBlockCandidate nonlinearChartCandidate : QuadraticMajorant
bchCandidate = quadraticMajorant 2 2
commutatorCandidate = quadraticMajorant 3 2
nonlinearTransportCandidate = quadraticMajorant 2 2
backgroundDerivativeCandidate = quadraticMajorant 4 3
nonlinearGaugeCandidate = quadraticMajorant 3 2
nonlinearBlockCandidate = quadraticMajorant 3 2
nonlinearChartCandidate = quadraticMajorant 4 2

sevenComponentCandidate : QuadraticMajorant
sevenComponentCandidate =
  sumMajorants
    (bchCandidate
    ∷ commutatorCandidate
    ∷ nonlinearTransportCandidate
    ∷ backgroundDerivativeCandidate
    ∷ nonlinearGaugeCandidate
    ∷ nonlinearBlockCandidate
    ∷ nonlinearChartCandidate
    ∷ [])

greenCandidateNumerator : Nat
greenCandidateNumerator = 4

scaledNonlinearNumerator : Nat
scaledNonlinearNumerator =
  greenCandidateNumerator
  * evaluateDyadicNumerator sevenComponentCandidate candidateRadiusExponent

nonlinearCandidateComputation :
  ltBool scaledNonlinearNumerator
    (pow2 candidateRadiusExponent * pow2 candidateRadiusExponent)
  ≡ true
nonlinearCandidateComputation = refl

nonlinearCandidateStrict :
  scaledNonlinearNumerator
  <N (pow2 candidateRadiusExponent * pow2 candidateRadiusExponent)
nonlinearCandidateStrict =
  ltBoolSound scaledNonlinearNumerator
    (pow2 candidateRadiusExponent * pow2 candidateRadiusExponent)
    nonlinearCandidateComputation

record CandidateQuantitativeRegion : Set where
  constructor candidateRegion
  field
    hessianBudget :
      DyadicBelow fiveComponentCandidate
        hessianReservedThreshold candidateRadiusExponent
    patchBudget :
      patchNumeratorSum candidatePatchBudget <N patchDenominator
    nonlinearBudget :
      scaledNonlinearNumerator
      <N (pow2 candidateRadiusExponent * pow2 candidateRadiusExponent)

candidateQuantitativeRegion : CandidateQuantitativeRegion
candidateQuantitativeRegion =
  candidateRegion
    hessianCandidateBudget
    patchCandidateStrict
    nonlinearCandidateStrict

candidateQuantitativeRegionLevel : ProofLevel
candidateQuantitativeRegionLevel = computed

physicalHessianCoefficientDerivationLevel : ProofLevel
physicalHessianCoefficientDerivationLevel = conditional

physicalPatchCoefficientDerivationLevel : ProofLevel
physicalPatchCoefficientDerivationLevel = conditional

physicalSevenNonlinearCoefficientDerivationLevel : ProofLevel
physicalSevenNonlinearCoefficientDerivationLevel = conditional
