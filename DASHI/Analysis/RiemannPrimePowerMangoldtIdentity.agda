module DASHI.Analysis.RiemannPrimePowerMangoldtIdentity where

-- The exact arithmetic identity
--
--   J₀(x) = Σ_{2 ≤ n ≤ x} Λ(n) / log n
--           - 1/2 · Λ(x) / log x.
--
-- At a prime power n = p^k, Λ(n) / log n = log p / log(p^k) = 1/k.
-- The termwise logarithmic law and the finite enumeration identity are explicit
-- proof obligations; no analytic continuation is involved.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannVonMangoldtSpecification
open import DASHI.Analysis.RiemannPrimePowerCounting

record MangoldtLogQuotientKernel
  (space : WeilTestSpace)
  (arithmetic : AllPrimeArithmetic space)
  (mangoldt : VonMangoldtFunction space arithmetic)
  (countingScalar : PrimePowerCountingScalar space) : Set₁ where
  open WeilTestSpace space
  field
    logNat : Nat → Scalar
    _/S_ : Scalar → Scalar → Scalar
    _-S_ : Scalar → Scalar → Scalar

    lambdaOverLogAtPrimePower :
      (p : AllPrimeArithmetic.Prime arithmetic) →
      (exponentIndex : Nat) →
      (VonMangoldtFunction.lambda mangoldt
        (primePowerNat space arithmetic p exponentIndex)
       /S
       logNat (primePowerNat space arithmetic p exponentIndex))
      ≡
      PrimePowerCountingScalar.unitFraction
        countingScalar (suc exponentIndex)

mangoldtLogQuotientTerm :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  (mangoldt : VonMangoldtFunction space arithmetic) →
  (countingScalar : PrimePowerCountingScalar space) →
  MangoldtLogQuotientKernel
    space arithmetic mangoldt countingScalar →
  Nat →
  WeilTestSpace.Scalar space
mangoldtLogQuotientTerm
  space arithmetic mangoldt countingScalar kernel n =
  MangoldtLogQuotientKernel._/S_ kernel
    (VonMangoldtFunction.lambda mangoldt n)
    (MangoldtLogQuotientKernel.logNat kernel n)

mangoldtLogQuotientSumLE :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  (mangoldt : VonMangoldtFunction space arithmetic) →
  (countingScalar : PrimePowerCountingScalar space) →
  MangoldtLogQuotientKernel
    space arithmetic mangoldt countingScalar →
  Nat →
  WeilTestSpace.Scalar space
mangoldtLogQuotientSumLE
  space arithmetic mangoldt countingScalar kernel zero =
  WeilTestSpace.zeroS space
mangoldtLogQuotientSumLE
  space arithmetic mangoldt countingScalar kernel (suc zero) =
  WeilTestSpace.zeroS space
mangoldtLogQuotientSumLE
  space arithmetic mangoldt countingScalar kernel (suc (suc n)) =
  WeilTestSpace._+S_ space
    (mangoldtLogQuotientTerm
      space arithmetic mangoldt countingScalar kernel (suc (suc n)))
    (mangoldtLogQuotientSumLE
      space arithmetic mangoldt countingScalar kernel (suc n))

mangoldtPrimePowerCount0 :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  (mangoldt : VonMangoldtFunction space arithmetic) →
  (countingScalar : PrimePowerCountingScalar space) →
  MangoldtLogQuotientKernel
    space arithmetic mangoldt countingScalar →
  Nat →
  WeilTestSpace.Scalar space
mangoldtPrimePowerCount0
  space arithmetic mangoldt countingScalar kernel x =
  MangoldtLogQuotientKernel._-S_ kernel
    (mangoldtLogQuotientSumLE
      space arithmetic mangoldt countingScalar kernel x)
    (PrimePowerCountingScalar.halfS countingScalar
      (mangoldtLogQuotientTerm
        space arithmetic mangoldt countingScalar kernel x))

record RiemannPrimePowerMangoldtIdentity
  (space : WeilTestSpace)
  (arithmetic : AllPrimeArithmetic space)
  (mangoldt : VonMangoldtFunction space arithmetic)
  (countingScalar : PrimePowerCountingScalar space)
  (enumeration : PrimePowerEnumerationFamily space arithmetic)
  (kernel :
    MangoldtLogQuotientKernel
      space arithmetic mangoldt countingScalar) : Set₁ where
  field
    finiteMangoldtIdentity :
      (x : Nat) →
      riemannPrimePowerCount0
        space arithmetic countingScalar enumeration x
      ≡
      mangoldtPrimePowerCount0
        space arithmetic mangoldt countingScalar kernel x

record RiemannPrimePowerMangoldtBoundary : Set where
  field
    lambdaOverLogIsReciprocalExponent : ⊤
    endpointMangoldtTermIsHalved : ⊤
    finiteEnumerationIdentityRequired : ⊤
    noPerronOrExplicitFormulaUsed : ⊤

riemannPrimePowerMangoldtBoundary :
  RiemannPrimePowerMangoldtBoundary
riemannPrimePowerMangoldtBoundary = record
  { lambdaOverLogIsReciprocalExponent = tt
  ; endpointMangoldtTermIsHalved = tt
  ; finiteEnumerationIdentityRequired = tt
  ; noPerronOrExplicitFormulaUsed = tt
  }
