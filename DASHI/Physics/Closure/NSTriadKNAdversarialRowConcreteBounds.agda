module DASHI.Physics.Closure.NSTriadKNAdversarialRowConcreteBounds where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_; _*_; s≤s; z≤n)
open import Data.Nat.Properties using
  ( ≤-refl
  ; ≤-reflexive
  ; ≤-trans
  ; *-mono-≤
  ; *-identityˡ
  ; *-identityʳ
  )
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates
  using ( AdversarialClass
        ; sparseAdmissible
        ; angularDegenerate
        ; boundarySmallShell
        ; adversarialRowCountBound
        )
open import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType
  using (AdversarialTriadIncidence)

------------------------------------------------------------------------
-- Concrete row-bound arithmetic and theorem surface for the adversarial
-- profile.
--
-- The target theorem is the scaled form of
--
--   R_N^adv(w_N) <= A_adv / N^2
--
-- represented here as a bounded row functional together with the exact
-- primitive lemmas the analytic proof is expected to consume:
--
--   adversarialRowIncidenceCountBound
--   adversarialRowMagnitudeEnvelopeBound
--   adversarialRowCountMagnitudeProductN2
--   adversarialRowN2Bound

rowScaleBase : Nat -> Nat
rowScaleBase N = suc N

adversarialRowDenominator : AdversarialClass -> Nat -> Nat
adversarialRowDenominator sparseAdmissible N =
  rowScaleBase N * rowScaleBase N
adversarialRowDenominator angularDegenerate N =
  rowScaleBase N * (rowScaleBase N * rowScaleBase N)
adversarialRowDenominator boundarySmallShell N =
  rowScaleBase N * rowScaleBase N

adversarialRowProductN2Constant : AdversarialClass -> Nat
adversarialRowProductN2Constant _ = 1

adversarialRowScaledTarget : Nat -> Nat
adversarialRowScaledTarget _ = 1

postulate
  actualAdversarialKernelWeight :
    {c : AdversarialClass} ->
    (N : Nat) -> AdversarialTriadIncidence c N -> Nat

  adversarialRowScaledFunctional :
    Nat -> Nat

  adversarialRowMagnitudeEnvelopeBound :
    {c : AdversarialClass} ->
    (N : Nat) ->
    (τ : AdversarialTriadIncidence c N) ->
    actualAdversarialKernelWeight N τ * adversarialRowDenominator c N
      ≤ adversarialRowProductN2Constant c

  adversarialRowN2Bound :
    (N : Nat) ->
    adversarialRowScaledFunctional N ≤ adversarialRowScaledTarget N

adversarialRowIncidenceCountBound :
  (N : Nat) ->
  (c : AdversarialClass) ->
  (rowCount : Nat) ->
  rowCount ≡ adversarialRowCountBound c N ->
  rowCount ≤ adversarialRowCountBound c N
adversarialRowIncidenceCountBound _ _ _ count≡bound =
  ≤-reflexive count≡bound

------------------------------------------------------------------------
-- Classwise row count × magnitude arithmetic.
--
-- This is the formula-level part of the row proof. It makes the exponent
-- bookkeeping concrete before the final row functional is wired.

one≤suc : (N : Nat) -> 1 ≤ suc N
one≤suc _ = s≤s z≤n

n≤suc : (N : Nat) -> N ≤ suc N
n≤suc zero = z≤n
n≤suc (suc N) = s≤s (n≤suc N)

suc≤sucSquare : (N : Nat) -> suc N ≤ adversarialRowDenominator sparseAdmissible N
suc≤sucSquare N =
  ≤-trans
    (≤-reflexive (sym (*-identityʳ (suc N))))
    (*-mono-≤ (≤-refl {suc N}) (one≤suc N))

suc≤sucCube : (N : Nat) -> suc N ≤ adversarialRowDenominator angularDegenerate N
suc≤sucCube N =
  ≤-trans
    (≤-reflexive (sym (*-identityʳ (suc N))))
    (*-mono-≤
      (≤-refl {suc N})
      (≤-trans (one≤suc N) (suc≤sucSquare N)))

one≤sucSquare : (N : Nat) -> 1 ≤ adversarialRowDenominator sparseAdmissible N
one≤sucSquare N = ≤-trans (one≤suc N) (suc≤sucSquare N)

adversarialRowCountMagnitudeProductN2 :
  (c : AdversarialClass) ->
  (N : Nat) ->
  adversarialRowCountBound c N
    ≤ adversarialRowProductN2Constant c * adversarialRowDenominator c N
adversarialRowCountMagnitudeProductN2 sparseAdmissible N =
  ≤-trans
    (one≤sucSquare N)
    (≤-reflexive (sym (*-identityˡ
      (adversarialRowDenominator sparseAdmissible N))))
adversarialRowCountMagnitudeProductN2 angularDegenerate N =
  ≤-trans
    (≤-trans (n≤suc N) (suc≤sucCube N))
    (≤-reflexive (sym (*-identityˡ
      (adversarialRowDenominator angularDegenerate N))))
adversarialRowCountMagnitudeProductN2 boundarySmallShell N =
  ≤-trans
    (one≤sucSquare N)
    (≤-reflexive (sym (*-identityˡ
      (adversarialRowDenominator boundarySmallShell N))))

record NSTriadKNAdversarialRowConcreteBounds : Set where
  constructor mkNSTriadKNAdversarialRowConcreteBounds
  field
    rowIncidenceCountBoundWitness :
      (N : Nat) ->
      (c : AdversarialClass) ->
      (rowCount : Nat) ->
      rowCount ≡ adversarialRowCountBound c N ->
      rowCount ≤ adversarialRowCountBound c N

    rowMagnitudeEnvelopeBoundWitness :
      {c : AdversarialClass} ->
      (N : Nat) ->
      (τ : AdversarialTriadIncidence c N) ->
      actualAdversarialKernelWeight N τ * adversarialRowDenominator c N
        ≤ adversarialRowProductN2Constant c

    rowCountMagnitudeProductN2Witness :
      (c : AdversarialClass) ->
      (N : Nat) ->
      adversarialRowCountBound c N
        ≤ adversarialRowProductN2Constant c * adversarialRowDenominator c N

    rowN2BoundWitness :
      (N : Nat) ->
      adversarialRowScaledFunctional N ≤ adversarialRowScaledTarget N

open NSTriadKNAdversarialRowConcreteBounds public

canonicalNSTriadKNAdversarialRowConcreteBounds :
  NSTriadKNAdversarialRowConcreteBounds
canonicalNSTriadKNAdversarialRowConcreteBounds =
  mkNSTriadKNAdversarialRowConcreteBounds
    adversarialRowIncidenceCountBound
    adversarialRowMagnitudeEnvelopeBound
    adversarialRowCountMagnitudeProductN2
    adversarialRowN2Bound
