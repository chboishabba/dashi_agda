module DASHI.Physics.Closure.NSTriadKNAdversarialColumnConcreteBounds where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_; _*_; s≤s; z≤n)
open import Data.Nat.Properties using
  ( ≤-refl
  ; ≤-reflexive
  ; ≤-trans
  ; *-identityˡ
  )
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates
  using ( AdversarialClass
        ; sparseAdmissible
        ; angularDegenerate
        ; boundarySmallShell
        ; adversarialColumnCountBound
        )
open import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType
  using (AdversarialTriadIncidence)
open import DASHI.Physics.Closure.NSTriadKNAdversarialRowConcreteBounds
  using (actualAdversarialKernelWeight)

------------------------------------------------------------------------
-- Concrete column-bound arithmetic and theorem surface for the
-- adversarial profile.
--
-- The target theorem is the scaled form of
--
--   C_N^adv(w_N) <= B_adv / N
--
-- represented here as a bounded column functional together with the
-- exact primitive lemmas the analytic proof is expected to consume:
--
--   adversarialColumnIncidenceCountBound
--   adversarialColumnMagnitudeEnvelopeBound
--   adversarialColumnCountMagnitudeProductN1
--   adversarialColumnN1Bound

columnScaleBase : Nat -> Nat
columnScaleBase N = suc N

adversarialColumnDenominator : AdversarialClass -> Nat -> Nat
adversarialColumnDenominator sparseAdmissible N =
  columnScaleBase N
adversarialColumnDenominator angularDegenerate N =
  columnScaleBase N
adversarialColumnDenominator boundarySmallShell N =
  columnScaleBase N

adversarialColumnProductN1Constant : AdversarialClass -> Nat
adversarialColumnProductN1Constant sparseAdmissible = 1
adversarialColumnProductN1Constant angularDegenerate = 1
adversarialColumnProductN1Constant boundarySmallShell = 1

adversarialColumnScaledTarget : Nat -> Nat
adversarialColumnScaledTarget _ = 1

postulate
  adversarialColumnScaledFunctional :
    Nat -> Nat

  adversarialColumnMagnitudeEnvelopeBound :
    {c : AdversarialClass} ->
    (N : Nat) ->
    (τ : AdversarialTriadIncidence c N) ->
    actualAdversarialKernelWeight N τ * adversarialColumnDenominator c N
      ≤ adversarialColumnProductN1Constant c

  adversarialColumnN1Bound :
    (N : Nat) ->
    adversarialColumnScaledFunctional N ≤ adversarialColumnScaledTarget N

adversarialColumnIncidenceCountBound :
  (N : Nat) ->
  (c : AdversarialClass) ->
  (columnCount : Nat) ->
  columnCount ≡ adversarialColumnCountBound c N ->
  columnCount ≤ adversarialColumnCountBound c N
adversarialColumnIncidenceCountBound _ _ _ count≡bound =
  ≤-reflexive count≡bound

------------------------------------------------------------------------
-- Classwise column count × magnitude arithmetic.
--
-- This is the formula-level part of the column proof. It makes the
-- exponent bookkeeping concrete before the final column functional is wired.

one≤suc : (N : Nat) -> 1 ≤ suc N
one≤suc _ = s≤s z≤n

n≤suc : (N : Nat) -> N ≤ suc N
n≤suc zero = z≤n
n≤suc (suc N) = s≤s (n≤suc N)

adversarialColumnCountMagnitudeProductN1 :
  (c : AdversarialClass) ->
  (N : Nat) ->
  adversarialColumnCountBound c N
    ≤ adversarialColumnProductN1Constant c * adversarialColumnDenominator c N
adversarialColumnCountMagnitudeProductN1 sparseAdmissible N =
  ≤-trans
    (n≤suc N)
    (≤-reflexive (sym (*-identityˡ (adversarialColumnDenominator sparseAdmissible N))))
adversarialColumnCountMagnitudeProductN1 angularDegenerate N =
  ≤-trans
    (n≤suc N)
    (≤-reflexive (sym (*-identityˡ (adversarialColumnDenominator angularDegenerate N))))
adversarialColumnCountMagnitudeProductN1 boundarySmallShell N =
  ≤-trans
    (one≤suc N)
    (≤-reflexive (sym (*-identityˡ (adversarialColumnDenominator boundarySmallShell N))))

record NSTriadKNAdversarialColumnConcreteBounds : Set where
  constructor mkNSTriadKNAdversarialColumnConcreteBounds
  field
    columnIncidenceCountBoundWitness :
      (N : Nat) ->
      (c : AdversarialClass) ->
      (columnCount : Nat) ->
      columnCount ≡ adversarialColumnCountBound c N ->
      columnCount ≤ adversarialColumnCountBound c N

    columnMagnitudeEnvelopeBoundWitness :
      {c : AdversarialClass} ->
      (N : Nat) ->
      (τ : AdversarialTriadIncidence c N) ->
      actualAdversarialKernelWeight N τ * adversarialColumnDenominator c N
        ≤ adversarialColumnProductN1Constant c

    columnCountMagnitudeProductN1Witness :
      (c : AdversarialClass) ->
      (N : Nat) ->
      adversarialColumnCountBound c N
        ≤ adversarialColumnProductN1Constant c * adversarialColumnDenominator c N

    columnN1BoundWitness :
      (N : Nat) ->
      adversarialColumnScaledFunctional N ≤ adversarialColumnScaledTarget N

open NSTriadKNAdversarialColumnConcreteBounds public

canonicalNSTriadKNAdversarialColumnConcreteBounds :
  NSTriadKNAdversarialColumnConcreteBounds
canonicalNSTriadKNAdversarialColumnConcreteBounds =
  mkNSTriadKNAdversarialColumnConcreteBounds
    adversarialColumnIncidenceCountBound
    adversarialColumnMagnitudeEnvelopeBound
    adversarialColumnCountMagnitudeProductN1
    adversarialColumnN1Bound
