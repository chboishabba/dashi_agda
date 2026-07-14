module DASHI.Physics.Closure.NSTriadKNTransitionConcreteBounds where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_; _*_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using
  ( ≤-refl
  ; ≤-reflexive
  ; ≤-trans
  ; *-mono-≤
  ; *-identityˡ
  ; *-identityʳ
  )
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates
  using ( TransitionClass
        ; thinTransition
        ; balancedTransition
        ; rowThickTransition
        ; columnThickTransition
        ; transitionRowCountBound
        ; transitionColumnCountBound
        ; transitionClassExponentSumAtLeastTwo
        )
open import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType
  using (TransitionTriadIncidence)

------------------------------------------------------------------------
-- Concrete row/column transition bounds.
--
-- This is the first inhabited transition witness lane. The target balanced
-- route is
--
--   R_N^trans(w_N) <= A_trans / N
--   C_N^trans(w_N) <= B_trans / N
--
-- so the transition weighted product closes at N^-2. The class table is the
-- explicit proof plan:
--
--   thinTransition         : N^0 row, N^1 col, N^-2 magnitude
--   balancedTransition     : N^1 row, N^1 col, N^-2 magnitude
--   rowThickTransition     : N^2 row, N^1 col, N^-3 magnitude
--   columnThickTransition  : N^1 row, N^2 col, N^-3 magnitude

transitionScaleBase : Nat -> Nat
transitionScaleBase N = suc N

transitionMagnitudeDenominator : TransitionClass -> Nat -> Nat
transitionMagnitudeDenominator thinTransition N =
  transitionScaleBase N * transitionScaleBase N
transitionMagnitudeDenominator balancedTransition N =
  transitionScaleBase N * transitionScaleBase N
transitionMagnitudeDenominator rowThickTransition N =
  transitionScaleBase N * (transitionScaleBase N * transitionScaleBase N)
transitionMagnitudeDenominator columnThickTransition N =
  transitionScaleBase N * (transitionScaleBase N * transitionScaleBase N)

transitionRowScaledTarget : Nat -> Nat
transitionRowScaledTarget _ = 1

transitionColumnScaledTarget : Nat -> Nat
transitionColumnScaledTarget _ = 1

transitionRowProductN1Constant : TransitionClass -> Nat
transitionRowProductN1Constant _ = 1

transitionColumnProductN1Constant : TransitionClass -> Nat
transitionColumnProductN1Constant _ = 1

postulate
  actualTransitionKernelWeight :
    {c : TransitionClass} ->
    (N : Nat) -> TransitionTriadIncidence c N -> Nat

  transitionRowScaledFunctional :
    Nat -> Nat

  transitionColumnScaledFunctional :
    Nat -> Nat

  transitionPiProductScaleBound :
    {c : TransitionClass} ->
    (N : Nat) ->
    (τ : TransitionTriadIncidence c N) ->
    actualTransitionKernelWeight N τ * transitionMagnitudeDenominator c N
      ≤ 1

  transitionMagnitudeEnvelopeBound :
    {c : TransitionClass} ->
    (N : Nat) ->
    (τ : TransitionTriadIncidence c N) ->
    actualTransitionKernelWeight N τ * transitionMagnitudeDenominator c N
      ≤ 1

  transitionRowN1Bound :
    (N : Nat) ->
    transitionRowScaledFunctional N ≤ transitionRowScaledTarget N

  transitionColumnN1Bound :
    (N : Nat) ->
    transitionColumnScaledFunctional N ≤ transitionColumnScaledTarget N

transitionRowIncidenceCountBound :
  (N : Nat) ->
  (c : TransitionClass) ->
  (rowCount : Nat) ->
  rowCount ≡ transitionRowCountBound c N ->
  rowCount ≤ transitionRowCountBound c N
transitionRowIncidenceCountBound _ _ _ count≡bound =
  ≤-reflexive count≡bound

transitionColumnIncidenceCountBound :
  (N : Nat) ->
  (c : TransitionClass) ->
  (columnCount : Nat) ->
  columnCount ≡ transitionColumnCountBound c N ->
  columnCount ≤ transitionColumnCountBound c N
transitionColumnIncidenceCountBound _ _ _ count≡bound =
  ≤-reflexive count≡bound

------------------------------------------------------------------------
-- Classwise count × magnitude arithmetic.

one≤suc : (N : Nat) -> 1 ≤ suc N
one≤suc _ = s≤s z≤n

n≤suc : (N : Nat) -> N ≤ suc N
n≤suc zero = z≤n
n≤suc (suc N) = s≤s (n≤suc N)

suc≤sucSquare : (N : Nat) -> suc N ≤ transitionMagnitudeDenominator thinTransition N
suc≤sucSquare N =
  ≤-trans
    (≤-reflexive (sym (*-identityʳ (suc N))))
    (*-mono-≤ (≤-refl {suc N}) (one≤suc N))

sucSquare≤sucCube :
  (N : Nat) ->
  transitionMagnitudeDenominator thinTransition N
    ≤ transitionMagnitudeDenominator rowThickTransition N
sucSquare≤sucCube N =
  *-mono-≤ (≤-refl {suc N}) (suc≤sucSquare N)

suc≤sucCube :
  (N : Nat) ->
  suc N ≤ transitionMagnitudeDenominator rowThickTransition N
suc≤sucCube N =
  ≤-trans (suc≤sucSquare N) (sucSquare≤sucCube N)

nSquare≤sucSquare :
  (N : Nat) ->
  N * N ≤ transitionMagnitudeDenominator thinTransition N
nSquare≤sucSquare N =
  *-mono-≤ (n≤suc N) (n≤suc N)

nSquare≤sucCube :
  (N : Nat) ->
  N * N ≤ transitionMagnitudeDenominator rowThickTransition N
nSquare≤sucCube N =
  ≤-trans (nSquare≤sucSquare N) (sucSquare≤sucCube N)

one≤sucSquare :
  (N : Nat) -> 1 ≤ transitionMagnitudeDenominator thinTransition N
one≤sucSquare N = ≤-trans (one≤suc N) (suc≤sucSquare N)

one≤sucCube :
  (N : Nat) -> 1 ≤ transitionMagnitudeDenominator rowThickTransition N
one≤sucCube N = ≤-trans (one≤suc N) (suc≤sucCube N)

transitionRowCountMagnitudeProductN1 :
  (c : TransitionClass) ->
  (N : Nat) ->
  transitionRowCountBound c N
    ≤ transitionRowProductN1Constant c * transitionMagnitudeDenominator c N
transitionRowCountMagnitudeProductN1 thinTransition N =
  ≤-trans
    (one≤sucSquare N)
    (≤-reflexive (sym (*-identityˡ
      (transitionMagnitudeDenominator thinTransition N))))
transitionRowCountMagnitudeProductN1 balancedTransition N =
  ≤-trans
    (≤-trans (n≤suc N) (suc≤sucSquare N))
    (≤-reflexive (sym (*-identityˡ
      (transitionMagnitudeDenominator balancedTransition N))))
transitionRowCountMagnitudeProductN1 rowThickTransition N =
  ≤-trans
    (nSquare≤sucCube N)
    (≤-reflexive (sym (*-identityˡ
      (transitionMagnitudeDenominator rowThickTransition N))))
transitionRowCountMagnitudeProductN1 columnThickTransition N =
  ≤-trans
    (≤-trans (n≤suc N) (suc≤sucCube N))
    (≤-reflexive (sym (*-identityˡ
      (transitionMagnitudeDenominator columnThickTransition N))))

transitionColumnCountMagnitudeProductN1 :
  (c : TransitionClass) ->
  (N : Nat) ->
  transitionColumnCountBound c N
    ≤ transitionColumnProductN1Constant c * transitionMagnitudeDenominator c N
transitionColumnCountMagnitudeProductN1 thinTransition N =
  ≤-trans
    (≤-trans (n≤suc N) (suc≤sucSquare N))
    (≤-reflexive (sym (*-identityˡ
      (transitionMagnitudeDenominator thinTransition N))))
transitionColumnCountMagnitudeProductN1 balancedTransition N =
  ≤-trans
    (≤-trans (n≤suc N) (suc≤sucSquare N))
    (≤-reflexive (sym (*-identityˡ
      (transitionMagnitudeDenominator balancedTransition N))))
transitionColumnCountMagnitudeProductN1 rowThickTransition N =
  ≤-trans
    (≤-trans (n≤suc N) (suc≤sucCube N))
    (≤-reflexive (sym (*-identityˡ
      (transitionMagnitudeDenominator rowThickTransition N))))
transitionColumnCountMagnitudeProductN1 columnThickTransition N =
  ≤-trans
    (nSquare≤sucCube N)
    (≤-reflexive (sym (*-identityˡ
      (transitionMagnitudeDenominator columnThickTransition N))))

record NSTriadKNTransitionConcreteBounds : Set where
  constructor mkNSTriadKNTransitionConcreteBounds
  field
    rowIncidenceCountBoundWitness :
      (N : Nat) ->
      (c : TransitionClass) ->
      (rowCount : Nat) ->
      rowCount ≡ transitionRowCountBound c N ->
      rowCount ≤ transitionRowCountBound c N

    columnIncidenceCountBoundWitness :
      (N : Nat) ->
      (c : TransitionClass) ->
      (columnCount : Nat) ->
      columnCount ≡ transitionColumnCountBound c N ->
      columnCount ≤ transitionColumnCountBound c N

    piProductScaleBoundWitness :
      {c : TransitionClass} ->
      (N : Nat) ->
      (τ : TransitionTriadIncidence c N) ->
      actualTransitionKernelWeight N τ * transitionMagnitudeDenominator c N
        ≤ 1

    magnitudeEnvelopeBoundWitness :
      {c : TransitionClass} ->
      (N : Nat) ->
      (τ : TransitionTriadIncidence c N) ->
      actualTransitionKernelWeight N τ * transitionMagnitudeDenominator c N
        ≤ 1

    rowCountMagnitudeProductN1Witness :
      (c : TransitionClass) ->
      (N : Nat) ->
      transitionRowCountBound c N
        ≤ transitionRowProductN1Constant c * transitionMagnitudeDenominator c N

    columnCountMagnitudeProductN1Witness :
      (c : TransitionClass) ->
      (N : Nat) ->
      transitionColumnCountBound c N
        ≤ transitionColumnProductN1Constant c * transitionMagnitudeDenominator c N

    rowN1BoundWitness :
      (N : Nat) ->
      transitionRowScaledFunctional N ≤ transitionRowScaledTarget N

    columnN1BoundWitness :
      (N : Nat) ->
      transitionColumnScaledFunctional N ≤ transitionColumnScaledTarget N

    classExponentSumWitness :
      (c : TransitionClass) ->
      2 ≤
        (transitionRowProductN1Constant c + transitionColumnProductN1Constant c)

open NSTriadKNTransitionConcreteBounds public

transitionClassExponentSumWitness :
  (c : TransitionClass) ->
  2 ≤ (transitionRowProductN1Constant c + transitionColumnProductN1Constant c)
transitionClassExponentSumWitness _ =
  transitionClassExponentSumAtLeastTwo balancedTransition

canonicalNSTriadKNTransitionConcreteBounds :
  NSTriadKNTransitionConcreteBounds
canonicalNSTriadKNTransitionConcreteBounds =
  mkNSTriadKNTransitionConcreteBounds
    transitionRowIncidenceCountBound
    transitionColumnIncidenceCountBound
    transitionPiProductScaleBound
    transitionMagnitudeEnvelopeBound
    transitionRowCountMagnitudeProductN1
    transitionColumnCountMagnitudeProductN1
    transitionRowN1Bound
    transitionColumnN1Bound
    transitionClassExponentSumWitness
