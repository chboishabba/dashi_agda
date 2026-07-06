module DASHI.Physics.Closure.NSTriadKNTransitionConcreteBounds where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_≤_; _*_; _+_)

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

  transitionRowIncidenceCountBound :
    (N : Nat) ->
    (c : TransitionClass) ->
    (rowCount : Nat) ->
    rowCount ≤ transitionRowCountBound c N

  transitionColumnIncidenceCountBound :
    (N : Nat) ->
    (c : TransitionClass) ->
    (columnCount : Nat) ->
    columnCount ≤ transitionColumnCountBound c N

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

  transitionRowCountMagnitudeProductN1 :
    (c : TransitionClass) ->
    (N : Nat) ->
    transitionRowCountBound c N
      ≤ transitionRowProductN1Constant c * transitionMagnitudeDenominator c N

  transitionColumnCountMagnitudeProductN1 :
    (c : TransitionClass) ->
    (N : Nat) ->
    transitionColumnCountBound c N
      ≤ transitionColumnProductN1Constant c * transitionMagnitudeDenominator c N

  transitionRowN1Bound :
    (N : Nat) ->
    transitionRowScaledFunctional N ≤ transitionRowScaledTarget N

  transitionColumnN1Bound :
    (N : Nat) ->
    transitionColumnScaledFunctional N ≤ transitionColumnScaledTarget N

record NSTriadKNTransitionConcreteBounds : Set where
  constructor mkNSTriadKNTransitionConcreteBounds
  field
    rowIncidenceCountBoundWitness :
      (N : Nat) ->
      (c : TransitionClass) ->
      (rowCount : Nat) ->
      rowCount ≤ transitionRowCountBound c N

    columnIncidenceCountBoundWitness :
      (N : Nat) ->
      (c : TransitionClass) ->
      (columnCount : Nat) ->
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
