module DASHI.Moonshine.Base369Monster3BMultiplicityProductActionFactorisationBidiExact where

------------------------------------------------------------------------
-- PRODUCT-ACTION FRONTIER ON THE COMPILED 90-CARRIER
--
-- We now own, by compiler construction,
--
--   Fin 90 <-> Completed10 x T^2
--
-- together with the actual multiplicity inertia action transported to this
-- product carrier.  The remaining scientific question is not carrier identity
-- but DYNAMICAL FACTORIZATION:
--
--   A(c,t) ?= (A10(c), AT2(t)).
--
-- This owner exposes both positive descent receipts and exact negative
-- witnesses.  Thus a coupled action cannot be mistaken for a product action
-- merely because the carrier itself factors as 10 x 3^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; cong₂; sym; trans)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Foundations.Base369NonaryTritSquareExact as Square
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Actual
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Compiler

------------------------------------------------------------------------
-- 1. Independent descent of the two product coordinates.
------------------------------------------------------------------------

record CoarseActionDescent
    {source : Action.ActualMonster3BActionRecognition}
    (attachment : Actual.ActualMultiplicityInertiaAttachment source) : Set₁ where
  field
    coarseAct :
      Actual.MultiplicityInertia attachment →
      Harmonic.CoarseChannel → Harmonic.CoarseChannel

    coarseProjectionIntertwines :
      (inertia : Actual.MultiplicityInertia attachment) →
      (coarse : Harmonic.CoarseChannel) →
      (square : Square.TritSquare) →
      proj₁ (Compiler.completedActualAct attachment inertia (coarse , square))
      ≡ coarseAct inertia coarse

open CoarseActionDescent public

record TritSquareActionDescent
    {source : Action.ActualMonster3BActionRecognition}
    (attachment : Actual.ActualMultiplicityInertiaAttachment source) : Set₁ where
  field
    tritSquareAct :
      Actual.MultiplicityInertia attachment →
      Square.TritSquare → Square.TritSquare

    tritSquareProjectionIntertwines :
      (inertia : Actual.MultiplicityInertia attachment) →
      (coarse : Harmonic.CoarseChannel) →
      (square : Square.TritSquare) →
      proj₂ (Compiler.completedActualAct attachment inertia (coarse , square))
      ≡ tritSquareAct inertia square

open TritSquareActionDescent public

------------------------------------------------------------------------
-- 2. If both projections descend, the whole transported action factors.
------------------------------------------------------------------------

record ProductActionFactorisation
    {source : Action.ActualMonster3BActionRecognition}
    (attachment : Actual.ActualMultiplicityInertiaAttachment source) : Set₁ where
  field
    coarseDescent : CoarseActionDescent attachment
    squareDescent : TritSquareActionDescent attachment

  productAction :
    Actual.MultiplicityInertia attachment →
    Harmonic.CoarseChannel → Square.TritSquare →
    Harmonic.CoarseChannel × Square.TritSquare
  productAction inertia coarse square =
    coarseAct coarseDescent inertia coarse ,
    tritSquareAct squareDescent inertia square

  field
    transportedActionFactors :
      (inertia : Actual.MultiplicityInertia attachment) →
      (coarse : Harmonic.CoarseChannel) →
      (square : Square.TritSquare) →
      Compiler.completedActualAct attachment inertia (coarse , square)
      ≡ productAction inertia coarse square

open ProductActionFactorisation public

factorisationFromIndependentDescents :
  ∀ {source}
    {attachment : Actual.ActualMultiplicityInertiaAttachment source} →
  (coarse : CoarseActionDescent attachment) →
  (square : TritSquareActionDescent attachment) →
  ProductActionFactorisation attachment
factorisationFromIndependentDescents coarse square =
  record
    { coarseDescent = coarse
    ; squareDescent = square
    ; transportedActionFactors = λ inertia c t →
        cong₂ _,_
          (coarseProjectionIntertwines coarse inertia c t)
          (tritSquareProjectionIntertwines square inertia c t)
    }

------------------------------------------------------------------------
-- 3. Exact negative witnesses: hidden cross-coordinate dependence blocks
--    descent of the corresponding projection.
------------------------------------------------------------------------

record CoarseCouplingWitness
    {source : Action.ActualMonster3BActionRecognition}
    (attachment : Actual.ActualMultiplicityInertiaAttachment source) : Set₁ where
  field
    inertia : Actual.MultiplicityInertia attachment
    coarse : Harmonic.CoarseChannel
    leftSquare rightSquare : Square.TritSquare
    coarseOutputsDiffer :
      proj₁ (Compiler.completedActualAct attachment inertia (coarse , leftSquare))
      ≢ proj₁ (Compiler.completedActualAct attachment inertia (coarse , rightSquare))

open CoarseCouplingWitness public

coarseCouplingBlocksDescent :
  ∀ {source}
    {attachment : Actual.ActualMultiplicityInertiaAttachment source} →
  CoarseCouplingWitness attachment →
  CoarseActionDescent attachment →
  ⊥
coarseCouplingBlocksDescent witness descent =
  coarseOutputsDiffer witness equality
  where
  equality :
    proj₁
      (Compiler.completedActualAct attachment
        (inertia witness) (coarse witness , leftSquare witness))
    ≡
    proj₁
      (Compiler.completedActualAct attachment
        (inertia witness) (coarse witness , rightSquare witness))
  equality =
    trans
      (coarseProjectionIntertwines descent
        (inertia witness) (coarse witness) (leftSquare witness))
      (sym
        (coarseProjectionIntertwines descent
          (inertia witness) (coarse witness) (rightSquare witness)))

record TritSquareCouplingWitness
    {source : Action.ActualMonster3BActionRecognition}
    (attachment : Actual.ActualMultiplicityInertiaAttachment source) : Set₁ where
  field
    inertia : Actual.MultiplicityInertia attachment
    square : Square.TritSquare
    leftCoarse rightCoarse : Harmonic.CoarseChannel
    squareOutputsDiffer :
      proj₂ (Compiler.completedActualAct attachment inertia (leftCoarse , square))
      ≢ proj₂ (Compiler.completedActualAct attachment inertia (rightCoarse , square))

open TritSquareCouplingWitness public

tritSquareCouplingBlocksDescent :
  ∀ {source}
    {attachment : Actual.ActualMultiplicityInertiaAttachment source} →
  TritSquareCouplingWitness attachment →
  TritSquareActionDescent attachment →
  ⊥
tritSquareCouplingBlocksDescent witness descent =
  squareOutputsDiffer witness equality
  where
  equality :
    proj₂
      (Compiler.completedActualAct attachment
        (inertia witness) (leftCoarse witness , square witness))
    ≡
    proj₂
      (Compiler.completedActualAct attachment
        (inertia witness) (rightCoarse witness , square witness))
  equality =
    trans
      (tritSquareProjectionIntertwines descent
        (inertia witness) (leftCoarse witness) (square witness))
      (sym
        (tritSquareProjectionIntertwines descent
          (inertia witness) (rightCoarse witness) (square witness)))

------------------------------------------------------------------------
-- 4. Boundary classification.
------------------------------------------------------------------------

record ProductActionBoundary : Set where
  constructor productActionBoundary
  field
    carrierTenTimesTritSquareOwned : Bool
    transportedActualActionOwned : Bool
    productFactorisationNotImpliedByCarrier : Bool
    independentProjectionDescentsSuffice : Bool
    coarseCrossDependenceBlocksCoarseDescent : Bool
    squareCrossDependenceBlocksSquareDescent : Bool
    actualFactorisationInhabitedHere : Bool

canonicalProductActionBoundary : ProductActionBoundary
canonicalProductActionBoundary =
  productActionBoundary true true true true true true false
