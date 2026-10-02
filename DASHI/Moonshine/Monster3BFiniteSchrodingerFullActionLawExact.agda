module DASHI.Moonshine.Monster3BFiniteSchrodingerFullActionLawExact where

------------------------------------------------------------------------
-- FULL HEISENBERG ACTION LAW FOR THE FINITE SCHRODINGER MODEL
--
-- DASHI CONTRIBUTION
--
-- The arbitrary-Weyl owner already proves all operator identities required:
--
--   T_a T_A = T_(a+A)
--   M_b M_B = M_(b+B)
--   M_b T_A = zeta^(b.A) T_A M_b
--
-- and the full action factors as
--
--   rho(a,b,c) = S_c T_a M_b.
--
-- This owner performs only the structural normalization
--
--   S_c T_a M_b S_C T_A M_B
--     = S_(c+C+b.A) T_(a+A) M_(b+B),
--
-- exactly matching the central-extension multiplication law.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BF3AlgebraExact as F3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as Schrodinger
import DASHI.Moonshine.Monster3BFiniteSchrodingerHeisenbergActionExact as Action
import DASHI.Moonshine.Monster3BFiniteSchrodingerArbitraryWeylExact as Weyl

infixl 6 _⊕_
_⊕_ : Trit → Trit → Trit
_⊕_ = G._+3_

------------------------------------------------------------------------
-- 1. Scalar operators commute through translation/modulation.
------------------------------------------------------------------------

translationCommutesCyclotomicScale :
  (a : G.X6) →
  (scalar : C3.Cyclotomic3) →
  (f : Schrodinger.SchrodingerFunction) →
  (x : G.X6) →
  Weyl.arbitraryTranslation a
    (Schrodinger.cyclotomicScaleFunction scalar f) x
  ≡
  Schrodinger.cyclotomicScaleFunction scalar
    (Weyl.arbitraryTranslation a f) x
translationCommutesCyclotomicScale a scalar f x = refl

modulationCommutesCyclotomicScale :
  (b : G.X6) →
  (scalar : C3.Cyclotomic3) →
  (f : Schrodinger.SchrodingerFunction) →
  (x : G.X6) →
  Weyl.arbitraryModulation b
    (Schrodinger.cyclotomicScaleFunction scalar f) x
  ≡
  Schrodinger.cyclotomicScaleFunction scalar
    (Weyl.arbitraryModulation b f) x
modulationCommutesCyclotomicScale b scalar f x =
  Action.scalarsCommuteThroughAction
    (Schrodinger.phase (H.dot6 b x))
    scalar
    (f x)

phaseScaleComposition :
  (left right : Trit) →
  (f : Schrodinger.SchrodingerFunction) →
  (x : G.X6) →
  Schrodinger.cyclotomicScaleFunction (Schrodinger.phase left)
    (Schrodinger.cyclotomicScaleFunction (Schrodinger.phase right) f) x
  ≡
  Schrodinger.cyclotomicScaleFunction
    (Schrodinger.phase (left ⊕ right)) f x
phaseScaleComposition left right f x =
  trans
    (Weyl.multiplyAssociative
      (Schrodinger.phase left)
      (Schrodinger.phase right)
      (f x))
    (cong
      (λ scalar → C3.multiply scalar (f x))
      (Action.phaseProduct left right))

------------------------------------------------------------------------
-- 2. Weyl normal form.
------------------------------------------------------------------------

weylNormalForm :
  Trit →
  G.X6 →
  G.X6 →
  Schrodinger.SchrodingerFunction →
  Schrodinger.SchrodingerFunction
weylNormalForm c a b f =
  Schrodinger.cyclotomicScaleFunction
    (Schrodinger.phase c)
    (Weyl.arbitraryTranslation a
      (Weyl.arbitraryModulation b f))

actionIsWeylNormalForm :
  (g : H.Heisenberg6) →
  (f : Schrodinger.SchrodingerFunction) →
  (x : G.X6) →
  Action.heisenbergAction g f x
  ≡
  weylNormalForm
    (H.centralPhase g)
    (H.translationPart (H.quotient g))
    (H.modulationPart (H.quotient g))
    f x
actionIsWeylNormalForm =
  Weyl.heisenbergActionFactorsThroughWeyl

------------------------------------------------------------------------
-- 2b. Pointwise equality transports through a Weyl normal form.
------------------------------------------------------------------------

normalFormCongPointwise :
  (c : Trit) →
  (a b : G.X6) →
  (left right : Schrodinger.SchrodingerFunction) →
  ((x : G.X6) → left x ≡ right x) →
  (x : G.X6) →
  weylNormalForm c a b left x
  ≡
  weylNormalForm c a b right x
normalFormCongPointwise c a b left right equal x =
  let y = Action.translateByVector a x in
  cong
    (λ value →
      C3.multiply
        (Schrodinger.phase c)
        (C3.multiply
          (Schrodinger.phase (H.dot6 b y))
          value))
    (equal y)

------------------------------------------------------------------------
-- 3. Composition of normal forms.
------------------------------------------------------------------------

normalFormComposition :
  (c C : Trit) →
  (a b A B : G.X6) →
  (f : Schrodinger.SchrodingerFunction) →
  (x : G.X6) →
  weylNormalForm c a b
    (weylNormalForm C A B f) x
  ≡
  weylNormalForm
    (c ⊕ (C ⊕ H.dot6 b A))
    (H.addX6 a A)
    (H.addX6 b B)
    f x
normalFormComposition c C a b A B f x =
  let
    y = Action.translateByVector a x
    d = H.dot6 b A
    tail = Weyl.arbitraryTranslation A (Weyl.arbitraryModulation B f)
  in
  trans
    (cong
      (λ z →
        C3.multiply
          (Schrodinger.phase c)
          z)
      (modulationCommutesCyclotomicScale
        b
        (Schrodinger.phase C)
        tail
        y))
    (trans
      (phaseScaleComposition
        c C
        (Weyl.arbitraryTranslation a
          (Weyl.arbitraryModulation b tail))
        x)
      (trans
        (cong
          (λ z →
            C3.multiply
              (Schrodinger.phase (c ⊕ C))
              z)
          (Weyl.arbitraryWeylRelation
            b A
            (Weyl.arbitraryModulation B f)
            y))
        (trans
          (cong
            (λ z →
              C3.multiply
                (Schrodinger.phase (c ⊕ C))
                z)
            (translationCommutesCyclotomicScale
              a
              (Schrodinger.phase d)
              (Weyl.arbitraryTranslation A
                (Weyl.arbitraryModulation b
                  (Weyl.arbitraryModulation B f)))
              x))
          (trans
            (phaseScaleComposition
              (c ⊕ C) d
              (Weyl.arbitraryTranslation a
                (Weyl.arbitraryTranslation A
                  (Weyl.arbitraryModulation b
                    (Weyl.arbitraryModulation B f))))
              x)
            (trans
              (cong
                (λ z →
                  C3.multiply
                    (Schrodinger.phase ((c ⊕ C) ⊕ d))
                    z)
                (Weyl.arbitraryTranslationComposition
                  a A
                  (Weyl.arbitraryModulation b
                    (Weyl.arbitraryModulation B f))
                  x))
              (trans
                (cong
                  (λ z →
                    C3.multiply
                      (Schrodinger.phase ((c ⊕ C) ⊕ d))
                      z)
                  (Weyl.arbitraryModulationComposition
                    b B f
                    (Action.translateByVector (H.addX6 a A) x)))
                (cong
                  (λ exponent →
                    C3.multiply
                      (Schrodinger.phase exponent)
                      (Weyl.arbitraryTranslation
                        (H.addX6 a A)
                        (Weyl.arbitraryModulation
                          (H.addX6 b B) f)
                        x))
                  (F3.plusAssoc c C d))))))))

------------------------------------------------------------------------
-- 4. Match exactly the central-extension compose law.
------------------------------------------------------------------------

actionCompositionPointwise :
  (g h : H.Heisenberg6) →
  (f : Schrodinger.SchrodingerFunction) →
  (x : G.X6) →
  Action.heisenbergAction (H.compose g h) f x
  ≡
  Action.heisenbergAction g
    (Action.heisenbergAction h f) x
actionCompositionPointwise
  (H.heisenberg6 (H.symplectic12 a b) c)
  (H.heisenberg6 (H.symplectic12 A B) C)
  f x =
  trans
    (actionIsWeylNormalForm
      (H.compose
        (H.heisenberg6 (H.symplectic12 a b) c)
        (H.heisenberg6 (H.symplectic12 A B) C))
      f x)
    (trans
      (sym
        (normalFormComposition
          c C a b A B f x))
      (trans
        (normalFormCongPointwise
          c a b
          (weylNormalForm C A B f)
          (Action.heisenbergAction
            (H.heisenberg6 (H.symplectic12 A B) C)
            f)
          (λ point →
            sym
              (actionIsWeylNormalForm
                (H.heisenberg6 (H.symplectic12 A B) C)
                f point))
          x)
        (sym
          (actionIsWeylNormalForm
            (H.heisenberg6 (H.symplectic12 a b) c)
            (Action.heisenbergAction
              (H.heisenberg6 (H.symplectic12 A B) C)
              f)
            x))))

------------------------------------------------------------------------
-- 5. Package the previously open action-law receipt.
------------------------------------------------------------------------

canonicalFullHeisenbergActionLawReceipt :
  Action.FullHeisenbergActionLawReceipt
canonicalFullHeisenbergActionLawReceipt =
  Action.full-heisenberg-action-law-receipt
    actionCompositionPointwise

record FullActionLawBoundary : Set where
  constructor full-action-law-boundary
  field
    arbitraryWeylConsumed : Bool
    centralExtensionComposeConsumed : Bool
    fullActionCompositionPointwisePaid : Bool
    fullHeisenbergActionLawReceiptInhabited : Bool

canonicalFullActionLawBoundary : FullActionLawBoundary
canonicalFullActionLawBoundary =
  full-action-law-boundary true true true true
