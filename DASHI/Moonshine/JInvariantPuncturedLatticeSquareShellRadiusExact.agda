module DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellRadiusExact where

------------------------------------------------------------------------
-- SUCCESSOR SQUARE SHELL -> RADIUS-SQUARE LOWER BOUND
--
-- A point lying in the radius-(R+1) square but outside the radius-R square
-- has at least one coordinate equal to +(R+1) or -(R+1).  This is proved
-- constructively from the existing signed cutoff Boolean, not by cardinality.
--
-- Therefore, after the canonical integer -> Bishop real embedding,
--
--   (R+1)^2 <= m^2 + n^2.
--
-- This is exactly the discrete leaf needed by the division-free lattice
-- coercivity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (tt)
open import Data.Bool.Base using (T; _∧_; not)
open import Data.Bool.Properties using (T-∧)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)
open import Relation.Nullary.Decidable.Core using (yes; no)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as Kernel
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as Shell
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Cutoff
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Lattice

falseHasNoT : T false → ⊥
falseHasNoT ()

positiveInCutoff :
  (radius n : Nat) →
  n ≤ radius →
  T (Cutoff.coordinateInCutoff? radius (+ n))
positiveInCutoff zero zero bound = tt
positiveInCutoff zero (suc n) ()
positiveInCutoff (suc radius) n bound =
  Equivalence.from T-∧
    ( ℤP.≤⇒≤ᵇ ℤ.-≤+
    , ℤP.≤⇒≤ᵇ (ℤ.+≤+ bound)
    )

negativeInCutoff :
  (radius n : Nat) →
  suc n ≤ radius →
  T (Cutoff.coordinateInCutoff? radius (-[1+ n ]))
negativeInCutoff zero n ()
negativeInCutoff (suc radius) n (s≤s n≤radius) =
  Equivalence.from T-∧
    ( ℤP.≤⇒≤ᵇ (ℤ.-≤- n≤radius)
    , ℤP.≤⇒≤ᵇ ℤ.-≤+
    )

positiveOuterMagnitudeBound :
  (inner n : Nat) →
  T (Cutoff.coordinateInCutoff? (suc inner) (+ n)) →
  n ≤ suc inner
positiveOuterMagnitudeBound inner n bounded =
  upperNat
    (ℤP.≤ᵇ⇒≤
      (proj₂ (Equivalence.to T-∧ bounded)))
  where
  upperNat : (+ n) ℤ.≤ (+ suc inner) → n ≤ suc inner
  upperNat (ℤ.+≤+ proof) = proof

negativeOuterMagnitudeBound :
  (inner n : Nat) →
  T (Cutoff.coordinateInCutoff? (suc inner) (-[1+ n ])) →
  n ≤ inner
negativeOuterMagnitudeBound inner n bounded =
  lowerNat
    (ℤP.≤ᵇ⇒≤
      (proj₁ (Equivalence.to T-∧ bounded)))
  where
  lowerNat :
    (ℤ.- (+ suc inner)) ℤ.≤ (-[1+ n ]) →
    n ≤ inner
  lowerNat (ℤ.-≤- proof) = proof

data SuccessorBoundaryCoordinate (inner : Nat) (z : ℤ) : Set where
  positiveEndpoint :
    z ≡ (+ suc inner) →
    SuccessorBoundaryCoordinate inner z
  negativeEndpoint :
    z ≡ (-[1+ inner ]) →
    SuccessorBoundaryCoordinate inner z

coordinateOnSuccessorBoundary :
  (inner : Nat) →
  (z : ℤ) →
  T (Cutoff.coordinateInCutoff? (suc inner) z) →
  Cutoff.coordinateInCutoff? inner z ≡ false →
  SuccessorBoundaryCoordinate inner z
coordinateOnSuccessorBoundary inner (+ n) outer innerFalse
  with NatP._≤?_ n inner
... | yes n≤inner =
  ⊥-elim
    (falseHasNoT
      (subst T innerFalse
        (positiveInCutoff inner n n≤inner)))
... | no n≰inner =
  let
    n≤next = positiveOuterMagnitudeBound inner n outer
    next≤n = NatP.≰⇒> n≰inner
    n≡next = NatP.≤-antisym n≤next next≤n
  in
  positiveEndpoint (cong +_ n≡next)
coordinateOnSuccessorBoundary zero (-[1+ n ]) outer innerFalse =
  caseZero n (negativeOuterMagnitudeBound zero n outer)
  where
  caseZero :
    (m : Nat) →
    m ≤ zero →
    SuccessorBoundaryCoordinate zero (-[1+ m ])
  caseZero zero z≤ = negativeEndpoint refl
  caseZero (suc m) ()
coordinateOnSuccessorBoundary (suc radius) (-[1+ n ]) outer innerFalse
  with NatP._≤?_ n radius
... | yes n≤radius =
  ⊥-elim
    (falseHasNoT
      (subst T innerFalse
        (negativeInCutoff
          (suc radius) n (s≤s n≤radius))))
... | no n≰radius =
  let
    n≤inner = negativeOuterMagnitudeBound (suc radius) n outer
    inner≤n = NatP.≰⇒> n≰radius
    n≡inner = NatP.≤-antisym n≤inner inner≤n
  in
  negativeEndpoint
    (cong (λ k → -[1+ k ]) n≡inner)

data SuccessorSquareBoundaryPoint
    (inner : Nat)
    (point : Lattice.LatticePoint) : Set where
  horizontalBoundary :
    SuccessorBoundaryCoordinate inner (Lattice.horizontal point) →
    SuccessorSquareBoundaryPoint inner point
  verticalBoundary :
    SuccessorBoundaryCoordinate inner (Lattice.vertical point) →
    SuccessorSquareBoundaryPoint inner point

successorSquareShellHasBoundaryCoordinate :
  (inner : Nat) →
  (point : Lattice.LatticePoint) →
  T (Shell.onSuccessorSquareShell? inner point) →
  SuccessorSquareBoundaryPoint inner point
successorSquareShellHasBoundaryCoordinate inner point shellProof =
  go
    (Cutoff.coordinateInCutoff? inner (Lattice.horizontal point))
    (Cutoff.coordinateInCutoff? inner (Lattice.vertical point))
    outerHorizontal outerVertical innerOutside
  where
  shellParts =
    Equivalence.to T-∧ shellProof

  outerAndOutside = shellParts
  outerSquare = proj₁ outerAndOutside
  innerOutside = proj₂ outerAndOutside

  outerParts = Equivalence.to T-∧ outerSquare
  outerHorizontal = proj₁ outerParts
  outerVertical = proj₂ outerParts

  go :
    (horizontalInner verticalInner : Bool) →
    T (Cutoff.coordinateInCutoff? (suc inner) (Lattice.horizontal point)) →
    T (Cutoff.coordinateInCutoff? (suc inner) (Lattice.vertical point)) →
    T (not (horizontalInner ∧ verticalInner)) →
    SuccessorSquareBoundaryPoint inner point
  go true true outerH outerV ()
  go false true outerH outerV outside =
    horizontalBoundary
      (coordinateOnSuccessorBoundary
        inner (Lattice.horizontal point) outerH refl)
  go true false outerH outerV outside =
    verticalBoundary
      (coordinateOnSuccessorBoundary
        inner (Lattice.vertical point) outerV refl)
  go false false outerH outerV outside =
    horizontalBoundary
      (coordinateOnSuccessorBoundary
        inner (Lattice.horizontal point) outerH refl)

radiusReal : Nat → BishopReal.ℝ
radiusReal inner = NatReal.natReal (suc inner)

radiusSquare : Nat → BishopReal.ℝ
radiusSquare inner = Norm.square (radiusReal inner)

positiveEndpointSquare :
  (inner : Nat) →
  BishopReal._≃_
    (Norm.square (Kernel.embedInteger (+ suc inner)))
    (radiusSquare inner)
positiveEndpointSquare inner = BishopP.≃-refl

negativeEndpointSquare :
  (inner : Nat) →
  BishopReal._≃_
    (Norm.square (Kernel.embedInteger (-[1+ inner ])))
    (radiusSquare inner)
negativeEndpointSquare inner =
  let open BishopP.ℝ-Solver in
  solve 1
    (λ r → (⊝ r) ⊗ (⊝ r) ⊜ r ⊗ r)
    BishopP.≃-refl (radiusReal inner)

coordinateBoundarySquare :
  (inner : Nat) →
  (z : ℤ) →
  SuccessorBoundaryCoordinate inner z →
  BishopReal._≃_
    (Norm.square (Kernel.embedInteger z))
    (radiusSquare inner)
coordinateBoundarySquare inner z (positiveEndpoint z≡)
  rewrite z≡ = positiveEndpointSquare inner
coordinateBoundarySquare inner z (negativeEndpoint z≡)
  rewrite z≡ = negativeEndpointSquare inner

leftSquareBelowSum :
  (left right : BishopReal.ℝ) →
  BishopReal._≤_
    (Norm.square left)
    (BishopReal._+_ (Norm.square left) (Norm.square right))
leftSquareBelowSum left right =
  BishopP.≤-respˡ-≃
    (BishopP.+-identityʳ (Norm.square left))
    (BishopP.+-monoʳ-≤
      (Norm.square left)
      (BishopP.nonNegx⇒0≤x
        (SquareNN.bishopSquareNonnegative right)))

rightSquareBelowSum :
  (left right : BishopReal.ℝ) →
  BishopReal._≤_
    (Norm.square right)
    (BishopReal._+_ (Norm.square left) (Norm.square right))
rightSquareBelowSum left right =
  BishopP.≤-respˡ-≃
    (BishopP.+-identityˡ (Norm.square right))
    (BishopP.+-monoˡ-≤
      (Norm.square right)
      (BishopP.nonNegx⇒0≤x
        (SquareNN.bishopSquareNonnegative left)))

successorSquareShellRadiusSquareLower :
  (inner : Nat) →
  (point : Lattice.LatticePoint) →
  T (Shell.onSuccessorSquareShell? inner point) →
  BishopReal._≤_
    (radiusSquare inner)
    (BishopReal._+_
      (Norm.square (Kernel.embedInteger (Lattice.horizontal point)))
      (Norm.square (Kernel.embedInteger (Lattice.vertical point))))
successorSquareShellRadiusSquareLower inner point shellProof
  with successorSquareShellHasBoundaryCoordinate inner point shellProof
... | horizontalBoundary boundary =
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm
      (coordinateBoundarySquare
        inner (Lattice.horizontal point) boundary))
    (leftSquareBelowSum
      (Kernel.embedInteger (Lattice.horizontal point))
      (Kernel.embedInteger (Lattice.vertical point)))
... | verticalBoundary boundary =
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm
      (coordinateBoundarySquare
        inner (Lattice.vertical point) boundary))
    (rightSquareBelowSum
      (Kernel.embedInteger (Lattice.horizontal point))
      (Kernel.embedInteger (Lattice.vertical point)))
