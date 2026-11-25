module DASHI.Reasoning.H07IntegerWindingExact where

-- Signed integer winding and its balanced residue, with quotient retained.
-- Reuse the original signed digit interpretation and integer ring solver.
-- The residue is not the independent Phase4 datum.
open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_])
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as BT
import DASHI.Reasoning.H07AffinePairedSeamExact as S
import DASHI.Reasoning.H07FullAtlasSectionExact as H
import DASHI.Reasoning.H07AtlasProjectionLawsExact as P
import DASHI.Reasoning.TypedHyperfabricCore as F

record WindingLift (n : ℤ) : Set where
  constructor lift
  field
    residue : Trit
    quotient : ℤ
    reconstruction : n ≡ BT.digitInteger residue Z.+ ((+ 3) Z.* quotient)

shiftPlus : {n : ℤ} → WindingLift n → WindingLift ((+ 3) Z.+ n)
shiftPlus (lift r q eq) = lift r ((+ 1) Z.+ q)
  (trans (cong ((+ 3) Z.+_) eq)
    (solve 2
      (λ d t →
        (con (+ 3) :+ (d :+ (con (+ 3) :* t)))
        := (d :+ (con (+ 3) :* (con (+ 1) :+ t))))
      refl (BT.digitInteger r) q))

shiftMinus : {n : ℤ} → WindingLift n → WindingLift ((-[1+ 2 ]) Z.+ n)
shiftMinus (lift r q eq) = lift r ((-[1+ 0 ]) Z.+ q)
  (trans (cong ((-[1+ 2 ]) Z.+_) eq)
    (solve 2
      (λ d t →
        (con (-[1+ 2 ]) :+ (d :+ (con (+ 3) :* t)))
        := (d :+ (con (+ 3) :* (con (-[1+ 0 ]) :+ t))))
      refl (BT.digitInteger r) q))

positiveLift : (n : Nat) → WindingLift (+ n)
positiveLift zero = lift zer (+ 0) refl
positiveLift (suc zero) = lift pos (+ 0) refl
positiveLift (suc (suc zero)) = lift neg (+ 1) refl
positiveLift (suc (suc (suc n))) =
  subst WindingLift (ZP.pos-+ 3 n) (shiftPlus (positiveLift n))

negativeLift : (n : Nat) → WindingLift (-[1+ n ])
negativeLift zero = lift neg (+ 0) refl
negativeLift (suc zero) = lift pos (-[1+ 0 ]) refl
negativeLift (suc (suc zero)) = lift zer (-[1+ 0 ]) refl
negativeLift (suc (suc (suc n))) = shiftMinus (negativeLift n)

integerLift : (n : ℤ) → WindingLift n
integerLift (+ n) = positiveLift n
integerLift (-[1+ n ]) = negativeLift n

-- No user-supplied unrelated trit can enter this integer-derived section.
-- Original context retains integer, history, time, depth, iteration,
-- version and Phase4. The lift additionally supplies the quotient.
record GovernedWindingContext : Set where
  constructor governedWinding
  field
    context : S.Context
    windingLift : WindingLift (S.Context.integerWinding context)

fromContext : (k : S.Context) → GovernedWindingContext
fromContext k = governedWinding k (integerLift (S.Context.integerWinding k))

sectionFromWinding : {L : H.Direction} (p : H.Mark L) → H.Vec5 →
  GovernedWindingContext → F.GlobalSection (H.fabric p)
sectionFromWinding p x (governedWinding k l) =
  P.atlasSection p x (WindingLift.residue l) k

integerAtlasSection : {L : H.Direction} (p : H.Mark L) → H.Vec5 →
  S.Context → F.GlobalSection (H.fabric p)
integerAtlasSection p x k = sectionFromWinding p x (fromContext k)

-- Source-written induction for every integer, not a bounded lookup.
-- This gives a linear-step-by-three specification, NOT a fast quotient
-- algorithm or kernel-certified proof. Use existing fast division if
-- a computational complexity claim is required.
