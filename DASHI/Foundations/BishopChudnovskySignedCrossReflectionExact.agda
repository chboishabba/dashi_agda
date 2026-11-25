module DASHI.Foundations.BishopChudnovskySignedCrossReflectionExact where

-- Source-written, uncompiled. Reflect the existing Q^u order constructor
-- on the actual O.window and Machin coordinates; no alternative real
-- or rational carrier, no postulate and no imported Lean proof.
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_)
import Data.Integer.Base as Z
import Data.Rational.Unnormalised as Q
import Real as R
import Sequence as S
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Stage
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as O
import DASHI.Foundations.BishopChudnovskyCrossOnlyEndpointExact as End

-- Q^u denominators are positive by construction. The signed numerator
-- is never replaced by its magnitude, including stage zero.
SignedLe : Q.ℚᵘ → Q.ℚᵘ → Set
SignedLe p q = Z._≤_ (Z._*_ (Q.↥ p) (Q.↧ q)) (Z._*_ (Q.↥ q) (Q.↧ p))

toOrder : ∀ {p q} → SignedLe p q → p Q.≤ q
toOrder = Q.*≤*

fromOrder : ∀ {p q} → p Q.≤ q → SignedLe p q
fromOrder (Q.*≤* h) = h

SignedCross : Nat → Set
SignedCross k =
  SignedLe (CH.lower (O.window k))
    (Stage.qMachinStage k Q.+ O.machinRadius k)
  × SignedLe (Stage.qMachinStage k)
    (CH.upper (O.window k) Q.+ O.machinRadius k)

toCross : (k : Nat) → SignedCross k →
  O.Cross (O.window k) (Stage.qMachinStage k) (O.machinRadius k)
toCross k (lo , hi) = O.cross (toOrder lo) (toOrder hi)

fromCross : (k : Nat) →
  O.Cross (O.window k) (Stage.qMachinStage k) (O.machinRadius k) →
  SignedCross k
fromCross k c = fromOrder (O.lowerCross c) , fromOrder (O.upperCross c)

-- Same original endpoint, but its unresolved premise is now literally
-- the two signed integer comparisons at each index. A finite receipt,
-- content hash or external boolean does not inhabit this function.
literalConvergenceFromSignedCross :
  ((k : Nat) → SignedCross k) →
  S._ConvergesTo_ (λ k → R._⋆ (CH.midpoint (O.window k))) M.bishopMachinPi
literalConvergenceFromSignedCross c =
  End.literalConvergenceFromCrossOnly (λ k → toCross k (c k))
