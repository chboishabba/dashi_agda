module DASHI.Physics.MaskedNoLeakageBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Integer using (+_)
open import Data.Vec using (Vec; _++_)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.MaskedBlockOrthogonality as MBO

------------------------------------------------------------------------
-- Concrete masked version of the general no-leakage principle from
-- DASHI.Geometry.NoLeakageOrthogonality.
--
-- In the diagonal masked carrier, the core/tail decomposition is already
-- represented by concatenation and neutral block embeddings.  Therefore the
-- no-leakage energy equation and the orthogonality equation can be proved
-- directly, without importing the abstract additive-vector assumptions.

NoLeakageσ :
  ∀ {m k : Nat} →
  Vec IMQ.Sign m → Vec IMQ.Sign k → Set
NoLeakageσ {m} {k} σc σt =
  ∀ (c : Vec Trit m) (t : Vec Trit k) →
  IMQ.Qσ (σc ++ σt) (c ++ t)
    ≡ IMQ.Qσ σc c + IMQ.Qσ σt t

OrthogonalBlocksσ :
  ∀ {m k : Nat} →
  Vec IMQ.Sign m → Vec IMQ.Sign k → Set
OrthogonalBlocksσ {m} {k} σc σt =
  ∀ (c : Vec Trit m) (t : Vec Trit k) →
  IMQ.B2σ (σc ++ σt)
    (MBO.embedCore {m} {k} c)
    (MBO.embedTail {m} {k} t)
    ≡ + 0

masked-noLeakage :
  ∀ {m k : Nat}
    (σc : Vec IMQ.Sign m)
    (σt : Vec IMQ.Sign k) →
  NoLeakageσ σc σt
masked-noLeakage = MBO.Qσ-++

masked-orthogonal :
  ∀ {m k : Nat}
    (σc : Vec IMQ.Sign m)
    (σt : Vec IMQ.Sign k) →
  OrthogonalBlocksσ σc σt
masked-orthogonal = MBO.core⊥tail-B2σ

record MaskedNoLeakageClosure {m k : Nat}
  (σc : Vec IMQ.Sign m)
  (σt : Vec IMQ.Sign k) : Set where
  field
    noLeakage : NoLeakageσ σc σt
    orthogonal : OrthogonalBlocksσ σc σt

maskedNoLeakageClosure :
  ∀ {m k : Nat}
    (σc : Vec IMQ.Sign m)
    (σt : Vec IMQ.Sign k) →
  MaskedNoLeakageClosure σc σt
maskedNoLeakageClosure σc σt =
  record
    { noLeakage = masked-noLeakage σc σt
    ; orthogonal = masked-orthogonal σc σt
    }
