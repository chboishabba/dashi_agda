module DASHI.Physics.MaskedSignature31Bridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec)

open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.SignatureFromMask as SFM
open import DASHI.Physics.MaskedCone as MC
open import DASHI.Physics.LorentzianCoreClosure as LCC

------------------------------------------------------------------------
-- Concrete content corresponding to the older abstract
-- DASHI.Geometry.Signature31AndDim3 interface.
--
-- The mask determines one negative and three positive directions.  The
-- spatial dimension is therefore read from the same finite object that
-- determines the quadratic signature; it is not introduced independently.

temporalCount₄ : SFM.countMinus MC.lorentzMask ≡ 1
temporalCount₄ = refl

spatialCount₄ : SFM.countPlus MC.lorentzMask ≡ 3
spatialCount₄ = refl

signature31₄ : SFM.signature MC.lorentzMask ≡ (1 , 3)
signature31₄ = MC.lorentzSignature

record MaskedSignature31Closure : Set where
  field
    mask : Vec IMQ.Sign 4
    temporal-one : SFM.countMinus mask ≡ 1
    spatial-three : SFM.countPlus mask ≡ 3
    signature-1+3 : SFM.signature mask ≡ (1 , 3)
    coreClosure : LCC.LorentzianCoreClosure

maskedSignature31Closure : MaskedSignature31Closure
maskedSignature31Closure =
  record
    { mask = MC.lorentzMask
    ; temporal-one = temporalCount₄
    ; spatial-three = spatialCount₄
    ; signature-1+3 = signature31₄
    ; coreClosure = LCC.lorentzianCoreClosure
    }
