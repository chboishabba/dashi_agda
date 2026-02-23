module DASHI.Physics.TernaryRealInstanceShift where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Relation.Binary.PropositionalEquality using (sym)
open import DASHI.Algebra.Trit using (Trit; zer)
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.RealOperatorStackShift as ROSS
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Geometry.RealIsotropy as RIS
open import DASHI.Geometry.RealFiniteSpeed as RFS
open import DASHI.Geometry.Isotropy as Iso
open import DASHI.Combinatorics.Entropy using (Involution)
import DASHI.Physics.RealClosureKitFiber as RKF
import DASHI.Physics.MaskedClosureKit as MK
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.SignatureFromMask as SFM
open import DASHI.Physics.DimensionBoundAssumptions as DBA
open import Data.Nat.Properties as NatP
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; replicate)

m′ : Nat
m′ = 5

m : Nat
m = suc m′

k : Nat
k = 4

n : Nat
n = m + k

orderLaws : SCC.OrderLaws
orderLaws =
  record
    { le-trans = NatP.≤-trans
    ; le-<-trans = NatP.≤-<-trans
    ; <-le-trans = NatP.<-≤-trans
    }

inv : Involution (RTC.Carrier n)
inv =
  record
    { ι = RTC.invVec
    ; invol = RTC.invVec-invol
    }

iso : RIS.RealIsotropy (FAM.ultrametricVec {n = n}) (λ x → ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
iso =
  record
    { iso = Iso.trivialIsotropy (FAM.ultrametricVec {n = n}) (λ x → ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
    ; coneInvariant = ⊤
    }

fs : RFS.RealFiniteSpeed (λ x → ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
fs =
  record
    { local = λ _ _ → ⊤
    ; preservesLocality = λ _ _ _ → tt
    }

obs : RTC.Carrier n → RTC.Carrier k
obs = TCP.tailOf m k

obs0 : RTC.Carrier k
obs0 = replicate k zer

obsT : RTC.Carrier k → RTC.Carrier k
obsT _ = obs0

obsFixed : obsT obs0 ≡ obs0
obsFixed = refl

obsUnique : ∀ o → obsT o ≡ o → o ≡ obs0
obsUnique o eq = sym eq

realKitFiber : RKF.RealClosureKitFiber
realKitFiber =
  record
    { S = RTC.Carrier n
    ; U = FAM.ultrametricVec {n = n}
    ; C = ROSS.C {m} {k}
    ; P = ROSS.P {m} {k}
    ; R = ROSS.R {m} {k}
    ; nonexpC = ROSS.nonexpC {m} {k}
    ; nonexpR = ROSS.nonexpR {m} {k}
    ; strictP-fiber = ROSS.strictP-fiber {m} {k}
    ; orderLaws = orderLaws
    ; Obs = RTC.Carrier k
    ; obs = obs
    ; obs0 = obs0
    ; obsT = obsT
    ; obsFixed = obsFixed
    ; obsUnique = obsUnique
    ; inv = inv
    ; iso = iso
    ; fs = fs
    }

------------------------------------------------------------------------
-- Masked quadratic closure kit (parameterized mask + orbit-profile seam)

mask : Vec IMQ.Sign m
mask = SFM.oneMinusRestPlus {m = m′}

postulate
  orbitProfile : DBA.ShellOrbitProfile m

maskKit : MK.RealClosureKitFiberMask
maskKit = MK.mkMaskKit {m = m} {k = k} realKitFiber mask orbitProfile
