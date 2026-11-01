module DASHI.Physics.TernaryRealInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import DASHI.Algebra.Trit using (Trit; zer)
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.RealOperatorStack as ROS
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Geometry.RealIsotropy.Core as RIS
open import DASHI.Geometry.RealFiniteSpeed.Core as RFS
open import DASHI.Geometry.RealIsotropy.Instance.Core as RI
open import DASHI.Geometry.RealFiniteSpeed.Instance.Core as RF
open import DASHI.Geometry.Isotropy as Iso
open import DASHI.Combinatorics.Entropy using (Involution)
import DASHI.Physics.RealClosureKitFiber as RKF
open import DASHI.Physics.TOperator as TOp
open import Data.Nat.Properties as NatP
open import Data.Unit using (⊤; tt)
open import Data.Vec.Base using (last)
open import Data.Vec using (replicate)

m : Nat
m = 6

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

fp : RTC.Carrier n
fp = RTC.zeroVec {n}

inv : Involution (RTC.Carrier n)
inv =
  record
    { ι = RTC.invVec
    ; invol = RTC.invVec-invol
    }

iso : RIS.RealIsotropy (FAM.ultrametricVec {n = n}) (TOp.TOperator.T (record { C = ROS.C {n} ; P = ROS.P {n} ; R = ROS.R {n} }))
iso = RI.realIsotropyInstance {n = n}

fs : RFS.RealFiniteSpeed (TOp.TOperator.T (record { C = ROS.C {n} ; P = ROS.P {n} ; R = ROS.R {n} }))
fs = RF.realFiniteSpeedInstance {n = n}

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
    ; C = ROS.C {n}
    ; P = ROS.P {n}
    ; R = ROS.R {n}
    ; nonexpC = ROS.nonexpC {n}
    ; nonexpR = ROS.nonexpR {n}
    ; strictP-fiber = ROS.strictP-fiber {n}
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
