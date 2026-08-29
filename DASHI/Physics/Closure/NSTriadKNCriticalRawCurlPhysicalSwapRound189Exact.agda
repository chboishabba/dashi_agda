module DASHI.Physics.Closure.NSTriadKNCriticalRawCurlPhysicalSwapRound189Exact where

------------------------------------------------------------------------
-- ROUND189 / PHYSICAL p/q SWAP LAW FOR RAW-CURL CRITICAL PRODUCTION
--
-- Round188 proves the scalar compiler assuming the physical slot transform
--
--   (C_k,C_p,C_q) -> (-C_k,-C_q,-C_p).
--
-- This file proves that transform on the literal C^3 Waleffe amplitude from
-- cross-product antisymmetry and then instantiates Round188.  Therefore the
-- complete physical raw-curl critical production is exactly invariant under
-- p/q swap.
--
-- This is strategically important: the old partner involution is still useful
-- for exposing multiplier differences and organising Bony classes, but at the
-- COMPLETE raw-curl-production level it is not a cancellation mechanism.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicityWalshPhysicalAmplitudeRound140Exact as R140
import DASHI.Physics.Closure.NSTriadKNCriticalRawCurlRadialGapRound169Exact as R169
import DASHI.Physics.Closure.NSTriadKNCriticalRawCurlPhysicalWeldRound170Exact as R170
import DASHI.Physics.Closure.NSTriadKNCriticalRawCurlSwapAlgebraRound188Exact as R188

crossSwapNegate :
  ∀ {r} {F : C3.RealField r}
    (p q : C3.Complex3 F) →
  Cross.complex3Cross q p
  ≡ C3.complex3Negate (Cross.complex3Cross p q)
crossSwapNegate {F = F}
    (C3.complex3 px py pz)
    (C3.complex3 qx qy qz) =
  Algebra.complex3Ext
    (R.solve 4
      (λ py pz qy qz →
        ((qy R.⊗ pz) R.⊕ (R.⊝ (qz R.⊗ py)))
        R.⊜
        (R.⊝ ((py R.⊗ qz) R.⊕ (R.⊝ (pz R.⊗ qy)))))
      refl py pz qy qz)
    (R.solve 4
      (λ pz px qz qx →
        ((qz R.⊗ px) R.⊕ (R.⊝ (qx R.⊗ pz)))
        R.⊜
        (R.⊝ ((pz R.⊗ qx) R.⊕ (R.⊝ (px R.⊗ qz)))))
      refl pz px qz qx)
    (R.solve 4
      (λ px py qx qy →
        ((qx R.⊗ py) R.⊕ (R.⊝ (qy R.⊗ px)))
        R.⊜
        (R.⊝ ((px R.⊗ qy) R.⊕ (R.⊝ (py R.⊗ qx)))))
      refl px py qx qy)
  where module R = Ring.Solver F

realComplexNegate :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.real (C3.complexNegate z) ≡ C3.negate F (C3.real z)
realComplexNegate (C3.complex zr zi) = refl

realAmplitudeSwapPQ :
  ∀ {r} {F : C3.RealField r}
    (k p q : C3.Complex3 F) →
  R140.realAmplitude k q p
  ≡ C3.negate F (R140.realAmplitude k p q)
realAmplitudeSwapPQ {F = F} k p q =
  trans
    (cong
      (λ cross → C3.real (C3.hermitianPairing3 k cross))
      (crossSwapNegate p q))
    (trans
      (cong C3.real
        (Additive.hermitianPairingNegateRight
          k (Cross.complex3Cross p q)))
      (realComplexNegate
        (C3.hermitianPairing3 k (Cross.complex3Cross p q))))

rawCurlSlotKSwapSign :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (k : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) →
  R170.rawCurlSlotK E k uK uQ uP
  ≡ C3.negate F (R170.rawCurlSlotK E k uK uP uQ)
rawCurlSlotKSwapSign E k uK uP uQ =
  realAmplitudeSwapPQ (Helical.curlSymbol E k uK) uP uQ

rawCurlSlotPSwapIsNegQ :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (q : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) →
  R170.rawCurlSlotP E q uK uQ uP
  ≡ C3.negate F (R170.rawCurlSlotQ E q uK uP uQ)
rawCurlSlotPSwapIsNegQ E q uK uP uQ =
  realAmplitudeSwapPQ uK uP (Helical.curlSymbol E q uQ)

rawCurlSlotQSwapIsNegP :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (p : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) →
  R170.rawCurlSlotQ E p uK uQ uP
  ≡ C3.negate F (R170.rawCurlSlotP E p uK uP uQ)
rawCurlSlotQSwapIsNegP E p uK uP uQ =
  realAmplitudeSwapPQ uK (Helical.curlSymbol E p uP) uQ

physicalRawCurlProductionSwapInvariant :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (rk rp rq : C3.Carrier F)
    (k p q : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) →
  R169.rawCurlGapProduction rk rq rp
    (R170.rawCurlSlotK E k uK uQ uP)
    (R170.rawCurlSlotP E q uK uQ uP)
    (R170.rawCurlSlotQ E p uK uQ uP)
  ≡
  R169.rawCurlGapProduction rk rp rq
    (R170.rawCurlSlotK E k uK uP uQ)
    (R170.rawCurlSlotP E p uK uP uQ)
    (R170.rawCurlSlotQ E q uK uP uQ)
physicalRawCurlProductionSwapInvariant {F = F}
    E rk rp rq k p q uK uP uQ
  rewrite rawCurlSlotKSwapSign E k uK uP uQ
        | rawCurlSlotPSwapIsNegQ E q uK uP uQ
        | rawCurlSlotQSwapIsNegP E p uK uP uQ =
  R188.rawCurlGapProductionSwapInvariant
    rk rp rq
    (R170.rawCurlSlotK E k uK uP uQ)
    (R170.rawCurlSlotP E p uK uP uQ)
    (R170.rawCurlSlotQ E q uK uP uQ)

round189PhysicalRawCurlProductionSwapInvariant : Bool
round189PhysicalRawCurlProductionSwapInvariant = true

round189FullSwapOrbitProvidesCancellation : Bool
round189FullSwapOrbitProvidesCancellation = false

round189StaticPartnerCancellationRouteClosed : Bool
round189StaticPartnerCancellationRouteClosed = false

round189TrajectoryDoubleCommutatorRemainsHighestAlpha : Bool
round189TrajectoryDoubleCommutatorRemainsHighestAlpha = true

round189PackageAClosed : Bool
round189PackageAClosed = false

round189ClayPromotion : Bool
round189ClayPromotion = false
