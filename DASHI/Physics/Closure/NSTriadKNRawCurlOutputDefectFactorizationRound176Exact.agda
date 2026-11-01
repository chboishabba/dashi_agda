module DASHI.Physics.Closure.NSTriadKNRawCurlOutputDefectFactorizationRound176Exact where

------------------------------------------------------------------------
-- ROUND176 / RAW p/q CURL SLOT DIFFERENCE FACTORS THROUGH THE LITERAL OUTPUT
--
-- Once Round171 removes the normalized-curl inverse radii, the p/q raw-curl
-- slot difference can be treated with the wavevectors themselves.  Round145
-- is generic in its two direction vectors, so put P=p and Q=q.  Resonance
-- p+q=k then identifies the anti-parallel defect P+Q EXACTLY with the literal
-- output vector k.  Consequently the entire raw p/q slot kernel is a low-
-- output object before any norm estimate or Bony counting.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3RelocationInstantiation as Relocation
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145

literalWavePairTransverse :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (p q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F) →
  Helical.Transverse E p uP →
  Helical.Transverse E q uQ →
  R145.TransverseHighPair
    (C3.modeVector E p) (C3.modeVector E q) uP uQ
literalWavePairTransverse E p q uP uQ pTrans qTrans =
  R145.transverse-high-pair
    (Relocation.transverseRightOrientation E p uP pTrans)
    (Relocation.transverseRightOrientation E q uQ qTrans)

resonantAntiParallelDefectIsOutputVector :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode} →
  Z3.Resonance p q k →
  R145.antiParallelDefect (C3.modeVector E p) (C3.modeVector E q)
  ≡ C3.modeVector E k
resonantAntiParallelDefectIsOutputVector E {p} {q} {k} resonance =
  trans
    (sym (Algebra.modeVectorAdd E p q))
    (cong (C3.modeVector E) (Z3.Resonance.closes resonance))

rawPQSlotKernelFactorsThroughLiteralOutput :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode}
    (uP uQ : C3.Complex3 F) →
  Z3.Resonance p q k →
  Helical.Transverse E p uP →
  Helical.Transverse E q uQ →
  R145.slotKernel (C3.modeVector E p) (C3.modeVector E q) uP uQ
  ≡
  C3.complex3Subtract
    (C3.complex3Add
      (C3.complex3Scale
        (C3.bilinearDot3 (C3.modeVector E k) uQ) uP)
      (C3.complex3Scale
        (C3.bilinearDot3 uP (C3.modeVector E k)) uQ))
    (C3.complex3Scale
      (C3.bilinearDot3 uP uQ)
      (C3.modeVector E k))
rawPQSlotKernelFactorsThroughLiteralOutput E {p} {q} {k} uP uQ
    resonance pTrans qTrans =
  let
    T = literalWavePairTransverse E p q uP uQ pTrans qTrans
    outputMeaning = resonantAntiParallelDefectIsOutputVector E resonance
  in
  trans
    (R145.slotKernelFactorsThroughAntiParallelDefect
      (C3.modeVector E p) (C3.modeVector E q) uP uQ T)
    (cong
      (λ output →
        C3.complex3Subtract
          (C3.complex3Add
            (C3.complex3Scale (C3.bilinearDot3 output uQ) uP)
            (C3.complex3Scale (C3.bilinearDot3 uP output) uQ))
          (C3.complex3Scale (C3.bilinearDot3 uP uQ) output))
      outputMeaning)

round176RawPQSlotKernelLiteralOutputFactorizationClosed : Bool
round176RawPQSlotKernelLiteralOutputFactorizationClosed = true

round176AnglePartitionNeeded : Bool
round176AnglePartitionNeeded = false

round176InverseRadiusPresent : Bool
round176InverseRadiusPresent = false

round176LiteralOutputKernelL2PaymentClosed : Bool
round176LiteralOutputKernelL2PaymentClosed = false

round176PackageAClosed : Bool
round176PackageAClosed = false

round176RawPQSlotKernelLiteralOutputFactorizationClosedIsTrue :
  round176RawPQSlotKernelLiteralOutputFactorizationClosed ≡ true
round176RawPQSlotKernelLiteralOutputFactorizationClosedIsTrue = refl

round176PackageAClosedIsFalse : round176PackageAClosed ≡ false
round176PackageAClosedIsFalse = refl
