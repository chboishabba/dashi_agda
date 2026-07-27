module DASHI.Physics.Closure.NSTriadKNComplex3NullGainBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNResonantNullGain as Null

complexExt :
  ∀ {r} {F : C3.RealField r} {a b : C3.Complex F} →
  C3.real a ≡ C3.real b →
  C3.imaginary a ≡ C3.imaginary b →
  a ≡ b
complexExt {a = C3.complex ar ai} {b = C3.complex .ar .ai} refl refl = refl

complexAddZeroRight :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.complexAdd z (C3.complexZero F) ≡ z
complexAddZeroRight {F = F} (C3.complex real imaginary) =
  complexExt
    (trans
      (C3.addCommutative F real (C3.zero F))
      (C3.addZeroLeft F real))
    (trans
      (C3.addCommutative F imaginary (C3.zero F))
      (C3.addZeroLeft F imaginary))

record Complex3LinearCompletion
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) :
    Set (lsuc r) where
  field
    waveVectorAdd :
      ∀ p q →
      C3.modeVector E (Z3.addMode p q)
      ≡ C3.complex3Add (C3.modeVector E p) (C3.modeVector E q)

    dotAddRight :
      ∀ u v w →
      C3.bilinearDot3 u (C3.complex3Add v w)
      ≡ C3.complexAdd
          (C3.bilinearDot3 u v)
          (C3.bilinearDot3 u w)

open Complex3LinearCompletion public

complex3ResonantDotLaws :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) →
  Complex3LinearCompletion F E →
  Null.ResonantDotLaws (C3.Complex3 F) (C3.Complex F)
complex3ResonantDotLaws {F = F} E linear = record
  { scalarZero = C3.complexZero F
  ; scalarAdd = C3.complexAdd
  ; scalarAddZeroLeft = λ z →
      complexExt
        (C3.addZeroLeft F (C3.real z))
        (C3.addZeroLeft F (C3.imaginary z))
  ; scalarAddZeroRight = complexAddZeroRight
  ; vectorAdd = C3.complex3Add
  ; waveVector = C3.modeVector E
  ; bilinearDot = C3.bilinearDot3
  ; waveVectorAdd = waveVectorAdd linear
  ; dotAddRight = dotAddRight linear
  }

complex3ResonantNullP :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (linear : Complex3LinearCompletion F E)
    (τ : Physical.PhysicalTriadIncidence)
    (uP : C3.Complex3 F) →
  C3.bilinearDot3 uP (C3.modeVector E (Physical.p τ))
    ≡ C3.complexZero F →
  C3.bilinearDot3 uP (C3.modeVector E (Physical.q τ))
    ≡
  C3.bilinearDot3 uP (C3.modeVector E (Physical.k τ))
complex3ResonantNullP E linear =
  Null.resonantNullIdentityP (complex3ResonantDotLaws E linear)

complex3ResonantNullQ :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (linear : Complex3LinearCompletion F E)
    (τ : Physical.PhysicalTriadIncidence)
    (uQ : C3.Complex3 F) →
  C3.bilinearDot3 uQ (C3.modeVector E (Physical.q τ))
    ≡ C3.complexZero F →
  C3.bilinearDot3 uQ (C3.modeVector E (Physical.p τ))
    ≡
  C3.bilinearDot3 uQ (C3.modeVector E (Physical.k τ))
complex3ResonantNullQ E linear =
  Null.resonantNullIdentityQ (complex3ResonantDotLaws E linear)

complex3NullGainBridgeImplemented : Bool
complex3NullGainBridgeImplemented = true

complex3NullGainBridgeImplementedIsTrue :
  complex3NullGainBridgeImplemented ≡ true
complex3NullGainBridgeImplementedIsTrue = refl
