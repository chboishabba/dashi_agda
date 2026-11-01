module DASHI.Physics.Plasma.MHDOrderedPairInductionCurlBidiExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; _≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State
import DASHI.Physics.Plasma.MHDDoubledMagneticElsasserFibreExact as Doubled
import DASHI.Physics.Plasma.MHDDoubledInductionVectorKernelWeldExact as Kernel
import DASHI.Physics.Plasma.MHDComplex3VectorTripleProductExact as Triple

------------------------------------------------------------------------
-- ORDERED-PAIR INDUCTION IS THE CURL OF TWO U x B ORIENTATIONS
------------------------------------------------------------------------

doubledVelocity :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  State.IdealElsasserFourierState F E →
  Z3.FourierMode → C3.Complex3 F
doubledVelocity state k =
  C3.complex3Add (State.zPlus state k) (State.zMinus state k)

doubledVelocityTransverse :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (k : Z3.FourierMode) →
  C3.bilinearDot3 (C3.modeVector E k) (doubledVelocity state k)
  ≡ C3.complexZero F
doubledVelocityTransverse {F = F} {E = E} state k =
  trans
    (Algebra.bilinearDot3RightAdd
      (C3.modeVector E k) (State.zPlus state k) (State.zMinus state k))
    (trans
      (cong₂ C3.complexAdd
        (State.plusDivergenceFree state k)
        (State.minusDivergenceFree state k))
      (Field.complexAddZeroLeft (C3.complexZero F)))

inductionKernel :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
inductionKernel q up bp uq bq =
  C3.complex3Subtract
    (C3.complex3Scale (C3.bilinearDot3 up q) bq)
    (C3.complex3Scale (C3.bilinearDot3 bp q) uq)

curlChunk :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F
curlChunk p q up bq =
  C3.complex3Subtract
    (C3.complex3Scale (C3.bilinearDot3 up q) bq)
    (C3.complex3Scale (C3.bilinearDot3 bq p) up)

kernelPairRegroupsIntoCurlChunks :
  ∀ {r : Level} {F : C3.RealField r}
    (p q up bp uq bq : C3.Complex3 F) →
  C3.complex3Add
    (inductionKernel q up bp uq bq)
    (inductionKernel p uq bq up bp)
  ≡
  C3.complex3Add
    (curlChunk p q up bq)
    (curlChunk q p uq bp)
kernelPairRegroupsIntoCurlChunks {F = F}
    p q
    (C3.complex3 upx upy upz)
    (C3.complex3 bpx bpy bpz)
    (C3.complex3 uqx uqy uqz)
    (C3.complex3 bqx bqy bqz) =
  Field.complex3Ext
    (coordinate upx bpx uqx bqx)
    (coordinate upy bpy uqy bqy)
    (coordinate upz bpz uqz bqz)
  where
  a = C3.bilinearDot3 (C3.complex3 upx upy upz) q
  b = C3.bilinearDot3 (C3.complex3 bpx bpy bpz) q
  c = C3.bilinearDot3 (C3.complex3 uqx uqy uqz) p
  d = C3.bilinearDot3 (C3.complex3 bqx bqy bqz) p

  coordinate :
    (up bp uq bq : C3.Complex F) →
    C3.complexAdd
      (C3.complexSubtract (C3.complexMultiply a bq) (C3.complexMultiply b uq))
      (C3.complexSubtract (C3.complexMultiply c bp) (C3.complexMultiply d up))
    ≡
    C3.complexAdd
      (C3.complexSubtract (C3.complexMultiply a bq) (C3.complexMultiply d up))
      (C3.complexSubtract (C3.complexMultiply c bp) (C3.complexMultiply b uq))
  coordinate up bp uq bq =
    R.solve 8
      (λ a b c d up bp uq bq →
        ((((a R.⊗ bq) R.⊕ (R.⊝ (b R.⊗ uq)))
          R.⊕ ((c R.⊗ bp) R.⊕ (R.⊝ (d R.⊗ up))))
        R.⊜
        (((a R.⊗ bq) R.⊕ (R.⊝ (d R.⊗ up)))
          R.⊕ ((c R.⊗ bp) R.⊕ (R.⊝ (b R.⊗ uq)))))
      refl a b c d up bp uq bq
    where module R = Ring.Solver F

physicalOutputWaveIsInputSum :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (tau : Physical.PhysicalTriadIncidence) →
  C3.modeVector E (Physical.k tau)
  ≡ C3.complex3Add
      (C3.modeVector E (Physical.p tau))
      (C3.modeVector E (Physical.q tau))
physicalOutputWaveIsInputSum E tau =
  trans
    (sym (cong (C3.modeVector E) (Physical.resonance tau)))
    (Algebra.modeVectorAdd E (Physical.p tau) (Physical.q tau))

physicalCurlChunkIsNegativeCrossCurl :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  curlChunk
    (C3.modeVector E (Physical.p tau))
    (C3.modeVector E (Physical.q tau))
    (doubledVelocity state (Physical.p tau))
    (Doubled.doubledMagnetic state (Physical.q tau))
  ≡
  C3.complex3Negate
    (Cross.complex3Cross
      (C3.modeVector E (Physical.k tau))
      (Cross.complex3Cross
        (doubledVelocity state (Physical.p tau))
        (Doubled.doubledMagnetic state (Physical.q tau))))
physicalCurlChunkIsNegativeCrossCurl {F = F} {E = E} E state tau =
  Triple.inductionKernelIsNegativeCurlCross
    (C3.modeVector E (Physical.p tau))
    (C3.modeVector E (Physical.q tau))
    (C3.modeVector E (Physical.k tau))
    (doubledVelocity state (Physical.p tau))
    (Doubled.doubledMagnetic state (Physical.q tau))
    (Triple.resonant-induction-geometry
      (physicalOutputWaveIsInputSum E tau)
      (doubledVelocityTransverse state (Physical.p tau))
      (Doubled.doubledMagneticTransverse state (Physical.q tau)))

physicalOrderedPairKernelIsTwoNegativeCurlCrosses :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  C3.complex3Add
    (inductionKernel
      (C3.modeVector E (Physical.q tau))
      (doubledVelocity state (Physical.p tau))
      (Doubled.doubledMagnetic state (Physical.p tau))
      (doubledVelocity state (Physical.q tau))
      (Doubled.doubledMagnetic state (Physical.q tau)))
    (inductionKernel
      (C3.modeVector E (Physical.p tau))
      (doubledVelocity state (Physical.q tau))
      (Doubled.doubledMagnetic state (Physical.q tau))
      (doubledVelocity state (Physical.p tau))
      (Doubled.doubledMagnetic state (Physical.p tau)))
  ≡
  C3.complex3Add
    (C3.complex3Negate
      (Cross.complex3Cross
        (C3.modeVector E (Physical.k tau))
        (Cross.complex3Cross
          (doubledVelocity state (Physical.p tau))
          (Doubled.doubledMagnetic state (Physical.q tau)))))
    (C3.complex3Negate
      (Cross.complex3Cross
        (C3.modeVector E (Physical.k tau))
        (Cross.complex3Cross
          (doubledVelocity state (Physical.q tau))
          (Doubled.doubledMagnetic state (Physical.p tau)))))
physicalOrderedPairKernelIsTwoNegativeCurlCrosses E state tau =
  trans
    (kernelPairRegroupsIntoCurlChunks
      (C3.modeVector E (Physical.p tau))
      (C3.modeVector E (Physical.q tau))
      (doubledVelocity state (Physical.p tau))
      (Doubled.doubledMagnetic state (Physical.p tau))
      (doubledVelocity state (Physical.q tau))
      (Doubled.doubledMagnetic state (Physical.q tau)))
    (cong₂ C3.complex3Add
      (physicalCurlChunkIsNegativeCrossCurl E state tau)
      (physicalCurlChunkIsNegativeCrossCurl E state (Symmetry.swapTriad tau)))

record OrderedPairInductionCurlBoundary : Set where
  constructor ordered-pair-induction-curl-boundary
  field
    singleOrderedKernelIsAlreadyCurlForm : Bool
    singleOrderedKernelIsAlreadyCurlFormIsFalse :
      singleOrderedKernelIsAlreadyCurlForm ≡ false

    orderedPairRegroupingOwned : Bool
    orderedPairRegroupingOwnedIsTrue : orderedPairRegroupingOwned ≡ true

    physicalOrderedPairCurlFormOwned : Bool
    physicalOrderedPairCurlFormOwnedIsTrue : physicalOrderedPairCurlFormOwned ≡ true

canonicalOrderedPairInductionCurlBoundary : OrderedPairInductionCurlBoundary
canonicalOrderedPairInductionCurlBoundary =
  ordered-pair-induction-curl-boundary false refl true refl true refl
