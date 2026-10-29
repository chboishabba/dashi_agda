module DASHI.Physics.Closure.R2P227729HermitianConvolutionTransportExact where

------------------------------------------------------------------------
-- EXACT HERMlTIAN 13-PAIR CODEC ↔ FINITE INTEGER CONVOLUTION CONSUMER
--
-- Original source-owner imports:
--  BalancedTernaryAntipodalOrbitExact          13 nonzero pairs of 27
--  C3CubeCyclotomicFourierExact               Q(omega), conjugation
--  R2P227729BilinearCyclotomicPadCutExact     actual 729 pair sums
--
-- New: for TWO arbitrary separate Hermitian Q(omega) coefficient fields,
-- pack (real centre + 13 Qω values), decode, and compute the original
-- true Z³ bilinear convolution. Every one of 125 coefficients is
-- identical. Also transports the exact 4³ retained and 5³ full INDEX
-- group-convolution equality through the codec.
--
-- This is NOT yet a 13-orbit reduced-complexity convolution algorithm:
-- the consumer may decode and enumerate all 729 signed pairs.
-- It does not prove actual C4/C5 Fourier sampled-field multiplication,
-- NS Clay regularity, R2P2 physics or Monster representation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Full
import DASHI.Physics.Closure.R2P227729BilinearCyclotomicPadCutExact as Bilinear
import DASHI.Physics.Closure.R2P227729HermitianThirteenPairFourierCodecExact as Hermitian
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as C3

compactFullBilinearAt :
  (a b : Hermitian.PackedHermitian27) →
  Full.WideCube125 → C3.Cyclotomic3
compactFullBilinearAt a b =
  Bilinear.trueBilinearConvolutionAt Bilinear.cyclotomicOps
    (Hermitian.packedMode a) (Hermitian.packedMode b)

originalFullBilinearAt :
  (a b : Hermitian.Hermitian27) →
  Full.WideCube125 → C3.Cyclotomic3
originalFullBilinearAt a b =
  Bilinear.trueBilinearConvolutionAt Bilinear.cyclotomicOps
    (Hermitian.coefficient a) (Hermitian.coefficient b)

compactPairWeightAfterPacking :
  (a b : Hermitian.Hermitian27)
  (target : Full.WideCube125)
  (pair : I.ModePair729) →
  Bilinear.exactContribution Bilinear.cyclotomicOps
    (Hermitian.packedMode (Hermitian.packHermitian27 a))
    (Hermitian.packedMode (Hermitian.packHermitian27 b))
    target pair
  ≡ Bilinear.exactContribution Bilinear.cyclotomicOps
      (Hermitian.coefficient a) (Hermitian.coefficient b)
      target pair
compactPairWeightAfterPacking a b target (p , q)
  rewrite Hermitian.decodeAfterEncodeHermitian27 a p
        | Hermitian.decodeAfterEncodeHermitian27 b q = refl

-- A genuine BIDI *consumer* preservation for arbitrary admissible
-- fields and ALL true wide integer output frequencies, not just 27.
compact13PairTransportPreservesAll125IntegerOutputs :
  (a b : Hermitian.Hermitian27)
  (target : Full.WideCube125) →
  compactFullBilinearAt
    (Hermitian.packHermitian27 a) (Hermitian.packHermitian27 b) target
  ≡ originalFullBilinearAt a b target
compact13PairTransportPreservesAll125IntegerOutputs a b target =
  Bilinear.sumUsingCong Bilinear.cyclotomicOps I.pair729
    (Bilinear.exactContribution Bilinear.cyclotomicOps
      (Hermitian.packedMode (Hermitian.packHermitian27 a))
      (Hermitian.packedMode (Hermitian.packHermitian27 b)) target)
    (Bilinear.exactContribution Bilinear.cyclotomicOps
      (Hermitian.coefficient a) (Hermitian.coefficient b) target)
    (compactPairWeightAfterPacking a b target)

compactFourGridRetainedAt :
  (a b : Hermitian.PackedHermitian27) →
  I.ModeCube27 → C3.Cyclotomic3
compactFourGridRetainedAt a b =
  Bilinear.fourGridBilinearRetainedAt Bilinear.cyclotomicOps
    (Hermitian.packedMode a) (Hermitian.packedMode b)

compactFiveGridFullAt :
  (a b : Hermitian.PackedHermitian27) →
  Full.WideCube125 → C3.Cyclotomic3
compactFiveGridFullAt a b =
  Bilinear.fiveGridBilinearFullAt Bilinear.cyclotomicOps
    (Hermitian.packedMode a) (Hermitian.packedMode b)

compact13PairsPreserveFourGridRetainedQuadratic :
  (a b : Hermitian.Hermitian27) (target : I.ModeCube27) →
  compactFourGridRetainedAt
    (Hermitian.packHermitian27 a) (Hermitian.packHermitian27 b)
    target
  ≡ originalFullBilinearAt a b (Full.retainedToWide target)
compact13PairsPreserveFourGridRetainedQuadratic a b target =
  trans
    (Bilinear.cyclotomicFourGridRetainedBilinearExact
      (Hermitian.packedMode (Hermitian.packHermitian27 a))
      (Hermitian.packedMode (Hermitian.packHermitian27 b)) target)
    (compact13PairTransportPreservesAll125IntegerOutputs
      a b (Full.retainedToWide target))

compact13PairsPreserveFiveGridFullQuadratic :
  (a b : Hermitian.Hermitian27) (target : Full.WideCube125) →
  compactFiveGridFullAt
    (Hermitian.packHermitian27 a) (Hermitian.packHermitian27 b)
    target
  ≡ originalFullBilinearAt a b target
compact13PairsPreserveFiveGridFullQuadratic a b target =
  trans
    (Bilinear.cyclotomicFiveGridFullBilinearExact
      (Hermitian.packedMode (Hermitian.packHermitian27 a))
      (Hermitian.packedMode (Hermitian.packHermitian27 b)) target)
    (compact13PairTransportPreservesAll125IntegerOutputs a b target)
