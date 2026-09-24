{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPhysicalOPERemainderSharedTailRound442Exact where

------------------------------------------------------------------------
-- C / ROUND442: PHYSICAL OPE REMAINDER = SHARED COMPOSITE-MARK TAIL.
--
-- Round83 already proves that the shared composite insertion tail is a
-- DyadicOPERemainderMajorant.  Therefore the Goal-1 C2 theorem is not another
-- decay estimate.  Once the physical product-expansion remainder is identified
-- with that SAME tail, its quantitative OPE modulus is compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _*_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.YangMillsSharedMarkedCompositeOPERemainderExact as SharedOPE
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

record PhysicalOPERemainderSharedTail
    (Index Scale Volume Root : Set) : Set₁ where
  field
    shared :
      Shared.SharedMarkedAnalyticShellControl Scale Volume Root

    scaleOf : Index → Scale
    volumeOf : Index → Volume
    rootOf : Index → Root

    -- Number of finite RG shells remaining after truncation at a given depth.
    remaining : Index → Nat → Nat

    physicalRemainderMagnitude : Index → Nat → ℚ

    -- The only genuine C2 same-object theorem.
    physicalRemainderIsCompositeTail :
      ∀ index depth →
      physicalRemainderMagnitude index depth
      ≡
      Shared.compositeInsertionTail shared
        (scaleOf index)
        (volumeOf index)
        (rootOf index)
        depth
        (remaining index depth)

open PhysicalOPERemainderSharedTail public

physicalRemainderMajorant :
  ∀ {Index Scale Volume Root} →
  PhysicalOPERemainderSharedTail Index Scale Volume Root →
  Index →
  Local.DyadicOPERemainderMajorant
physicalRemainderMajorant dataSet index =
  let
    sourceMajorant =
      SharedOPE.sharedCompositeAsDyadicOPERemainder
        (shared dataSet)
        (scaleOf dataSet index)
        (volumeOf dataSet index)
        (rootOf dataSet index)
        (remaining dataSet index)
  in
  record
    { Local.DyadicOPERemainderMajorant.coefficient =
        Local.coefficient sourceMajorant
    ; Local.DyadicOPERemainderMajorant.coefficientNonnegative =
        Local.coefficientNonnegative sourceMajorant
    ; Local.DyadicOPERemainderMajorant.remainderMagnitude =
        physicalRemainderMagnitude dataSet index
    ; Local.DyadicOPERemainderMajorant.remainderNonnegative =
        λ depth →
          subst
            (λ value → 0ℚ ≤ value)
            (sym (physicalRemainderIsCompositeTail dataSet index depth))
            (Local.remainderNonnegative sourceMajorant depth)
    ; Local.DyadicOPERemainderMajorant.remainderBelowDyadic =
        λ depth →
          subst
            (λ value →
              value
              ≤
              Local.coefficient sourceMajorant
                *
              Geo.halfPower depth)
            (sym (physicalRemainderIsCompositeTail dataSet index depth))
            (Local.remainderBelowDyadic sourceMajorant depth)
    }

physicalOPERemainderModulus :
  ∀ {Index Scale Volume Root}
    (dataSet : PhysicalOPERemainderSharedTail Index Scale Volume Root)
    index depth →
  physicalRemainderMagnitude dataSet index depth
  ≤
  Local.coefficient (physicalRemainderMajorant dataSet index)
    *
  Geo.halfPower depth
physicalOPERemainderModulus dataSet index =
  Local.explicitOPERemainderModulus
    (physicalRemainderMajorant dataSet index)

round442SharedCompositeTailCompilerLevel : ProofLevel
round442SharedCompositeTailCompilerLevel =
  SharedOPE.sharedMarkedCompositeOPERemainderCompilerLevel

round442PhysicalOPERemainderCompilerLevel : ProofLevel
round442PhysicalOPERemainderCompilerLevel = machineChecked

-- C2 is now exactly one physical identity.  No independent remainder-decay,
-- convergence, or dyadic-modulus theorem remains after this field is inhabited.
literalRound442PhysicalRemainderIsCompositeTailLevel : ProofLevel
literalRound442PhysicalRemainderIsCompositeTailLevel = conditional
