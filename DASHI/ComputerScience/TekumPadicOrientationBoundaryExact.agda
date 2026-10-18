module DASHI.ComputerScience.TekumPadicOrientationBoundaryExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as PAdic
import DASHI.Codec.TriadicPAdicCylinderExact as Cylinder
import DASHI.ComputerScience.TekumTruncationRoundingExact as Tekum
import DASHI.ComputerScience.TekumTriadicPAdicKernelBridgeExact as Bridge

------------------------------------------------------------------------
-- Critical orientation boundary.
--
-- In the Tekum representation used in this tranche, least-significant trits
-- are at the head and precision reduction removes low-order anchor trits.
-- A 3-adic cylinder, by contrast, retains the low-order prefix and forgets
-- newly added high-order digits when depth is reduced.
--
-- Therefore the two projections are not literally the same map.  A reversal /
-- dual coordinate chart is required before transporting the cylinder theorem
-- to Tekum nearest-rounding semantics.

tekumThreeToOne :
  Vec Trit.Trit 3 → Vec Trit.Trit 1
tekumThreeToOne = Tekum.truncateTwo

sampleWord : Vec Trit.Trit 3
sampleWord = Trit.neg ∷ Trit.zer ∷ Trit.pos ∷ []

tekumSampleKeepsHighTrit :
  tekumThreeToOne sampleWord ≡ Trit.pos ∷ []
tekumSampleKeepsHighTrit = refl

sampleStream : Cylinder.ResidualStream
sampleStream 0 = Trit.neg
sampleStream 1 = Trit.zer
sampleStream 2 = Trit.pos
sampleStream _ = Trit.zer

padicSampleDepthOne :
  PAdic.CylinderSystem.project Cylinder.canonicalTriadicCylinderSystem 1 sampleStream
  ≡ Trit.neg PAdic.∷ᵥ PAdic.[]ᵥ
padicSampleDepthOne = refl

tekumAndPadicDepthOneDiffer :
  Bridge.toKernel (tekumThreeToOne sampleWord)
  ≡ PAdic.CylinderSystem.project Cylinder.canonicalTriadicCylinderSystem 1 sampleStream
  → ⊥
tekumAndPadicDepthOneDiffer ()

record TekumPadicOrientationBoundary : Set where
  constructor tekumPadicOrientationBoundary
  field
    finiteTritCarrierIsShared : Bool
    tekumPrecisionDropsLowOrderAnchorTrits : Bool
    padicCylinderRefinementRetainsLowOrderPrefix : Bool
    literalProjectionIdentityWithoutReversal : Bool
    reversalOrDualChartRequiredForNaturalityTransport : Bool

canonicalTekumPadicOrientationBoundary : TekumPadicOrientationBoundary
canonicalTekumPadicOrientationBoundary =
  tekumPadicOrientationBoundary true true true false true
