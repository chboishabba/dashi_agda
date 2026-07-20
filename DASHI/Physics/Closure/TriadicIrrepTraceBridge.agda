module DASHI.Physics.Closure.TriadicIrrepTraceBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.TriadicFiniteIrrep as Irrep
import DASHI.Physics.Closure.TriadicSectorQSeries as QS

------------------------------------------------------------------------
-- A stable sector name is transported through the finite-depth transforms.
-- Its block trace is exactly the coefficient of the associated q-series.

record IrrepTraceBridge
  (C : QS.QSeriesCarrier) : Set₁ where
  field
    transformAtDepth :
      (n : Nat) →
      Irrep.FiniteCharacterTransform n

    StableSector : Set
    SectorAtDepth : Nat → Set

    sectorAtDepth :
      StableSector →
      (n : Nat) →
      SectorAtDepth n

    BlockOperator :
      (n : Nat) →
      SectorAtDepth n →
      Set

    operatorAtDepth :
      (n : Nat) →
      (s : StableSector) →
      BlockOperator n (sectorAtDepth s n)

    traceBlock :
      (n : Nat) →
      (sector : SectorAtDepth n) →
      BlockOperator n sector →
      QS.Coeff C

    traceTower : QS.SectorTraceTower C

    stableSectorMatchesTraceSector :
      StableSector ≡ QS.Sector traceTower

    traceCoefficientAgreement :
      (n : Nat) →
      (s : StableSector) →
      QS.traceCoefficient
        traceTower
        n
        (transportSector s)
      ≡ traceBlock
          n
          (sectorAtDepth s n)
          (operatorAtDepth n s)
      where
        transportSector : StableSector → QS.Sector traceTower
        transportSector s rewrite stableSectorMatchesTraceSector = s

    reductionPreservesTrackedSector : (n : Nat) → Set
    traceCompatibleAcrossDepth : (n : Nat) → Set

open IrrepTraceBridge public

------------------------------------------------------------------------
-- Promotion boundary.

traceBridgeStatement : String
traceBridgeStatement =
  "Each q-series coefficient is tied to the trace of an explicitly tracked finite representation block; the bridge also records sector and trace compatibility across quotient depth."

traceBridgeBoundary : String
traceBridgeBoundary =
  "A sequence of block traces is not automatically rational, Hecke eigen, modular, or p-adically interpolating. Those properties remain downstream gates."
