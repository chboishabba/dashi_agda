module DASHI.Analysis.GRHNative27ConsumerDescentExact where

-- The principal 27 digit chart is explicitly tied to the SAME native
-- 3×3×3 geometric carrier. This is not a mere count-of-27 replacement.
-- Source owners are reused; no new residue or cube datatype is introduced.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as G
import DASHI.Moonshine.JInvariant369Cube27CuspCodecNonIsometryExact as Chart

-- Every consumer on original points can be reconstructed from the
-- complete three-coordinate residue chart, using the original inverse.
-- This proves consumer-specific FactorsThrough at this precise granularity.
record Factorisation {State Surface Outcome : Set}
    (project : State → Surface)
    (consumer : State → Outcome) : Set where
  field
    recovered : Surface → Outcome
    factors : (s : State) →
      consumer s ≡ recovered (project s)

complete27ChartFactors :
  {Outcome : Set} (consumer : G.Ternary27Point → Outcome) →
  Factorisation Chart.encodeCubeDigits consumer
complete27ChartFactors consumer = record
  { recovered = λ digits → consumer (Chart.decodeCubeDigits digits)
  ; factors = λ p → sym (cong consumer (Chart.decodeEncodeCube p))
  }
  where
    cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
    cong f refl = refl
    sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

-- The geometric edge relation is not the cycle's +1 successor.
-- A digit chart is a geometric COORDINATE CHART with transported
-- geometry, not permission to substitute a different edge relation.
carryCornerNotAnEdge :
  G.HypervoxelAdjacent G.positiveCorner G.negativeCorner → ⊥
carryCornerNotAnEdge = Chart.wrappedCornersAreNotGridAdjacent

carryMapsCorners :
  Chart.addOneCusp (Chart.encodeCubeDigits G.positiveCorner)
    ≡ Chart.encodeCubeDigits G.negativeCorner
carryMapsCorners = Chart.residueCarryWrapsSpatialCorners
