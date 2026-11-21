module DASHI.Analysis.GRHNative27ConsumerDescentExact where

-- Reuse the SAME native geometric 27 via its original reversible digit chart.
-- The exact consumer-sufficiency owner is QueryFactorisationSufficiency:
-- do not define a parallel FactorsThrough/Factorisation interface here.
-- No external GRH theorem is assumed by this finite geometric theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as G
import DASHI.Moonshine.JInvariant369Cube27CuspCodecNonIsometryExact as Chart
import DASHI.Core.QueryFactorisationSufficiency as Query

cong27 : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong27 f refl = refl

sym27 : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym27 refl = refl

pointConsumerQuestions :
  {Outcome : Set} (consumer : G.Ternary27Point → Outcome) →
  Query.InquiryQuestionFamily G.Ternary27Point ⊤
pointConsumerQuestions {Outcome} consumer =
  Query.inquiryQuestionFamily (λ _ → Outcome) (λ _ point → consumer point)

-- Every complete encoded point is sufficient for its original point-consumer.
-- This instantiates the canonical theorem record, not a new quotient ontology.
complete27ChartFactors :
  {Outcome : Set} (consumer : G.Ternary27Point → Outcome) →
  Query.FactorsThrough
    (pointConsumerQuestions consumer) Chart.encodeCubeDigits tt
complete27ChartFactors consumer =
  Query.factorsThrough
    (λ digits → consumer (Chart.decodeCubeDigits digits))
    (λ point → sym27 (cong27 consumer (Chart.decodeEncodeCube point)))

-- A geometrically marked 27 and its residue digits are two complete charts
-- of the same point set; the cyclic +1 adjacency is NOT the native grid edge.
carryCornerNotAnEdge :
  G.HypervoxelAdjacent G.positiveCorner G.negativeCorner → ⊥
carryCornerNotAnEdge = Chart.wrappedCornersAreNotGridAdjacent

carryMapsCorners :
  Chart.addOneCusp (Chart.encodeCubeDigits G.positiveCorner)
    ≡ Chart.encodeCubeDigits G.negativeCorner
carryMapsCorners = Chart.residueCarryWrapsSpatialCorners
