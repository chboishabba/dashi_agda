module DASHI.Unified.KKBraidMoonshineGaugeSameObjectCutExact where

-- Cross-sector same-object transport. Each map is supplied explicitly:
-- shared notation or matching finite symmetry is not a physical identification.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

record SectorComparison : Set₁ where
  field
    Source Field Representation Observable : Set
    physicalField : Source → Field
    represent : Field → Representation
    observeField : Field → Observable
    observeRepresentation : Representation → Observable
    representationSound :
      ∀ x → observeRepresentation (represent (physicalField x))
               ≡ observeField (physicalField x)
open SectorComparison public

-- An elementary and reusable compatibility theorem: if the represented
-- physical field agrees, all declared gauge-invariant observations agree.
sameFieldSameObservation :
  (S : SectorComparison) (x y : Source S) →
  physicalField S x ≡ physicalField S y →
  observeRepresentation S (represent S (physicalField S x))
    ≡ observeRepresentation S (represent S (physicalField S y))
sameFieldSameObservation S x y equalField =
  cong (λ f → observeRepresentation S (represent S f)) equalField

record KKYangMillsTransport : Set₁ where
  field
    Connection Curvature GaugeAction : Set
    curvature : Connection → Curvature
    transform : GaugeAction → Connection → Connection
    transformCurvature : GaugeAction → Curvature → Curvature
    curvatureEquivariant :
      ∀ u A → curvature (transform u A) ≡
              transformCurvature u (curvature A)

    GaugeInvariant : Set
    readout : Curvature → GaugeInvariant
    readoutGaugeInvariant :
      ∀ u F → readout (transformCurvature u F) ≡ readout F
open KKYangMillsTransport public

kkGaugeReadoutInvariant :
  (K : KKYangMillsTransport) (u : GaugeAction K) (A : Connection K) →
  readout K (curvature K (transform K u A)) ≡
  readout K (curvature K A)
kkGaugeReadoutInvariant K u A =
  trans (cong (readout K) (curvatureEquivariant K u A))
        (readoutGaugeInvariant K u (curvature K A))

-- A Monster/moonshine representation can serve as a Representation in
-- SectorComparison only after an actual map and commuting readout proof
-- are supplied; this record deliberately has no automatic inhabitant.
record MoonshinePhysicalPromotion
  (S : SectorComparison) : Set₁ where
  field
    PhysicalSource : Set
    toSector : PhysicalSource → Source S
    measurablePrediction : PhysicalSource → Observable S
    predictionMatches :
      ∀ x → measurablePrediction x ≡
             observeField S (physicalField S (toSector x))
open MoonshinePhysicalPromotion public
