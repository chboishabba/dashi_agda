module DASHI.Geometry.GeneralLeviCivitaTheoremBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- General Levi-Civita theorem boundary.
--
-- The mathematical theorem says that a sufficiently regular nondegenerate
-- metric determines a unique torsion-free metric-compatible connection.
-- This module does not postulate that result.  It records the exact abstract
-- ingredients a constructive producer must supply, and proves uniqueness once
-- the Koszul-determination witness has been supplied.

record SmoothMetricGeometry : Set₁ where
  constructor mkSmoothMetricGeometry
  field
    Point : Set
    Vector : Point → Set
    Scalar : Set
    Metric : (p : Point) → Vector p → Vector p → Scalar
    Connection : Set
    torsionFree : Connection → Set
    metricCompatible : Connection → Set
    sameConnection : Connection → Connection → Set
    geometryLabel : String

open SmoothMetricGeometry public

record LeviCivitaExistenceData (G : SmoothMetricGeometry) : Set where
  constructor mkLeviCivitaExistenceData
  field
    smoothStructureAvailable : Bool
    metricRegularEnough : Bool
    metricNondegenerate : Bool
    candidateConnection : Connection G
    candidateTorsionFree : torsionFree G candidateConnection
    candidateMetricCompatible : metricCompatible G candidateConnection
    existenceScope : String

open LeviCivitaExistenceData public

record KoszulDetermination
  (G : SmoothMetricGeometry)
  (data₀ : LeviCivitaExistenceData G) : Set where
  constructor mkKoszulDetermination
  field
    determine :
      (other : Connection G) →
      torsionFree G other →
      metricCompatible G other →
      sameConnection G other (candidateConnection data₀)
    determinationScope : String

open KoszulDetermination public

record GeneralLeviCivitaReceipt (G : SmoothMetricGeometry) : Set where
  constructor mkGeneralLeviCivitaReceipt
  field
    data₀ : LeviCivitaExistenceData G
    smoothReceipt : smoothStructureAvailable data₀ ≡ true
    regularityReceipt : metricRegularEnough data₀ ≡ true
    nondegeneracyReceipt : metricNondegenerate data₀ ≡ true
    KoszulReceipt : KoszulDetermination G data₀
    receiptScope : String

open GeneralLeviCivitaReceipt public

leviCivitaUnique :
  (G : SmoothMetricGeometry) →
  (receipt : GeneralLeviCivitaReceipt G) →
  (other : Connection G) →
  torsionFree G other →
  metricCompatible G other →
  sameConnection G other (candidateConnection (data₀ receipt))
leviCivitaUnique G receipt other torsion compatibility =
  determine (KoszulReceipt receipt) other torsion compatibility

record LeviCivitaPromotionBoundary : Set where
  constructor mkLeviCivitaPromotionBoundary
  field
    theoremSchemaImplemented : Bool
    internalSmoothManifoldDevelopment : Bool
    internalKoszulFormulaDerivation : Bool
    generalExistenceConstructed : Bool
    generalUniquenessDerivedWithoutImportedWitness : Bool
    boundaryStatement : String

open LeviCivitaPromotionBoundary public

canonicalLeviCivitaPromotionBoundary : LeviCivitaPromotionBoundary
canonicalLeviCivitaPromotionBoundary =
  mkLeviCivitaPromotionBoundary
    true false false false false
    "the general theorem interface and uniqueness eliminator are implemented; smooth geometry, Koszul derivation, and existence remain producer obligations"

canonicalGeneralLeviCivitaNotYetProved :
  generalExistenceConstructed canonicalLeviCivitaPromotionBoundary ≡ false
canonicalGeneralLeviCivitaNotYetProved = refl
