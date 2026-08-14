module DASHI.Cognition.PNF.FutureGeometryEmbeddingExact where

------------------------------------------------------------------------
-- LOW-RATE EMBEDDING OF CONSUMER-FUTURE GEOMETRY
--
-- The canonical future quotient determines which states may coincide.  A code
-- still has to realize a geometry.  This module separates an abstract future
-- metric from the code metric and gives compositional Lipschitz certificates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record NatDistance (Carrier : Set) : Set₁ where
  constructor natDistance
  field
    distance : Carrier → Carrier → Nat

open NatDistance public

record LipschitzRepresentation
    (State Code : Set)
    (futureMetric : NatDistance State)
    (codeMetric : NatDistance Code) : Set₁ where
  constructor lipschitzRepresentation
  field
    encode : State → Code
    constant : Nat
    upperGeometryBound :
      (left right : State) →
      distance codeMetric (encode left) (encode right)
      ≤ constant * distance futureMetric left right

open LipschitzRepresentation public

record CoLipschitzRepresentation
    (State Code : Set)
    (futureMetric : NatDistance State)
    (codeMetric : NatDistance Code) : Set₁ where
  constructor coLipschitzRepresentation
  field
    encodeCo : State → Code
    inverseConstant : Nat
    lowerGeometryBound :
      (left right : State) →
      distance futureMetric left right
      ≤ inverseConstant * distance codeMetric (encodeCo left) (encodeCo right)

open CoLipschitzRepresentation public

record BiLipschitzRepresentation
    (State Code : Set)
    (futureMetric : NatDistance State)
    (codeMetric : NatDistance Code) : Set₁ where
  constructor biLipschitzRepresentation
  field
    upper : LipschitzRepresentation State Code futureMetric codeMetric
    lower : CoLipschitzRepresentation State Code futureMetric codeMetric
    sameEncoder : encode upper ≡ encodeCo lower

open BiLipschitzRepresentation public

------------------------------------------------------------------------
-- Composition theorem: geometric distortion constants multiply.
------------------------------------------------------------------------

composeLipschitz :
  ∀ {A B C}
    {metricA : NatDistance A}
    {metricB : NatDistance B}
    {metricC : NatDistance C} →
  (first : LipschitzRepresentation A B metricA metricB) →
  (second : LipschitzRepresentation B C metricB metricC) →
  LipschitzRepresentation A C metricA metricC
composeLipschitz first second =
  lipschitzRepresentation
    (λ x → encode second (encode first x))
    (constant second * constant first)
    proof
  where
    proof : (left right : _) →
      distance _
        (encode second (encode first left))
        (encode second (encode first right))
      ≤ (constant second * constant first) * distance _ left right
    proof left right =
      ≤-trans
        (upperGeometryBound second (encode first left) (encode first right))
        (≤-trans
          (*-monoˡ-≤ (constant second)
            (upperGeometryBound first left right))
          (≤-reflexive (sym (*-assoc (constant second) (constant first)
            (distance _ left right)))))

------------------------------------------------------------------------
-- Geometry boundary: preserving one-step edges is weaker than a bi-Lipschitz
-- guarantee on all pairs.  WaveGrayLocalGlobalGeometryExact supplies a concrete
-- witness of that separation.
------------------------------------------------------------------------
