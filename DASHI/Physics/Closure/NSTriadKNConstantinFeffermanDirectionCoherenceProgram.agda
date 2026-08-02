module DASHI.Physics.Closure.NSTriadKNConstantinFeffermanDirectionCoherenceProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- Venue/year: Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
-- Uses: the deterministic geometric depletion mechanism in which coherence
-- of the physical-space vorticity direction weakens the singular
-- Biot--Savart vortex-stretching kernel.
-- Relationship: represents the result as a conditional physical-space
-- regularity route.  It is not identified with modal helicity, a normalized
-- Fourier coefficient, or an unconditional arbitrary-data theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record PhysicalVorticityDirectionCarrier
    {p t s v : Level} : Set (lsuc (p ⊔ t ⊔ s ⊔ v)) where
  field
    Point : Set p
    Time : Set t
    Scalar : Set s
    Vector : Set v

    zeroScalar : Scalar
    _≤_ : Scalar → Scalar → Set s
    add multiply : Scalar → Scalar → Scalar

    vorticity : Point → Time → Vector
    vorticityMagnitude : Point → Time → Scalar
    highVorticityThreshold : Scalar
    HighVorticity : Point → Time → Set s
    highVorticityDefinition :
      ∀ point time →
      HighVorticity point time →
      _≤_ highVorticityThreshold
           (vorticityMagnitude point time)

    direction :
      ∀ point time →
      HighVorticity point time →
      Vector

    distance : Point → Point → Scalar
    directionCrossMagnitude :
      ∀ x y time →
      HighVorticity x time →
      HighVorticity y time →
      Scalar

    CoherenceExponent : Set s
    coherencePower : CoherenceExponent → Scalar → Scalar
    coherenceConstant : Scalar
    physicalDirectionCoherence :
      CoherenceExponent → Set s

open PhysicalVorticityDirectionCarrier public

record ConstantinFeffermanKernelDepletion
    {p t s v : Level}
    (carrier : PhysicalVorticityDirectionCarrier {p} {t} {s} {v}) :
    Set (lsuc (p ⊔ t ⊔ s ⊔ v)) where
  field
    stretchingKernel :
      Point carrier → Point carrier → Time carrier → Scalar carrier
    singularKernelMagnitude :
      Point carrier → Point carrier → Scalar carrier
    determinantCancellation :
      ∀ x y time →
      HighVorticity carrier x time →
      HighVorticity carrier y time →
      Set s

    nearFieldDepletionFromDirectionCoherence :
      ∀ exponent →
      physicalDirectionCoherence carrier exponent →
      Set s
    farFieldControl : Set s
    vortexStretchingBound : Set s
    conditionalRegularityFromDirectionCoherence : Set s

open ConstantinFeffermanKernelDepletion public

record FourierTranslationAudit
    {m v s : Level} : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    Mode : Set m
    Vector : Set v
    Scalar : Set s

    modalVorticity : Mode → Vector
    physicalDirectionFourierCoefficient : Mode → Vector
    normalizeModalVorticity : Mode → Vector

    normalizationIsNonlinear : Set s
    directionFourierCoefficientContainsConvolutions : Set s
    normalizedModalVorticityIsNotPhysicalDirectionCoefficient : Set s

open FourierTranslationAudit public

constantinFeffermanRouteIsConditional : Bool
constantinFeffermanRouteIsConditional = true

constantinFeffermanRouteIsConditionalIsTrue :
  constantinFeffermanRouteIsConditional ≡ true
constantinFeffermanRouteIsConditionalIsTrue = refl

unconditionalDirectionCoherenceClosed : Bool
unconditionalDirectionCoherenceClosed = false

unconditionalDirectionCoherenceClosedIsFalse :
  unconditionalDirectionCoherenceClosed ≡ false
unconditionalDirectionCoherenceClosedIsFalse = refl

modalDirectionEqualsPhysicalDirectionFourierCoefficient : Bool
modalDirectionEqualsPhysicalDirectionFourierCoefficient = false

modalDirectionEqualsPhysicalDirectionFourierCoefficientIsFalse :
  modalDirectionEqualsPhysicalDirectionFourierCoefficient ≡ false
modalDirectionEqualsPhysicalDirectionFourierCoefficientIsFalse = refl
