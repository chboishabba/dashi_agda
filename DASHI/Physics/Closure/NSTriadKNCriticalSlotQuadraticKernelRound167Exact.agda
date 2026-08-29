module DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact where

------------------------------------------------------------------------
-- ROUND167 / THE SURVIVING SLOT DIFFERENCE HAS A QUADRATIC COMPANION KERNEL
--
-- Round166 shows the raw cubic slot-defect energy is too high in amplitude
-- degree to be the quartic Cauchy companion.  The correct object is already
-- latent in Round145.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157

normalizedDirection :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  Z3.FourierMode → C3.Complex3 F
normalizedDirection {F = F} E S k =
  C3.complex3Scale
    (C3.realEmbed F (Helical.inverseModeNorm S k))
    (C3.modeVector E k)

normalizedCurlIsICrossNormalizedDirection :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode)
    (u : C3.Complex3 F) →
  R142.normalizedCurl E S k u
  ≡ C3.complex3Scale (C3.complexI F)
      (Cross.complex3Cross (normalizedDirection E S k) u)
normalizedCurlIsICrossNormalizedDirection {F = F} E S k u =
  trans
    (R157.complex3ScaleNestedCommutes
      (C3.realEmbed F (Helical.inverseModeNorm S k))
      (C3.complexI F)
      (Cross.complex3Cross (C3.modeVector E k) u))
    (cong (C3.complex3Scale (C3.complexI F))
      (sym
        (R94.crossScaleLeft
          (C3.realEmbed F (Helical.inverseModeNorm S k))
          (C3.modeVector E k) u)))

complex3ScaleSubtract :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (u v : C3.Complex3 F) →
  C3.complex3Subtract
    (C3.complex3Scale scalar u)
    (C3.complex3Scale scalar v)
  ≡ C3.complex3Scale scalar (C3.complex3Subtract u v)
complex3ScaleSubtract {F = F} scalar
    (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Field.complex3Ext
    (R.solve 3
      (λ s u v → (s R.⊗ u) R.⊕ (R.⊝ (s R.⊗ v))
        R.⊜ s R.⊗ (u R.⊕ (R.⊝ v))) refl scalar ux vx)
    (R.solve 3
      (λ s u v → (s R.⊗ u) R.⊕ (R.⊝ (s R.⊗ v))
        R.⊜ s R.⊗ (u R.⊕ (R.⊝ v))) refl scalar uy vy)
    (R.solve 3
      (λ s u v → (s R.⊗ u) R.⊕ (R.⊝ (s R.⊗ v))
        R.⊜ s R.⊗ (u R.⊕ (R.⊝ v))) refl scalar uz vz)
  where module R = Ring.Solver F

normalizedCurlSlotVectorDifferenceIsIQuadraticKernel :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (p q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F) →
  C3.complex3Subtract
    (Cross.complex3Cross (R142.normalizedCurl E S p uP) uQ)
    (Cross.complex3Cross uP (R142.normalizedCurl E S q uQ))
  ≡
  C3.complex3Scale (C3.complexI F)
    (R145.slotKernel
      (normalizedDirection E S p)
      (normalizedDirection E S q)
      uP uQ)
normalizedCurlSlotVectorDifferenceIsIQuadraticKernel {F = F}
    E S p q uP uQ =
  trans
    (cong₂ C3.complex3Subtract
      (trans
        (cong (λ v → Cross.complex3Cross v uQ)
          (normalizedCurlIsICrossNormalizedDirection E S p uP))
        (R94.crossScaleLeft (C3.complexI F)
          (Cross.complex3Cross (normalizedDirection E S p) uP) uQ))
      (trans
        (cong (Cross.complex3Cross uP)
          (normalizedCurlIsICrossNormalizedDirection E S q uQ))
        (R94.crossScaleRight (C3.complexI F) uP
          (Cross.complex3Cross (normalizedDirection E S q) uQ))))
    (complex3ScaleSubtract (C3.complexI F)
      (Cross.complex3Cross
        (Cross.complex3Cross (normalizedDirection E S p) uP) uQ)
      (Cross.complex3Cross uP
        (Cross.complex3Cross (normalizedDirection E S q) uQ)))

round167NormalizedCurlSlotDifferenceHasQuadraticKernel : Bool
round167NormalizedCurlSlotDifferenceHasQuadraticKernel = true

round167QuadraticKernelHasCompanionAmplitudeDegree : Bool
round167QuadraticKernelHasCompanionAmplitudeDegree = true

round167QuadraticKernelL2BudgetClosed : Bool
round167QuadraticKernelL2BudgetClosed = false

round167PackageAClosed : Bool
round167PackageAClosed = false

round167NormalizedCurlSlotDifferenceHasQuadraticKernelIsTrue :
  round167NormalizedCurlSlotDifferenceHasQuadraticKernel ≡ true
round167NormalizedCurlSlotDifferenceHasQuadraticKernelIsTrue = refl

round167PackageAClosedIsFalse : round167PackageAClosed ≡ false
round167PackageAClosedIsFalse = refl
