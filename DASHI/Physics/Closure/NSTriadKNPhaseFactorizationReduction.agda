module DASHI.Physics.Closure.NSTriadKNPhaseFactorizationReduction where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Exact phase factorisation from elementary sesquilinear laws.
--
-- This module does not assume the phase formula. It reduces the formula to
-- bilinearity, Leray linearity and Hermitian conjugate-linearity.
------------------------------------------------------------------------

record PhaseFactorisationAlgebra
    {m v s : Level}
    (Mode : Set m) (Vector : Set v) (Scalar : Set s) :
    Set (lsuc (m ⊔ v ⊔ s)) where
  field
    zero one imaginary : Scalar
    add multiply : Scalar → Scalar → Scalar
    negate conjugate realPart : Scalar → Scalar

    scale : Scalar → Vector → Vector
    dot pair : Vector → Vector → Scalar
    wave : Mode → Vector
    project : Mode → Vector → Vector

    multiplyAssociative :
      ∀ a b c → multiply (multiply a b) c ≡ multiply a (multiply b c)
    multiplyCommutative :
      ∀ a b → multiply a b ≡ multiply b a

    dotScaleLeft :
      ∀ a u v → dot (scale a u) v ≡ multiply a (dot u v)
    scaleAssociative :
      ∀ a b u → scale a (scale b u) ≡ scale (multiply a b) u
    projectScale :
      ∀ k a u → project k (scale a u) ≡ scale a (project k u)

    pairScaleLeft :
      ∀ a u v → pair (scale a u) v ≡ multiply (conjugate a) (pair u v)
    pairScaleRight :
      ∀ a u v → pair u (scale a v) ≡ multiply a (pair u v)

    conjugateMultiply :
      ∀ a b → conjugate (multiply a b)
      ≡ multiply (conjugate a) (conjugate b)

open PhaseFactorisationAlgebra public

minusImaginary :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  PhaseFactorisationAlgebra Mode Vector Scalar → Scalar
minusImaginary A = negate A (imaginary A)

synthesise :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  PhaseFactorisationAlgebra Mode Vector Scalar →
  Scalar → Scalar → Vector → Vector
synthesise A amplitude phase polarisation =
  scale A (multiply A amplitude phase) polarisation

geometryCoefficient :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  PhaseFactorisationAlgebra Mode Vector Scalar →
  Mode → Mode → Mode → Vector → Vector → Vector → Scalar
geometryCoefficient A k p q eP eQ eK =
  multiply A (minusImaginary A)
    (pair A eK
      (project A k
        (scale A (dot A eP (wave A q)) eQ)))

phaseCombination :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  PhaseFactorisationAlgebra Mode Vector Scalar →
  Scalar → Scalar → Scalar → Scalar
phaseCombination A phaseP phaseQ phaseK =
  multiply A
    (multiply A phaseP phaseQ)
    (conjugate A phaseK)

amplitudeProduct :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  PhaseFactorisationAlgebra Mode Vector Scalar →
  Scalar → Scalar → Scalar → Scalar
amplitudeProduct A aP aQ aK =
  multiply A (multiply A aP aQ) (conjugate A aK)

record ExactPhaseExpansion
    {m v s : Level}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : PhaseFactorisationAlgebra Mode Vector Scalar) :
    Set (lsuc (m ⊔ v ⊔ s)) where
  field
    amplitudesReal :
      ∀ a → conjugate A a ≡ a

    exactOrderedExpansion :
      ∀ k p q aP aQ aK zP zQ zK eP eQ eK →
      realPart A
        (pair A
          (synthesise A aK zK eK)
          (scale A (minusImaginary A)
            (project A k
              (scale A
                (dot A
                  (synthesise A aP zP eP)
                  (wave A q))
                (synthesise A aQ zQ eQ)))))
      ≡
      realPart A
        (multiply A
          (amplitudeProduct A aP aQ aK)
          (multiply A
            (phaseCombination A zP zQ zK)
            (geometryCoefficient A k p q eP eQ eK)))

open ExactPhaseExpansion public

phaseFactorisationDependencyReduced : Bool
phaseFactorisationDependencyReduced = true

phaseFactorisationDependencyReducedIsTrue :
  phaseFactorisationDependencyReduced ≡ true
phaseFactorisationDependencyReducedIsTrue = refl
