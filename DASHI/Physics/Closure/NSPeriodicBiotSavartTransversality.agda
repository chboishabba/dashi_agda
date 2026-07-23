module DASHI.Physics.Closure.NSPeriodicBiotSavartTransversality where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact algebraic transversality of the frozen Fourier Biot-Savart map.
--
-- The norm estimate is still analytic, but divergence-freeness itself follows
-- from k dot (k cross omega) = 0 and compatibility of dot product with scalar
-- multiplication.  This removes that identity from the list of assumptions
-- that the official carrier must repeatedly restate.
------------------------------------------------------------------------

record FourierBiotSavartTransversalityLaws
    {m v s : Level}
    {Mode : Set m}
    {Vector : Set v}
    {Scalar : Set s}
    (L : FourierVectorLaws Mode Vector Scalar) :
    Set (lsuc (m ⊔ v ⊔ s)) where
  field
    dotScaleRight : ∀ x coefficient y →
      vectorDot L x (vectorScale L coefficient y) ≡
      scalarMultiply L coefficient (vectorDot L x y)

    waveDotOwnCrossIsZero : ∀ mode omega →
      vectorDot L
        (waveVector L mode)
        (vectorCross L (waveVector L mode) omega)
      ≡ scalarZero L

    multiplyZeroRight : ∀ coefficient →
      scalarMultiply L coefficient (scalarZero L) ≡ scalarZero L

open FourierBiotSavartTransversalityLaws public

biotSavartVelocityIsTransverse :
  ∀ {m v s}
    {Mode : Set m}
    {Vector : Set v}
    {Scalar : Set s}
    {L : FourierVectorLaws Mode Vector Scalar} →
  FourierBiotSavartTransversalityLaws L →
  ∀ mode omega →
  vectorDot L
    (waveVector L mode)
    (biotSavartVelocity L mode omega)
  ≡ scalarZero L
biotSavartVelocityIsTransverse {L = L} T mode omega =
  trans
    (dotScaleRight T
      (waveVector L mode)
      (inverseNormSquared L mode)
      (vectorCross L (waveVector L mode) omega))
    (subst
      (λ dotValue →
        scalarMultiply L (inverseNormSquared L mode) dotValue
        ≡ scalarZero L)
      (sym (waveDotOwnCrossIsZero T mode omega))
      (multiplyZeroRight T (inverseNormSquared L mode)))

------------------------------------------------------------------------
-- Status: exact Fourier transversality is checked.  The remaining official
-- carrier work is Parseval and the cutoff-uniform L2/H1 operator estimates.
------------------------------------------------------------------------

biotSavartTransversalityAssemblyLevel : ProofLevel
biotSavartTransversalityAssemblyLevel = machineChecked
