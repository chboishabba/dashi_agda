module DASHI.Physics.Closure.NSTriadKNCriticalSlotDifferenceEnergyRound158Exact where

------------------------------------------------------------------------
-- ROUND158 / ENERGY IDENTITY FOR THE DAMPED NORMALIZED-CURL SLOT DIFFERENCE
--
-- R157 gives the exact scalar complex equation
--
--   dZ = sigma Z + F,
--
-- for Z = B_k-B_q, with sigma the sum of the three real viscous decay
-- coefficients and F the literal difference of two Round94 network forcings.
--
-- This file differentiates the algebraic square |Z|^2 = conj(Z) Z at tangent
-- level.  For conjugation-fixed sigma,
--
--   d |Z|^2
--     = (sigma+sigma) |Z|^2
--       + conj(F) Z + conj(Z) F.
--
-- Thus viscosity damps the exact quotient-visible slot defect, while every
-- possible increase is owned by one explicit signed forcing-work term.  This
-- is the dynamic analogue of the YM covariance telescope: the residual has
-- its own energy ledger rather than being paid cellwise by absolute values.
--
-- No positivity/order/integration theorem is asserted on the weak RealField.
-- The remaining A producer is to sum/integrate these forcing-work terms on the
-- literal Galerkin network and charge their quadratic variation uniformly in
-- cutoff.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157

slotDefectEnergy :
  ∀ {r} {F : C3.RealField r} → C3.Complex F → C3.Complex F
slotDefectEnergy z =
  C3.complexMultiply (C3.complexConjugate z) z

slotDefectEnergyTangent :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F
slotDefectEnergyTangent z dz =
  C3.complexAdd
    (C3.complexMultiply (C3.complexConjugate dz) z)
    (C3.complexMultiply (C3.complexConjugate z) dz)

forcingWork :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F
forcingWork z forcing =
  C3.complexAdd
    (C3.complexMultiply (C3.complexConjugate forcing) z)
    (C3.complexMultiply (C3.complexConjugate z) forcing)

record ConjugationFixedScalar {r} {F : C3.RealField r}
    (scalar : C3.Complex F) : Set r where
  constructor conjugation-fixed-scalar
  field
    conjugationFixed : C3.complexConjugate scalar ≡ scalar

open ConjugationFixedScalar public

dampedForcedEnergyIdentity :
  ∀ {r} {F : C3.RealField r}
    (decay z forcing : C3.Complex F) →
  ConjugationFixedScalar decay →
  slotDefectEnergyTangent z
    (C3.complexAdd (C3.complexMultiply decay z) forcing)
  ≡
  C3.complexAdd
    (C3.complexMultiply
      (C3.complexAdd decay decay)
      (slotDefectEnergy z))
    (forcingWork z forcing)
dampedForcedEnergyIdentity {F = F} decay z forcing realDecay =
  trans expanded regrouped
  where
  expanded :
    slotDefectEnergyTangent z
      (C3.complexAdd (C3.complexMultiply decay z) forcing)
    ≡
    C3.complexAdd
      (C3.complexMultiply
        (C3.complexAdd
          (C3.complexMultiply decay (C3.complexConjugate z))
          (C3.complexConjugate forcing))
        z)
      (C3.complexMultiply
        (C3.complexConjugate z)
        (C3.complexAdd (C3.complexMultiply decay z) forcing))
  expanded =
    cong
      (λ conjugated →
        C3.complexAdd
          (C3.complexMultiply conjugated z)
          (C3.complexMultiply
            (C3.complexConjugate z)
            (C3.complexAdd (C3.complexMultiply decay z) forcing)))
      (trans
        (Hermitian.complexConjugateAdd
          (C3.complexMultiply decay z) forcing)
        (cong
          (λ head → C3.complexAdd head (C3.complexConjugate forcing))
          (trans
            (Hermitian.complexConjugateMultiply decay z)
            (cong
              (λ head → C3.complexMultiply head (C3.complexConjugate z))
              (conjugationFixed realDecay)))))

  regrouped :
    C3.complexAdd
      (C3.complexMultiply
        (C3.complexAdd
          (C3.complexMultiply decay (C3.complexConjugate z))
          (C3.complexConjugate forcing))
        z)
      (C3.complexMultiply
        (C3.complexConjugate z)
        (C3.complexAdd (C3.complexMultiply decay z) forcing))
    ≡
    C3.complexAdd
      (C3.complexMultiply
        (C3.complexAdd decay decay)
        (slotDefectEnergy z))
      (forcingWork z forcing)
  regrouped =
    R.solve 4
      (λ decay zbar z fbar →
        ((((decay R.⊗ zbar) R.⊕ fbar) R.⊗ z)
          R.⊕ (zbar R.⊗ ((decay R.⊗ z) R.⊕ R.Κ forcing)))
        R.⊜
        (((decay R.⊕ decay) R.⊗ (zbar R.⊗ z))
          R.⊕ ((fbar R.⊗ z) R.⊕ (zbar R.⊗ R.Κ forcing))))
      refl decay (C3.complexConjugate z) z (C3.complexConjugate forcing)
    where module R = Ring.Solver F

-- The exact Round94 total decay is conjugation-fixed because each modal decay
-- scalar is a real embedding and conjugation distributes over addition.
totalNegativeDecayIsConjugationFixed :
  ∀ {r} {F : C3.RealField r}
    (rhoK rhoP rhoQ : C3.Carrier F) →
  ConjugationFixedScalar (R94.totalNegativeDecay rhoK rhoP rhoQ)
totalNegativeDecayIsConjugationFixed {F = F} rhoK rhoP rhoQ =
  conjugation-fixed-scalar
    (trans
      (Hermitian.complexConjugateAdd
        (C3.complexAdd (R94.negativeReal rhoK) (R94.negativeReal rhoP))
        (R94.negativeReal rhoQ))
      (trans
        (cong
          (λ tail → C3.complexAdd tail
            (C3.complexConjugate (R94.negativeReal rhoQ)))
          (Hermitian.complexConjugateAdd
            (R94.negativeReal rhoK) (R94.negativeReal rhoP)))
        (cong2close
          (R94.negativeRealConjugate rhoK)
          (R94.negativeRealConjugate rhoP)
          (R94.negativeRealConjugate rhoQ))))
  where
  cong2close :
    C3.complexConjugate (R94.negativeReal rhoK) ≡ R94.negativeReal rhoK →
    C3.complexConjugate (R94.negativeReal rhoP) ≡ R94.negativeReal rhoP →
    C3.complexConjugate (R94.negativeReal rhoQ) ≡ R94.negativeReal rhoQ →
    C3.complexAdd
      (C3.complexAdd
        (C3.complexConjugate (R94.negativeReal rhoK))
        (C3.complexConjugate (R94.negativeReal rhoP)))
      (C3.complexConjugate (R94.negativeReal rhoQ))
    ≡ R94.totalNegativeDecay rhoK rhoP rhoQ
  cong2close refl refl refl = refl

round158SlotDifferenceEnergyIdentityClosed : Bool
round158SlotDifferenceEnergyIdentityClosed = true

round158ViscousDecayAndNetworkForcingOwnershipSeparated : Bool
round158ViscousDecayAndNetworkForcingOwnershipSeparated = true

round158ForcingWorkQuadraticVariationPaymentClosed : Bool
round158ForcingWorkQuadraticVariationPaymentClosed = false

round158PackageAClosed : Bool
round158PackageAClosed = false

round158SlotDifferenceEnergyIdentityClosedIsTrue :
  round158SlotDifferenceEnergyIdentityClosed ≡ true
round158SlotDifferenceEnergyIdentityClosedIsTrue = refl

round158PackageAClosedIsFalse : round158PackageAClosed ≡ false
round158PackageAClosedIsFalse = refl
