module DASHI.Physics.Closure.NSTriadKNCannoneTrilinearAntisymmetryAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Marco Cannone.
-- Title: "Harmonic Analysis Tools for Solving the Incompressible
-- Navier-Stokes Equations".
-- Venue/year: Handbook of Mathematical Fluid Dynamics, Volume 3, Elsevier,
-- 2005, Chapter 3, pages 161--244.
-- DOI: 10.1016/S1874-5792(05)80006-0.
-- Uses: the classical divergence-free trilinear integration-by-parts identity
-- b(u,v,w) = -b(u,w,v) when div u = 0.
-- Relationship: the repository proves the corresponding exact Fourier
-- derivative-factor identity from resonance and transversality.  The full
-- reality-mate Hermitian pairing is checked by an exact rational verifier.
-- Crucially, the permutation keeps the transport leg p fixed and sends
-- (advected q, tested k) to (advected -k, tested -q); it does not turn the
-- first-adjoint low-p ordering into the favourable second-adjoint low-q
-- ordering.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3RelocationInstantiation as Relocation

complexAddInverseRight :
  ∀ {r} {F : C3.RealField r}
    (z : C3.Complex F) →
  C3.complexAdd z (C3.complexNegate z) ≡ C3.complexZero F
complexAddInverseRight {F = F} (C3.complex real imaginary)
  rewrite Algebra.realAddInverseRight F real
        | Algebra.realAddInverseRight F imaginary = refl

transportDerivativeFactor :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  C3.Complex3 F → Z3.FourierMode → C3.Complex F
transportDerivativeFactor E transport mode =
  C3.bilinearDot3 transport (C3.modeVector E mode)

conjugateTestDerivativeFactor :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  C3.Complex3 F → Z3.FourierMode → C3.Complex F
conjugateTestDerivativeFactor E transport output =
  C3.complexNegate
    (C3.bilinearDot3 transport (C3.modeVector E output))

------------------------------------------------------------------------
-- Exact Fourier form of integration by parts at the derivative-factor level:
--
--   (u_p dot q) + (u_p dot (-k)) = 0,
--
-- represented with the derivative on the conjugated output test as
-- -(u_p dot k).  This is precisely the resonance/transversality relocation
-- already proved on the concrete C3 carrier, followed by additive inverse.
------------------------------------------------------------------------

discreteTransportPlusConjugateTestDerivativeZero :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode}
    {uP : C3.Complex3 F} →
  Z3.Resonance p q k →
  Helical.Transverse E p uP →
  C3.complexAdd
    (transportDerivativeFactor E uP q)
    (conjugateTestDerivativeFactor E uP k)
  ≡ C3.complexZero F
discreteTransportPlusConjugateTestDerivativeZero E {p} {q} {k} {uP}
  resonance transverse =
  trans
    (cong
      (λ factor →
        C3.complexAdd factor
          (conjugateTestDerivativeFactor E uP k))
      (Relocation.complex3OutputDerivativeRelocation E resonance transverse))
    (complexAddInverseRight
      (C3.bilinearDot3 uP (C3.modeVector E k)))

data FrozenOrderingRole : Set where
  lowTransportOutput
  highAdvectedInput
  highOriginalOutput
  highRealityMateAdvected
  highRealityMateOutput
  lowSecondAdjointFrozenDerivative : FrozenOrderingRole

data AntisymmetryRouteDecision : Set where
  exactClassicalIdentityAvailable
  transfersFirstEstimateToFavourableSecondEstimate
  sameFrozenTransportOrderingNeedsOwnEstimate : AntisymmetryRouteDecision

classicalIdentityDecision : AntisymmetryRouteDecision
classicalIdentityDecision = exactClassicalIdentityAvailable

firstAdjointBypassDecision : AntisymmetryRouteDecision
firstAdjointBypassDecision = sameFrozenTransportOrderingNeedsOwnEstimate

record FourierAntisymmetryPermutationReceipt : Set where
  constructor permutation-receipt
  field
    transportLegBefore : FrozenOrderingRole
    advectedLegBefore : FrozenOrderingRole
    testedOutputBefore : FrozenOrderingRole
    advectedRealityMateAfter : FrozenOrderingRole
    testedRealityMateAfter : FrozenOrderingRole
    favourableSecondFrozenDerivative : FrozenOrderingRole

    transportRemainsLowP : transportLegBefore ≡ lowTransportOutput
    qIsHighBefore : advectedLegBefore ≡ highAdvectedInput
    kIsHighBefore : testedOutputBefore ≡ highOriginalOutput
    minusKRemainsHighAfter :
      advectedRealityMateAfter ≡ highRealityMateAdvected
    minusQRemainsHighAfter : testedRealityMateAfter ≡ highRealityMateOutput
    favourableSecondOrderingWouldRequireLowQ :
      favourableSecondFrozenDerivative ≡ lowSecondAdjointFrozenDerivative

open FourierAntisymmetryPermutationReceipt public

fourierAntisymmetryPermutationReceipt : FourierAntisymmetryPermutationReceipt
fourierAntisymmetryPermutationReceipt =
  permutation-receipt
    lowTransportOutput
    highAdvectedInput
    highOriginalOutput
    highRealityMateAdvected
    highRealityMateOutput
    lowSecondAdjointFrozenDerivative
    refl refl refl refl refl refl

record ClassicalAntisymmetryScopeReceipt : Set where
  constructor scope-receipt
  field
    derivativeFactorIdentityClosed : Bool
    fullRealityMatePairingExactAuditPassed : Bool
    fullHermitianPairingAgdaTheoremClosed : Bool
    transportLegChangesUnderIntegrationByParts : Bool
    derivativeBecomesLowUnderIntegrationByParts : Bool
    firstAdjointEstimateDerivedFromSecondAdjointEstimate : Bool
    directSobolevTailStillNeeded : Bool

open ClassicalAntisymmetryScopeReceipt public

classicalAntisymmetryScopeReceipt : ClassicalAntisymmetryScopeReceipt
classicalAntisymmetryScopeReceipt =
  scope-receipt true true false false false false true

record ClassicalAntisymmetryProofReceipt : Set where
  constructor proof-receipt
  field
    derivativeIdentityAvailable :
      derivativeFactorIdentityClosed classicalAntisymmetryScopeReceipt ≡ true
    finitePairingAuditAvailable :
      fullRealityMatePairingExactAuditPassed classicalAntisymmetryScopeReceipt
      ≡ true
    fullAgdaPairingStillOpen :
      fullHermitianPairingAgdaTheoremClosed classicalAntisymmetryScopeReceipt
      ≡ false
    frozenTransportDoesNotChange :
      transportLegChangesUnderIntegrationByParts classicalAntisymmetryScopeReceipt
      ≡ false
    derivativeDoesNotBecomeLow :
      derivativeBecomesLowUnderIntegrationByParts classicalAntisymmetryScopeReceipt
      ≡ false
    noFirstFromSecondBypass :
      firstAdjointEstimateDerivedFromSecondAdjointEstimate
        classicalAntisymmetryScopeReceipt
      ≡ false
    tailRouteRetained :
      directSobolevTailStillNeeded classicalAntisymmetryScopeReceipt ≡ true
    routeDecisionIsSameFrozenOrdering :
      firstAdjointBypassDecision ≡ sameFrozenTransportOrderingNeedsOwnEstimate

open ClassicalAntisymmetryProofReceipt public

classicalAntisymmetryProofReceipt : ClassicalAntisymmetryProofReceipt
classicalAntisymmetryProofReceipt =
  proof-receipt refl refl refl refl refl refl refl refl

classicalAntisymmetryAuditRepresented : Bool
classicalAntisymmetryAuditRepresented = true

classicalAntisymmetryAuditRepresentedIsTrue :
  classicalAntisymmetryAuditRepresented ≡ true
classicalAntisymmetryAuditRepresentedIsTrue = refl

classicalAntisymmetryClosesFirstAdjointFunctionalEstimate : Bool
classicalAntisymmetryClosesFirstAdjointFunctionalEstimate = false

classicalAntisymmetryClosesFirstAdjointFunctionalEstimateIsFalse :
  classicalAntisymmetryClosesFirstAdjointFunctionalEstimate ≡ false
classicalAntisymmetryClosesFirstAdjointFunctionalEstimateIsFalse = refl
