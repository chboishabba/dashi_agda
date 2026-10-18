module DASHI.Physics.Closure.NSTriadKNCanonicalModeListedCoherenceRound643Exact where

------------------------------------------------------------------------
-- ROUND643 / CANONICAL MODE-LIST MEMBERSHIP -> modeListed COHERENCE
--
-- R640 isolated one small representation receipt:
--
--   mode ∈ Audit.modes system -> Audit.modeListed system mode.
--
-- The abstract Audit.FiniteComplex3GalerkinSystem intentionally keeps the
-- executable mode list and the logical modeListed predicate independent, so
-- that implication cannot be proved for an arbitrary audit system.
--
-- On the actual canonical R34 constructor, however, modeListed is defined
-- *literally* as membership in the same reconstructed-state mode list.  This
-- module records that definitional fact as an explicit reusable theorem.
--
-- No Fourier estimate, Sobolev estimate, or Navier--Stokes inequality is
-- introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as R34

canonicalModeMembershipImpliesModeListed :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : R34.CutoffSameObjectDatum F E state)
    (mode : Z3.FourierMode) →
  mode Cube.∈
    Audit.modes
      (R30.finiteSystem (R34.canonicalPhysicalFiniteSystem datum)) →
  Audit.modeListed
    (R30.finiteSystem (R34.canonicalPhysicalFiniteSystem datum))
    mode
canonicalModeMembershipImpliesModeListed datum mode member = member

canonicalModeListedImpliesModeMembership :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : R34.CutoffSameObjectDatum F E state)
    (mode : Z3.FourierMode) →
  Audit.modeListed
    (R30.finiteSystem (R34.canonicalPhysicalFiniteSystem datum))
    mode →
  mode Cube.∈
    Audit.modes
      (R30.finiteSystem (R34.canonicalPhysicalFiniteSystem datum))
canonicalModeListedImpliesModeMembership datum mode listed = listed

canonicalModeListedIffLiteralMembershipClosed : Bool
canonicalModeListedIffLiteralMembershipClosed = true

canonicalR34PaysR640ModeCoherenceWithoutEstimate : Bool
canonicalR34PaysR640ModeCoherenceWithoutEstimate = true

round643IntroducesNewNSEstimate : Bool
round643IntroducesNewNSEstimate = false

round643ClayPromotion : Bool
round643ClayPromotion = false

canonicalModeListedIffLiteralMembershipClosedIsTrue :
  canonicalModeListedIffLiteralMembershipClosed ≡ true
canonicalModeListedIffLiteralMembershipClosedIsTrue = refl

canonicalR34PaysR640ModeCoherenceWithoutEstimateIsTrue :
  canonicalR34PaysR640ModeCoherenceWithoutEstimate ≡ true
canonicalR34PaysR640ModeCoherenceWithoutEstimateIsTrue = refl

round643IntroducesNewNSEstimateIsFalse :
  round643IntroducesNewNSEstimate ≡ false
round643IntroducesNewNSEstimateIsFalse = refl

round643ClayPromotionIsFalse :
  round643ClayPromotion ≡ false
round643ClayPromotionIsFalse = refl
