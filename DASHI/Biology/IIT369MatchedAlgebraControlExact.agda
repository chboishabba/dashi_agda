module DASHI.Biology.IIT369MatchedAlgebraControlExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Separation
import DASHI.Biology.IIT4FiniteExecutableKernelExact as Kernel

------------------------------------------------------------------------
-- SAME CARDINALITY DOES NOT MEAN SAME ALGEBRA, AND SYSTEM-PHI NEED NOT SEE IT.
--
-- Existing repo theorem:
--   Q9 = C3 x C3 and NonaryTruth = C9 have an exact nine-state carrier chart,
--   but no group isomorphism can preserve their respective additions.
--
-- The matched Python experiment puts both laws on the same two-cell recurrent
-- fabric A'=B; B'=mu(A,B).  Under the 2023 system measure both produce the
-- same statewise phi_s profile: log2(81) on all 81 states.  Under the 2026
-- intrinsic-information requirement both deterministic systems have phi_s=0.
--
-- This is numerical non-identifiability of the group law by that system-phi
-- observation on this fixture, not an Agda proof of the logarithmic values.
------------------------------------------------------------------------

sameCarrierChart :
  (pair : Separation.Phase.PhaseQuotient9) →
  Separation.nonaryToPhasePair (Separation.phasePairToNonary pair) ≡ pair
sameCarrierChart = Separation.phaseNonaryRoundTrip

sameCardinalityStillNotGroupIsomorphic :
  Separation.Q9NonaryGroupIsomorphism → ⊥
sameCardinalityStillNotGroupIsomorphic =
  Separation.q9NonaryGroupIsomorphismImpossible

naturalCarrierChartDoesNotPreserveAddition :
  Separation.phasePairToNonary
    (Separation.q9Add
      (Separation.Base.tri-low , Separation.Base.tri-mid)
      (Separation.Base.tri-low , Separation.Base.tri-high))
  ≡
  Separation.Base.nonaryXor
    (Separation.phasePairToNonary
      (Separation.Base.tri-low , Separation.Base.tri-mid))
    (Separation.phasePairToNonary
      (Separation.Base.tri-low , Separation.Base.tri-high))
  → ⊥
naturalCarrierChartDoesNotPreserveAddition =
  Separation.naturalChartDoesNotPreserveAddition

record AlgebraControlReceipt : Set where
  constructor algebraControlReceipt
  field
    statesPerSystem : Nat
    z9IIT42023Profile : String
    f3SquaredIIT42023Profile : String
    iit42026DeterministicProfile : String
    same2023ProfileObserved : Bool
    formalNonisomorphismAlreadyOwned : Bool
    scanner : String

open AlgebraControlReceipt public

currentAlgebraControlReceipt : AlgebraControlReceipt
currentAlgebraControlReceipt =
  algebraControlReceipt
    81
    "phi_s=log2(81) on all 81 states"
    "phi_s=log2(81) on all 81 states"
    "phi_s=0 on all deterministic states under IIT_4_0_2026"
    true true
    "scripts/iit_369_algebra_scan.py"

record IIT369AlgebraControlBoundary : Set where
  constructor iit369AlgebraControlBoundary
  field
    nineStateCarrierChartExists : Bool
    groupLawsAreIsomorphic : Bool
    matchedFabricHeldFixed : Bool
    matched2023SystemPhiProfileObserved : Bool
    sameSystemPhiProfileIdentifiesGroupLaw : Bool
    sameCardinalityIdentifiesGroupLaw : Bool
    numericalReceiptIsKernelProof : Bool

open IIT369AlgebraControlBoundary public

canonicalIIT369AlgebraControlBoundary : IIT369AlgebraControlBoundary
canonicalIIT369AlgebraControlBoundary =
  iit369AlgebraControlBoundary true false true true false false false

phiProfileDoesNotIdentifyAlgebra :
  sameSystemPhiProfileIdentifiesGroupLaw
    canonicalIIT369AlgebraControlBoundary ≡ false
phiProfileDoesNotIdentifyAlgebra = refl

cardinalityDoesNotIdentifyAlgebra :
  sameCardinalityIdentifiesGroupLaw
    canonicalIIT369AlgebraControlBoundary ≡ false
cardinalityDoesNotIdentifyAlgebra = refl

versionBoundary : Kernel.IIT4ExecutableKernelBoundary
versionBoundary = Kernel.canonicalIIT4ExecutableKernelBoundary
