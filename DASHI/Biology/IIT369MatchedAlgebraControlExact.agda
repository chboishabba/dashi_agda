module DASHI.Biology.IIT369MatchedAlgebraControlExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Separation
import DASHI.Biology.IIT4FiniteExecutableKernelExact as Kernel

------------------------------------------------------------------------
-- SAME CARDINALITY DOES NOT MEAN SAME ALGEBRA, AND SYSTEM-PHI NEED NOT SEE IT.
------------------------------------------------------------------------

sameCarrierChart :
  (pair : Phase.PhaseQuotient9) →
  Separation.nonaryToPhasePair (Separation.phasePairToNonary pair) ≡ pair
sameCarrierChart = Separation.phaseNonaryRoundTrip

sameCardinalityStillNotGroupIsomorphic :
  Separation.Q9NonaryGroupIsomorphism → ⊥
sameCardinalityStillNotGroupIsomorphic =
  Separation.q9NonaryGroupIsomorphismImpossible

naturalCarrierChartDoesNotPreserveAddition :
  Separation.phasePairToNonary
    (Separation.q9Add
      (Base.tri-low , Base.tri-mid)
      (Base.tri-low , Base.tri-high))
  ≡
  Base.nonaryXor
    (Separation.phasePairToNonary (Base.tri-low , Base.tri-mid))
    (Separation.phasePairToNonary (Base.tri-low , Base.tri-high))
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
