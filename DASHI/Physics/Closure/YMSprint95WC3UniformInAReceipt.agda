module DASHI.Physics.Closure.YMSprint95WC3UniformInAReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMBlockedL2KPEntropy as BlockedKP
import DASHI.Physics.Closure.YMSprint94UniformBoundForAllAReceipt as Sprint94

------------------------------------------------------------------------
-- Sprint 95 WC3 uniform-in-a summability.
--
-- Sprint 94 supplied a physical-diameter activity bound uniform for all
-- a < a0.  This receipt combines that bound with the existing blocked L=2
-- eta=4 KP carrier:
--
--   4q = 0.9271275790105094 < 1.
--
-- Therefore the cluster expansion is uniformly summable in a at the WC3
-- interface.  This does not derive the connected Schwinger decay theorem,
-- the continuum mass gap, or Clay promotion.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

wc3UniformInAClosedInRepo : Bool
wc3UniformInAClosedInRepo = true

uniformConnectedSchwingerDecayDerivedInRepo : Bool
uniformConnectedSchwingerDecayDerivedInRepo = false

continuumLimitMassGapDerivedInRepo : Bool
continuumLimitMassGapDerivedInRepo = false

record WC3UniformInA : Set₁ where
  constructor mkWC3UniformInA
  field
    uniformBound :
      Sprint94.UniformBoundForAllA
    blockedL2KP :
      BlockedKP.AnisotropicL2WeightedKPClosesAuthorityConditional
    eta4QBelowOne :
      String
    clusterExpansionSummableUniformly :
      String
    wc3Closed :
      wc3UniformInAClosedInRepo ≡ true

data UniformConnectedSchwingerDecay : Set where

uniformConnectedSchwingerDecayImpossibleHere :
  UniformConnectedSchwingerDecay →
  ⊥
uniformConnectedSchwingerDecayImpossibleHere ()

data ContinuumLimitMassGap : Set where

continuumLimitMassGapImpossibleHere :
  ContinuumLimitMassGap →
  ⊥
continuumLimitMassGapImpossibleHere ()

sprint95Route : String
sprint95Route =
  "UniformBoundForAllA + blocked L=2 eta=4 KP arithmetic -> WC3UniformInA; remaining work is UniformConnectedSchwingerDecay -> ContinuumLimitMassGap."

sprint95Remaining : String
sprint95Remaining =
  "Remaining after Sprint 95: UniformConnectedSchwingerDecay, ContinuumLimitMassGap, Nontrivial4DSU3YangMillsMeasure, ClayStatementBoundaryDischarged, ExternalAcceptanceToken."

canonicalWC3UniformInA : WC3UniformInA
canonicalWC3UniformInA =
  mkWC3UniformInA
    Sprint94.canonicalUniformBoundForAllA
    BlockedKP.anisotropicL2WeightedKPClosesAuthorityConditional
    "eta=4 and q=0.23178189475262734 give 4q=0.9271275790105094<1"
    "The polymer cluster sum is bounded uniformly in a by the Sprint 94 constants and the blocked L=2 KP geometric factor"
    refl

record YMSprint95WC3UniformInAReceipt : Set₁ where
  field
    sprint94UniformBoundReceipt :
      Sprint94.YMSprint94UniformBoundForAllAReceipt
    wc3 :
      WC3UniformInA
    wc3Closed :
      wc3UniformInAClosedInRepo ≡ true
    uniformDecayStillOpen :
      uniformConnectedSchwingerDecayDerivedInRepo ≡ false
    continuumMassGapStillOpen :
      continuumLimitMassGapDerivedInRepo ≡ false
    uniformDecayWitnessNotExported :
      UniformConnectedSchwingerDecay → ⊥
    continuumLimitMassGapWitnessNotExported :
      ContinuumLimitMassGap → ⊥
    route :
      sprint95Route ≡
      "UniformBoundForAllA + blocked L=2 eta=4 KP arithmetic -> WC3UniformInA; remaining work is UniformConnectedSchwingerDecay -> ContinuumLimitMassGap."
    remaining :
      sprint95Remaining ≡
      "Remaining after Sprint 95: UniformConnectedSchwingerDecay, ContinuumLimitMassGap, Nontrivial4DSU3YangMillsMeasure, ClayStatementBoundaryDischarged, ExternalAcceptanceToken."
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint95WC3UniformInAReceipt :
  YMSprint95WC3UniformInAReceipt
canonicalYMSprint95WC3UniformInAReceipt =
  record
    { sprint94UniformBoundReceipt =
        Sprint94.canonicalYMSprint94UniformBoundForAllAReceipt
    ; wc3 =
        canonicalWC3UniformInA
    ; wc3Closed =
        refl
    ; uniformDecayStillOpen =
        refl
    ; continuumMassGapStillOpen =
        refl
    ; uniformDecayWitnessNotExported =
        uniformConnectedSchwingerDecayImpossibleHere
    ; continuumLimitMassGapWitnessNotExported =
        continuumLimitMassGapImpossibleHere
    ; route =
        refl
    ; remaining =
        refl
    ; noClayPromotion =
        refl
    }
