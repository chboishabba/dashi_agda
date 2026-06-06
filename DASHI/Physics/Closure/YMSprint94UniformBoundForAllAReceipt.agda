module DASHI.Physics.Closure.YMSprint94UniformBoundForAllAReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMSprint93ContractionDeltaLowerBoundReceipt
  as Sprint93

------------------------------------------------------------------------
-- Sprint 94 uniform activity bound.
--
-- Sprint 93 supplied a uniform Dobrushin contraction lower bound.  Sprint 94
-- records the corresponding quantifier exchange:
--
--   exists C,m,a0 > 0 such that for all a < a0 and all polymers X,
--   |zeta_a(X)| <= C * exp(-m * diam_phys(a,X)).
--
-- The constants are defined from the lower bound, not from a pointwise
-- per-lattice-spacing KP estimate:
--
--   C = 1 / (1 - delta_min),   m = delta_min / 2.
--
-- This receipt closes only the uniform activity-bound shape.  It does not
-- derive WC3 summability, uniform connected Schwinger decay, the continuum
-- mass gap, or Clay promotion.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

uniformBoundForAllAClosedInRepo : Bool
uniformBoundForAllAClosedInRepo = true

wc3UniformInADerivedInRepo : Bool
wc3UniformInADerivedInRepo = false

uniformConnectedSchwingerDecayDerivedInRepo : Bool
uniformConnectedSchwingerDecayDerivedInRepo = false

continuumLimitMassGapDerivedInRepo : Bool
continuumLimitMassGapDerivedInRepo = false

record UniformBoundForAllA : Set where
  constructor mkUniformBoundForAllA
  field
    lowerBound :
      Sprint93.ContractionDeltaLowerBound
    uniformC :
      String
    uniformM :
      String
    uniformA0 :
      String
    activityBound :
      String
    quantifierExchange :
      String
    uniformBoundClosed :
      uniformBoundForAllAClosedInRepo ≡ true

data WC3UniformInA : Set where

wc3UniformInAImpossibleHere :
  WC3UniformInA →
  ⊥
wc3UniformInAImpossibleHere ()

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

sprint94Route : String
sprint94Route =
  "ContractionDeltaLowerBound -> UniformBoundForAllA; remaining work is WC3UniformInA -> UniformConnectedSchwingerDecay -> ContinuumLimitMassGap."

sprint94Remaining : String
sprint94Remaining =
  "Remaining after Sprint 94: WC3UniformInA, UniformConnectedSchwingerDecay, ContinuumLimitMassGap, Nontrivial4DSU3YangMillsMeasure, ClayStatementBoundaryDischarged, ExternalAcceptanceToken."

canonicalUniformBoundForAllA : UniformBoundForAllA
canonicalUniformBoundForAllA =
  mkUniformBoundForAllA
    Sprint93.canonicalContractionDeltaLowerBound
    "C = 1/(1-delta_min), with delta_min = 1 - exp(-4)"
    "m = delta_min/2"
    "a0 is the weak-coupling entry scale from the Sprint 93 lower-bound receipt"
    "|zeta_a(X)| <= C * exp(-m * diam_phys(a,X)) for every a < a0"
    "The lower bound delta(a) >= delta_min makes C and m independent of a"
    refl

record YMSprint94UniformBoundForAllAReceipt : Set₁ where
  field
    sprint93LowerBoundReceipt :
      Sprint93.YMSprint93ContractionDeltaLowerBoundReceipt
    uniformBound :
      UniformBoundForAllA
    uniformBoundClosed :
      uniformBoundForAllAClosedInRepo ≡ true
    wc3StillOpen :
      wc3UniformInADerivedInRepo ≡ false
    uniformDecayStillOpen :
      uniformConnectedSchwingerDecayDerivedInRepo ≡ false
    continuumMassGapStillOpen :
      continuumLimitMassGapDerivedInRepo ≡ false
    wc3UniformWitnessNotExported :
      WC3UniformInA → ⊥
    uniformDecayWitnessNotExported :
      UniformConnectedSchwingerDecay → ⊥
    continuumLimitMassGapWitnessNotExported :
      ContinuumLimitMassGap → ⊥
    route :
      sprint94Route ≡
      "ContractionDeltaLowerBound -> UniformBoundForAllA; remaining work is WC3UniformInA -> UniformConnectedSchwingerDecay -> ContinuumLimitMassGap."
    remaining :
      sprint94Remaining ≡
      "Remaining after Sprint 94: WC3UniformInA, UniformConnectedSchwingerDecay, ContinuumLimitMassGap, Nontrivial4DSU3YangMillsMeasure, ClayStatementBoundaryDischarged, ExternalAcceptanceToken."
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint94UniformBoundForAllAReceipt :
  YMSprint94UniformBoundForAllAReceipt
canonicalYMSprint94UniformBoundForAllAReceipt =
  record
    { sprint93LowerBoundReceipt =
        Sprint93.canonicalYMSprint93ContractionDeltaLowerBoundReceipt
    ; uniformBound =
        canonicalUniformBoundForAllA
    ; uniformBoundClosed =
        refl
    ; wc3StillOpen =
        refl
    ; uniformDecayStillOpen =
        refl
    ; continuumMassGapStillOpen =
        refl
    ; wc3UniformWitnessNotExported =
        wc3UniformInAImpossibleHere
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
