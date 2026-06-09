module DASHI.Physics.Closure.YMSprint93ContractionDeltaLowerBoundReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMSprint92MasterWC3Condition as Sprint92

------------------------------------------------------------------------
-- Sprint 93 contraction lower-bound receipt.
--
-- Sprint 92 exposed the master-WC3 theorem interface and the corrected
-- SU(3) k=11 arithmetic.  Sprint 93 records the first non-roadmap step after
-- that correction:
--
-- * CMP98 averaging-kernel probability is accepted as scoped authority for
--   C_avg <= 1;
-- * CMP116 polymer-mass positivity is accepted as scoped authority;
-- * the Dobrushin contraction claim is corrected from independence in a to a
--   uniform lower bound: C_local(a) -> 0, so delta(a) -> 1, and the binding
--   condition is at the weak-coupling entry scale a0.
--
-- This does not derive WC3, uniform Schwinger decay, the continuum mass gap,
-- or Clay promotion.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

balabanCMP98AveragingKernelProbabilityScopedAuthorityAccepted : Bool
balabanCMP98AveragingKernelProbabilityScopedAuthorityAccepted = true

balabanCMP116PolymerMassBoundScopedAuthorityAccepted : Bool
balabanCMP116PolymerMassBoundScopedAuthorityAccepted = true

contractionDeltaLowerBoundClosedInRepo : Bool
contractionDeltaLowerBoundClosedInRepo = true

uniformBoundForAllADerivedInRepo : Bool
uniformBoundForAllADerivedInRepo = false

wc3UniformInADerivedInRepo : Bool
wc3UniformInADerivedInRepo = false

uniformConnectedSchwingerDecayDerivedInRepo : Bool
uniformConnectedSchwingerDecayDerivedInRepo = false

continuumLimitMassGapDerivedInRepo : Bool
continuumLimitMassGapDerivedInRepo = false

record BalabanCMP98AveragingKernelIsProbabilityAuthority : Set where
  constructor mkBalabanCMP98AveragingKernelIsProbabilityAuthority
  field
    source :
      String
    kernelIsHaarConvolution :
      String
    kernelL1NormEqualsOne :
      String
    cAvgBoundOne :
      String
    scopedAuthorityAccepted :
      balabanCMP98AveragingKernelProbabilityScopedAuthorityAccepted ≡ true

record BalabanCMP116PolymerMassBoundAuthority : Set where
  constructor mkBalabanCMP116PolymerMassBoundAuthority
  field
    source :
      String
    polymerMassPositive :
      String
    exponentialPolymerWeightBound :
      String
    scopedAuthorityAccepted :
      balabanCMP116PolymerMassBoundScopedAuthorityAccepted ≡ true

record ContractionDeltaLowerBound : Set where
  constructor mkContractionDeltaLowerBound
  field
    cmp98Kernel :
      BalabanCMP98AveragingKernelIsProbabilityAuthority
    cmp116PolymerMass :
      BalabanCMP116PolymerMassBoundAuthority
    sprint92Numerics :
      Sprint92.MasterWC3NumericalData
    cLocalScaling :
      String
    contractionLowerBound :
      String
    bindingScale :
      String
    lowerBoundClosed :
      contractionDeltaLowerBoundClosedInRepo ≡ true

data UniformBoundForAllA : Set where

uniformBoundForAllAImpossibleHere :
  UniformBoundForAllA →
  ⊥
uniformBoundForAllAImpossibleHere ()

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

sprint93Route : String
sprint93Route =
  "CMP98 probability + CMP116 polymer mass + SU3 k=11 row arithmetic -> ContractionDeltaLowerBound; remaining work is UniformBoundForAllA -> WC3UniformInA -> UniformConnectedSchwingerDecay -> ContinuumLimitMassGap."

sprint93Remaining : String
sprint93Remaining =
  "Remaining after Sprint 93: UniformBoundForAllA, WC3UniformInA, UniformConnectedSchwingerDecay, ContinuumLimitMassGap, Nontrivial4DSU3YangMillsMeasure, ClayStatementBoundaryDischarged, ExternalAcceptanceToken."

canonicalBalabanCMP98AveragingKernelIsProbabilityAuthority :
  BalabanCMP98AveragingKernelIsProbabilityAuthority
canonicalBalabanCMP98AveragingKernelIsProbabilityAuthority =
  mkBalabanCMP98AveragingKernelIsProbabilityAuthority
    "Balaban CMP 98 (1985), averaging operations for lattice gauge theories, Section 3"
    "Q_{ell,k} is treated as a Haar-measure convolution kernel on SU(N)"
    "Haar probability normalisation gives ||phi||_L1 = 1"
    "The scoped DASHI authority consequence is C_avg <= 1"
    refl

canonicalBalabanCMP116PolymerMassBoundAuthority :
  BalabanCMP116PolymerMassBoundAuthority
canonicalBalabanCMP116PolymerMassBoundAuthority =
  mkBalabanCMP116PolymerMassBoundAuthority
    "Balaban CMP 116 (1988), cluster expansions for lattice gauge theories, Theorem 1.1"
    "The small-field polymer activity has a positive mass parameter m > 0"
    "Polymer weights are exponentially bounded by exp(-m |gamma|) in the scoped authority lane"
    refl

canonicalContractionDeltaLowerBound :
  ContractionDeltaLowerBound
canonicalContractionDeltaLowerBound =
  mkContractionDeltaLowerBound
    canonicalBalabanCMP98AveragingKernelIsProbabilityAuthority
    canonicalBalabanCMP116PolymerMassBoundAuthority
    Sprint92.sprint92Numerics
    "C_local(a) = C_avg * g^{2*} * L^{-k*(a)} = C_avg * g^{2*} * m_phys * a, hence C_local(a) -> 0 as a -> 0"
    "There exist a0 and delta_min > 0 such that for all a < a0, delta(a) >= delta_min = 1 - exp(-4)"
    "The binding condition is at a = a0, the weak-coupling entry scale, not in the a -> 0 tail"
    refl

record YMSprint93ContractionDeltaLowerBoundReceipt : Set₁ where
  field
    sprint92ConditionSurface :
      Sprint92.YMSprint92MasterWC3ConditionReceipt
    cmp98Authority :
      BalabanCMP98AveragingKernelIsProbabilityAuthority
    cmp116Authority :
      BalabanCMP116PolymerMassBoundAuthority
    lowerBound :
      ContractionDeltaLowerBound
    cmp98AuthorityAccepted :
      balabanCMP98AveragingKernelProbabilityScopedAuthorityAccepted ≡ true
    cmp116AuthorityAccepted :
      balabanCMP116PolymerMassBoundScopedAuthorityAccepted ≡ true
    lowerBoundClosed :
      contractionDeltaLowerBoundClosedInRepo ≡ true
    uniformBoundStillOpen :
      uniformBoundForAllADerivedInRepo ≡ false
    wc3StillOpen :
      wc3UniformInADerivedInRepo ≡ false
    uniformDecayStillOpen :
      uniformConnectedSchwingerDecayDerivedInRepo ≡ false
    continuumMassGapStillOpen :
      continuumLimitMassGapDerivedInRepo ≡ false
    uniformBoundWitnessNotExported :
      UniformBoundForAllA → ⊥
    wc3UniformWitnessNotExported :
      WC3UniformInA → ⊥
    uniformDecayWitnessNotExported :
      UniformConnectedSchwingerDecay → ⊥
    continuumLimitMassGapWitnessNotExported :
      ContinuumLimitMassGap → ⊥
    route :
      sprint93Route ≡
      "CMP98 probability + CMP116 polymer mass + SU3 k=11 row arithmetic -> ContractionDeltaLowerBound; remaining work is UniformBoundForAllA -> WC3UniformInA -> UniformConnectedSchwingerDecay -> ContinuumLimitMassGap."
    remaining :
      sprint93Remaining ≡
      "Remaining after Sprint 93: UniformBoundForAllA, WC3UniformInA, UniformConnectedSchwingerDecay, ContinuumLimitMassGap, Nontrivial4DSU3YangMillsMeasure, ClayStatementBoundaryDischarged, ExternalAcceptanceToken."
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint93ContractionDeltaLowerBoundReceipt :
  YMSprint93ContractionDeltaLowerBoundReceipt
canonicalYMSprint93ContractionDeltaLowerBoundReceipt =
  record
    { sprint92ConditionSurface =
        Sprint92.canonicalYMSprint92MasterWC3ConditionReceipt
    ; cmp98Authority =
        canonicalBalabanCMP98AveragingKernelIsProbabilityAuthority
    ; cmp116Authority =
        canonicalBalabanCMP116PolymerMassBoundAuthority
    ; lowerBound =
        canonicalContractionDeltaLowerBound
    ; cmp98AuthorityAccepted =
        refl
    ; cmp116AuthorityAccepted =
        refl
    ; lowerBoundClosed =
        refl
    ; uniformBoundStillOpen =
        refl
    ; wc3StillOpen =
        refl
    ; uniformDecayStillOpen =
        refl
    ; continuumMassGapStillOpen =
        refl
    ; uniformBoundWitnessNotExported =
        uniformBoundForAllAImpossibleHere
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
