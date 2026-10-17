module DASHI.Physics.CondensedMatter.MATBGEntropyCombinatorics2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-BOUNDED ENTROPY COMBINATORICS
--
-- Zhang et al. (Nature Communications 17, 9785, 2026) compare the measured
-- entropy with combinatorial local-moment targets. Around 20 K:
--   S = k_B ln C(8, nu + 4)
-- and around 10 K on the electron side:
--   S = k_B ln C(4, |nu|).
-- This owner proves the finite microstate counts for nu = 0,1,2,3. It does
-- not rederive k_B, logarithms, chemical-potential data, or experimental fits.
------------------------------------------------------------------------

choose : Nat → Nat → Nat
choose n zero = 1
choose zero (suc k) = 0
choose (suc n) (suc k) = choose n k + choose n (suc k)

data IntegerFilling0to3 : Set where
  filling0 filling1 filling2 filling3 : IntegerFilling0to3

fillingIndex : IntegerFilling0to3 → Nat
fillingIndex filling0 = 0
fillingIndex filling1 = 1
fillingIndex filling2 = 2
fillingIndex filling3 = 3

highTemperatureOccupation : IntegerFilling0to3 → Nat
highTemperatureOccupation filling0 = 4
highTemperatureOccupation filling1 = 5
highTemperatureOccupation filling2 = 6
highTemperatureOccupation filling3 = 7

highTemperatureMicrostates : IntegerFilling0to3 → Nat
highTemperatureMicrostates f = choose 8 (highTemperatureOccupation f)

lowTemperatureMicrostates : IntegerFilling0to3 → Nat
lowTemperatureMicrostates f = choose 4 (fillingIndex f)

record EntropyExtractionSourceContract : Set where
  constructor entropy-extraction-source-contract
  field
    inverseCompressibilityMeasured : Bool
    chemicalPotentialObtainedByDensityIntegration : Bool
    maxwellRelationUsed : Bool
    entropyReferenceAtFullFillingAssumedZero : Bool
    entropyIntegratedFromMinusDmuDT : Bool
    sourceReference : String

open EntropyExtractionSourceContract public

zhang2026EntropyExtractionContract : EntropyExtractionSourceContract
zhang2026EntropyExtractionContract =
  entropy-extraction-source-contract
    true true true true true
    "Zhang et al. Nature Communications 17, 9785 (2026): dmu/dn -> mu(n,T); Maxwell relation dS/dn=-dmu/dT; S(full filling)=0 reference; entropy obtained by density integration"

record AtomicLimitTHFSourceContract : Set where
  constructor atomic-limit-thf-source-contract
  field
    highTemperatureDegeneracy : Nat
    lowTemperatureDegeneracy : Nat
    hubbardU1mV : Nat
    heterostrainTenThousandths : Nat
    atomicLimitUsed : Bool
    strainIncluded : Bool
    sitesDecoupledInAtomicLimit : Bool
    fAndCDecoupledInAtomicLimit : Bool
    lowTemperatureGroundStateValidityClaimed : Bool
    sourceReference : String

open AtomicLimitTHFSourceContract public

zhang2026AtomicLimitContract : AtomicLimitTHFSourceContract
zhang2026AtomicLimitContract =
  atomic-limit-thf-source-contract
    8 4 23 10
    true true true true false
    "Zhang et al. 2026 Fig. 2f / SI Appendix I: atomic-limit THF entropy with U1=23 mV and compressive heterostrain epsilon=0.001; source notes the decoupled atomic limit is not valid for real ground states below about 6 K"

record EntropyCombinatoricsBoundary : Set where
  constructor entropy-combinatorics-boundary
  field
    sourceFormulaRecorded : Bool
    exactHighTemperatureCountsPaid : Bool
    exactLowTemperatureCountsPaid : Bool
    maxwellExtractionProcedureSourcePaid : Bool
    atomicLimitParameterPairSourcePaid : Bool
    experimentalEntropyDataNumericallyReplayed : Bool
    logarithmMetrologyReproduced : Bool
    sameSampleQTMEntropyPaid : Bool
    combinatoricsAloneProvesMicroscopicMechanism : Bool

open EntropyCombinatoricsBoundary public

canonicalEntropyCombinatoricsBoundary : EntropyCombinatoricsBoundary
canonicalEntropyCombinatoricsBoundary =
  entropy-combinatorics-boundary
    true true true true true false false false false

record EntropyAttributionBoundary : Set where
  constructor entropy-attribution-boundary
  field
    zhangEtAlOwnExperimentalAndModelComparisonFacts : Bool
    dashiOwnsFiniteChooseEvaluation : Bool
    finiteChooseEvaluationDoesNotOwnExperimentalEntropy : Bool

open EntropyAttributionBoundary public

canonicalEntropyAttributionBoundary : EntropyAttributionBoundary
canonicalEntropyAttributionBoundary =
  entropy-attribution-boundary true true true
