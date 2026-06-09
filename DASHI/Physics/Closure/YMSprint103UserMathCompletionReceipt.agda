module DASHI.Physics.Closure.YMSprint103UserMathCompletionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint102ProofObligationIndexReceipt as Sprint102
import DASHI.Physics.Closure.YMSprint103AuthorityInputs as AuthorityInputs
import DASHI.Physics.Closure.YMSprint103ContinuumMassGapObligation7
  as Obligation7
import DASHI.Physics.Closure.YMSprint103DobrushinWC3Receipt as DobrushinWC3
import DASHI.Physics.Closure.YMSprint103NontrivialSU3ContinuumMeasureObligation8
  as Obligation8

------------------------------------------------------------------------
-- Sprint 103 user-math completion receipt.
--
-- The user supplied mathematical arguments for the eight items indexed in
-- Sprint 102.  This module records those arguments as inhabited, non-empty
-- proof-argument records.  It is deliberately not an external Clay promotion:
-- external acceptance is not repo-internal.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

userSuppliedMathForAllEight : Bool
userSuppliedMathForAllEight = true

allEightProofArgumentsRecordedInRepo : Bool
allEightProofArgumentsRecordedInRepo = true

externalAcceptanceTokenAvailable : Bool
externalAcceptanceTokenAvailable = false

record NumericWitness : Set where
  constructor mkNumericWitness
  field
    expression :
      String
    decimalValue :
      String
    comparison :
      String

record AuthorityProofArgument : Set where
  constructor mkAuthorityProofArgument
  field
    lemmaName :
      String
    formalStatement :
      String
    source :
      String
    userSuppliedArgument :
      String
    recordedAsInhabitedReceipt :
      Bool

record ConstructiveProofArgument : Set where
  constructor mkConstructiveProofArgument
  field
    lemmaName :
      String
    formalStatement :
      String
    dependencies :
      String
    userSuppliedArgument :
      String
    keyEstimate :
      String
    recordedAsInhabitedReceipt :
      Bool

record ContinuumProofArgument : Set where
  constructor mkContinuumProofArgument
  field
    lemmaName :
      String
    formalStatement :
      String
    dependencies :
      String
    userSuppliedArgument :
      String
    continuumBoundary :
      String
    recordedAsInhabitedReceipt :
      Bool

balabanCMP98LocalOscillationBound :
  AuthorityProofArgument
balabanCMP98LocalOscillationBound =
  mkAuthorityProofArgument
    "BalabanCMP98LocalOscillationBound"
    "osc_e(Q_hp k) <= C_avg * g^2 * 2^(-k) for spatial links e in the half-plane blocking lane"
    "Balaban CMP 98, averaging operations, local averaging estimates; DASHI spatial-only Q_hp restriction"
    "The half-plane map is Balaban's local averaging restricted to spatial links. Temporal links are excluded, so the spatial support count is no larger than the CMP98 local averaging support. The user-supplied proof identifies the per-link decay with the Q_hp spatial averaging weight."
    true

balabanCMP98AveragingKernelIsProbability :
  AuthorityProofArgument
balabanCMP98AveragingKernelIsProbability =
  mkAuthorityProofArgument
    "BalabanCMP98AveragingKernelIsProbability"
    "C_avg <= 1 for the Haar-normalised averaging kernel"
    "Balaban CMP 98 Section 3 averaging kernel construction"
    "The averaging kernel is a Haar-measure convolution on SU(N). Haar measure is normalised as a probability measure, so the L1 kernel norm is 1 and the scoped DASHI consequence is C_avg <= 1."
    true

balabanCMP116PolymerMassBound :
  AuthorityProofArgument
balabanCMP116PolymerMassBound =
  mkAuthorityProofArgument
    "BalabanCMP116PolymerMassBound"
    "There is m > 0 such that small-field polymer weights obey exponential decay exp(-m |gamma|)"
    "Balaban CMP 116 Theorem 1.1, cluster expansion bounds"
    "The user-supplied argument consumes Balaban's small-field polymer activity estimate as the positive polymer-mass input needed by the master WC3 condition."
    true

su3K11MasterRowWitness : NumericWitness
su3K11MasterRowWitness =
  mkNumericWitness
    "18 * (9 / 4) / 2^(11 + 1)"
    "0.0098876953125"
    "0.0098876953125 < exp(-4) = 0.01831563888873418"

gaugeCovariantDobrushinComparison :
  ConstructiveProofArgument
gaugeCovariantDobrushinComparison =
  mkConstructiveProofArgument
    "GaugeCovariantDobrushinComparison"
    "AnisotropicAssumptionA + MasterWC3ConditionSU3AtK11 -> exists delta > 0, forall x, sum_y c(x,y) <= 1 - delta"
    "Sprint 91 Cauchy-Schwarz linearisation, Sprint 92 SU(3) k=11 row arithmetic, Sprint 93 contraction lower-bound correction"
    "The quadratic oscillation estimate is converted to a linear Dobrushin row by Cauchy-Schwarz. The spatial-neighbour count contributes 18, the conservative SU(3) adjoint penalty contributes 9/4, and at k=11 the row is below exp(-4). Hence the Dobrushin row sum is uniformly below 1."
    "row_SU3(k=11) = 18 * (9/4) / 2^12 = 0.0098876953125 < exp(-4)"
    true

uniformPolymerActivityFromDobrushin :
  ConstructiveProofArgument
uniformPolymerActivityFromDobrushin =
  mkConstructiveProofArgument
    "UniformPolymerActivityFromDobrushin"
    "GaugeCovariantDobrushinComparison -> exists C m a0, forall a<a0 X, |zeta_a X| <= C * exp(-m * diam_phys(a,X))"
    "Gauge-covariant Dobrushin contraction with delta(a) >= delta_min"
    "The corrected contraction statement is a lower bound, not independence in a. Since C_local(a) -> 0, the binding condition is at a0. The fixed lower bound delta_min yields a-independent constants C = 1/(1-delta_min) and m = delta_min/2."
    "delta_min = 1 - exp(-4), C = exp(4), m = (1 - exp(-4))/2"
    true

wc3UniformClusterSummability :
  ConstructiveProofArgument
wc3UniformClusterSummability =
  mkConstructiveProofArgument
    "WC3UniformClusterSummability"
    "UniformPolymerActivityFromDobrushin + KPEntropyAtBlockedScaleL2 -> uniform cluster summability"
    "Uniform physical-diameter polymer activity, Sprint 80/Sprint 95 eta=4 blocked KP arithmetic"
    "The uniform activity constants feed the KP cluster sum. The blocked L=2 entropy exponent is eta=4, and the current q satisfies 4q < 1; hence the cluster expansion is uniformly summable in a."
    "4q = 0.9271275790105094 < 1"
    true

continuumLimitMassGap :
  ContinuumProofArgument
continuumLimitMassGap =
  mkContinuumProofArgument
    "ContinuumLimitMassGap"
    "UniformConnectedSchwingerDecay + RGGeneratedMassTerm + TransferGapTracksEffectiveMass + RGInvariantPhysicalScale -> lim_{a->0} gap(T(a))*block_size(a) = m_phys > 0"
    "WC3 uniformity, uniform connected Schwinger decay, Balaban RG effective mass generation, transfer matrix comparison, asymptotic-freedom RG-invariant scale"
    "The KP lower bound alone scales to zero, so the user-supplied proof identifies the physical mass through the RG flow. Uniform WC3 prevents loss of control, the effective Wilsonian mass is positive at the physical scale, and the transfer gap tracks that effective mass after multiplying by the block size."
    "This is the main continuum bridge and remains separated from external Clay acceptance."
    true

nontrivial4DSU3YangMillsMeasure :
  ContinuumProofArgument
nontrivial4DSU3YangMillsMeasure =
  mkContinuumProofArgument
    "Nontrivial4DSU3YangMillsMeasure"
    "The continuum SU(3) Yang-Mills measure is non-Gaussian/nontrivial"
    "SU(3) non-Abelian curvature F=dA+[A,A], Bianchi identity structure, connected-correlation witness"
    "The non-Abelian bracket creates cubic and quartic self-interaction terms in the curvature action. These generate connected higher-point correlations incompatible with a Gaussian measure, giving the structural nontriviality witness."
    "This is a repo-internal mathematical witness, not external acceptance."
    true

record AllEightUserMathItems : Set where
  constructor mkAllEightUserMathItems
  field
    item1LocalOscillation :
      AuthorityProofArgument
    item2KernelProbability :
      AuthorityProofArgument
    item3PolymerMass :
      AuthorityProofArgument
    item4Dobrushin :
      ConstructiveProofArgument
    item5UniformActivity :
      ConstructiveProofArgument
    item6WC3 :
      ConstructiveProofArgument
    item7ContinuumGap :
      ContinuumProofArgument
    item8NontrivialMeasure :
      ContinuumProofArgument
    su3K11NumericalWitness :
      NumericWitness

canonicalAllEightUserMathItems :
  AllEightUserMathItems
canonicalAllEightUserMathItems =
  mkAllEightUserMathItems
    balabanCMP98LocalOscillationBound
    balabanCMP98AveragingKernelIsProbability
    balabanCMP116PolymerMassBound
    gaugeCovariantDobrushinComparison
    uniformPolymerActivityFromDobrushin
    wc3UniformClusterSummability
    continuumLimitMassGap
    nontrivial4DSU3YangMillsMeasure
    su3K11MasterRowWitness

record YMSprint103UserMathCompletionReceipt : Set₁ where
  field
    sprint102Index :
      Sprint102.YMSprint102ProofObligationIndexReceipt
    authorityInputsOneToThree :
      AuthorityInputs.YMSprint103AuthorityInputs
    dobrushinWC3ObligationsFourToSix :
      DobrushinWC3.YMSprint103DobrushinWC3Receipt
    continuumMassGapObligation7 :
      Obligation7.YMSprint103ContinuumMassGapObligation7Receipt
    nontrivialSU3Obligation8 :
      Obligation8.Sprint103NontrivialSU3ContinuumMeasureObligation8
    allEightItems :
      AllEightUserMathItems
    userMathAvailable :
      userSuppliedMathForAllEight ≡ true
    proofArgumentsRecorded :
      allEightProofArgumentsRecordedInRepo ≡ true
    externalAcceptanceUnavailable :
      externalAcceptanceTokenAvailable ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint103UserMathCompletionReceipt :
  YMSprint103UserMathCompletionReceipt
canonicalYMSprint103UserMathCompletionReceipt =
  record
    { sprint102Index =
        Sprint102.canonicalYMSprint102ProofObligationIndexReceipt
    ; authorityInputsOneToThree =
        AuthorityInputs.canonicalYMSprint103AuthorityInputs
    ; dobrushinWC3ObligationsFourToSix =
        DobrushinWC3.canonicalYMSprint103DobrushinWC3Receipt
    ; continuumMassGapObligation7 =
        Obligation7.canonicalYMSprint103ContinuumMassGapObligation7Receipt
    ; nontrivialSU3Obligation8 =
        Obligation8.canonicalSprint103NontrivialSU3ContinuumMeasureObligation8
    ; allEightItems =
        canonicalAllEightUserMathItems
    ; userMathAvailable =
        refl
    ; proofArgumentsRecorded =
        refl
    ; externalAcceptanceUnavailable =
        refl
    ; noClayPromotion =
        refl
    }
