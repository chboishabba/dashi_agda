module DASHI.Physics.YangMills.BalabanClayGate4PhysicalOperatorChannelIdentificationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exhaustive operator/channel naming audit.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- The five fluctuation-Hessian channels and the five H-R_beta channels use
-- overlapping but non-identical terminology.  This module fixes one exhaustive
-- map to the underlying analytic families.  A physical instantiation must give
-- literal operator equalities for every constructor, preventing an epsilon
-- budget or determinant/localization term from being silently dropped.
------------------------------------------------------------------------

data PhysicalAnalyticFamily : Set where
  su2Geometry : PhysicalAnalyticFamily
  resolventConstraint : PhysicalAnalyticFamily
  spectralDeterminant : PhysicalAnalyticFamily
  polymerInteraction : PhysicalAnalyticFamily
  randomWalkLocalization : PhysicalAnalyticFamily

data T3Channel : Set where
  curvature transport chart gauge constraint : T3Channel

data HRBetaChannel : Set where
  determinant interaction chartRemainder gaugeRemainder localization :
    HRBetaChannel

t3Family : T3Channel → PhysicalAnalyticFamily
t3Family curvature = su2Geometry
t3Family transport = su2Geometry
t3Family chart = su2Geometry
t3Family gauge = resolventConstraint
t3Family constraint = resolventConstraint

hrBetaFamily : HRBetaChannel → PhysicalAnalyticFamily
hrBetaFamily determinant = spectralDeterminant
hrBetaFamily interaction = polymerInteraction
hrBetaFamily chartRemainder = su2Geometry
hrBetaFamily gaugeRemainder = resolventConstraint
hrBetaFamily localization = randomWalkLocalization

allT3Channels : List T3Channel
allT3Channels = curvature ∷ transport ∷ chart ∷ gauge ∷ constraint ∷ []

allHRBetaChannels : List HRBetaChannel
allHRBetaChannels =
  determinant ∷ interaction ∷ chartRemainder ∷
  gaugeRemainder ∷ localization ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

t3ChannelCountFive : listLength allT3Channels ≡ 5
t3ChannelCountFive = refl

hrBetaChannelCountFive : listLength allHRBetaChannels ≡ 5
hrBetaChannelCountFive = refl

record PhysicalChannelOperatorIdentification (Operator : Set) : Set₁ where
  field
    operatorForFamily : PhysicalAnalyticFamily → Operator
    t3Operator : T3Channel → Operator
    hrBetaOperator : HRBetaChannel → Operator

    t3OperatorMeaning : ∀ channel →
      t3Operator channel ≡ operatorForFamily (t3Family channel)

    hrBetaOperatorMeaning : ∀ channel →
      hrBetaOperator channel ≡ operatorForFamily (hrBetaFamily channel)

open PhysicalChannelOperatorIdentification public

t3CurvatureOperatorMeaning :
  ∀ {Operator}
    (identification : PhysicalChannelOperatorIdentification Operator) →
  t3Operator identification curvature
  ≡ operatorForFamily identification su2Geometry
t3CurvatureOperatorMeaning identification =
  t3OperatorMeaning identification curvature

t3GaugeOperatorMeaning :
  ∀ {Operator}
    (identification : PhysicalChannelOperatorIdentification Operator) →
  t3Operator identification gauge
  ≡ operatorForFamily identification resolventConstraint
t3GaugeOperatorMeaning identification =
  t3OperatorMeaning identification gauge

hrBetaDeterminantOperatorMeaning :
  ∀ {Operator}
    (identification : PhysicalChannelOperatorIdentification Operator) →
  hrBetaOperator identification determinant
  ≡ operatorForFamily identification spectralDeterminant
hrBetaDeterminantOperatorMeaning identification =
  hrBetaOperatorMeaning identification determinant

hrBetaLocalizationOperatorMeaning :
  ∀ {Operator}
    (identification : PhysicalChannelOperatorIdentification Operator) →
  hrBetaOperator identification localization
  ≡ operatorForFamily identification randomWalkLocalization
hrBetaLocalizationOperatorMeaning identification =
  hrBetaOperatorMeaning identification localization

physicalChannelEnumerationLevel : ProofLevel
physicalChannelEnumerationLevel = computed

physicalChannelFamilyMapLevel : ProofLevel
physicalChannelFamilyMapLevel = machineChecked

physicalChannelOperatorIdentificationInputsLevel : ProofLevel
physicalChannelOperatorIdentificationInputsLevel = conditional

physicalChannelEpsilonBudgetIdentificationInputsLevel : ProofLevel
physicalChannelEpsilonBudgetIdentificationInputsLevel = conditional
