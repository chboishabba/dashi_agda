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
-- overlapping but non-identical terminology.  Family ownership is metadata for
-- choosing a common majorant; it is not operator equality.  In particular,
-- curvature, transport and chart are three distinct operators even though all
-- are estimated by the SU(2)-geometry defect family.  This module keeps those
-- notions separate and requires one literal operator for every constructor.
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
    t3Operator : T3Channel → Operator
    hrBetaOperator : HRBetaChannel → Operator

    t3FamilyOwner : T3Channel → PhysicalAnalyticFamily
    hrBetaFamilyOwner : HRBetaChannel → PhysicalAnalyticFamily

    t3FamilyOwnerMeaning : ∀ channel →
      t3FamilyOwner channel ≡ t3Family channel

    hrBetaFamilyOwnerMeaning : ∀ channel →
      hrBetaFamilyOwner channel ≡ hrBetaFamily channel

open PhysicalChannelOperatorIdentification public

t3CurvatureFamilyMeaning :
  ∀ {Operator}
    (identification : PhysicalChannelOperatorIdentification Operator) →
  t3FamilyOwner identification curvature ≡ su2Geometry
t3CurvatureFamilyMeaning identification =
  t3FamilyOwnerMeaning identification curvature

t3GaugeFamilyMeaning :
  ∀ {Operator}
    (identification : PhysicalChannelOperatorIdentification Operator) →
  t3FamilyOwner identification gauge ≡ resolventConstraint
t3GaugeFamilyMeaning identification =
  t3FamilyOwnerMeaning identification gauge

hrBetaDeterminantFamilyMeaning :
  ∀ {Operator}
    (identification : PhysicalChannelOperatorIdentification Operator) →
  hrBetaFamilyOwner identification determinant ≡ spectralDeterminant
hrBetaDeterminantFamilyMeaning identification =
  hrBetaFamilyOwnerMeaning identification determinant

hrBetaLocalizationFamilyMeaning :
  ∀ {Operator}
    (identification : PhysicalChannelOperatorIdentification Operator) →
  hrBetaFamilyOwner identification localization ≡ randomWalkLocalization
hrBetaLocalizationFamilyMeaning identification =
  hrBetaFamilyOwnerMeaning identification localization

physicalChannelEnumerationLevel : ProofLevel
physicalChannelEnumerationLevel = computed

physicalChannelFamilyMapLevel : ProofLevel
physicalChannelFamilyMapLevel = machineChecked

physicalChannelOperatorIdentificationInputsLevel : ProofLevel
physicalChannelOperatorIdentificationInputsLevel = conditional

physicalChannelEpsilonBudgetIdentificationInputsLevel : ProofLevel
physicalChannelEpsilonBudgetIdentificationInputsLevel = conditional
