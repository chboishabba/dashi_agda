{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSHypothesisMaxCutExact where

------------------------------------------------------------------------
-- MAX-CUT THE MARKED LOCAL-C OS HYPOTHESES AGAINST EXISTING ROUND109 DATA.
--
-- Already machine-owned:
--   * Round109 completion gives a nuclear-continuous stress field on the SAME
--     completed marked RG state.
--   * that field is literally Top.stressTensor Y group.
--   * Local-C marks that SAME stress tensor symmetric and local.
--   * Round128 keeps the stress and OS Schwinger recovery on one continuum.
--
-- Therefore E0/E3 should not be treated as blank assumptions.  What remains is
-- the exact semantic/topological upgrade:
--
--   E0 bridge: Round109 nuclear continuity is continuity in the OS E0
--              distribution/test-function topology required by reconstruction.
--
--   E3 bridge: Local-C symmetry/locality induces the marked Schwinger
--              permutation/locality condition.
--
-- The genuinely new marked analytic conditions are then:
--   E1 Euclidean rank-two tensor covariance,
--   E2 reflection-positivity compatibility of the extended hierarchy,
--   E4 marked clustering compatibility.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSWightmanReconstructionExact as MarkedOS
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119R109NuclearStressExact as R109Nuclear
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact as R128
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep

record MarkedStressOSHypothesisMaxCut
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    : Set₂ where
  field
    sameFamilyOSRecovery :
      R128.SameFamilyOSStressRecovery stressLane

    markedStressCompletion :
      R109.LiteralSchwingerStressMarkedCompletion Y group

    markedStressIsPinnedLocalCStress :
      Top.stressTensor Y group
      ≡ LocalC.stressTensor localC

    -- Target OS predicates, kept abstract because the current repo does not
    -- expose the Schwartz/distribution carrier used by the external theorem.
    MarkedE0Regularity : Set
    MarkedE1EuclideanTensorCovariance : Set
    MarkedE2ReflectionPositivityCompatibility : Set
    MarkedE3SymmetryLocality : Set
    MarkedE4ClusterCompatibility : Set

    -- Exact bridges from already-owned data.
    nuclearContinuityToMarkedE0 :
      Marked.fieldNuclearContinuous
        (R109Nuclear.r109StressNuclearField markedStressCompletion) →
      MarkedE0Regularity

    localCSymmetryLocalityToMarkedE3 :
      (LocalC.Symmetric localC (LocalC.stressTensor localC)
       ×
       LocalC.LocalStressTensor localC (LocalC.stressTensor localC)) →
      MarkedE3SymmetryLocality

    -- Genuine new marked analytic hypotheses.
    markedE1 :
      MarkedE1EuclideanTensorCovariance

    markedE2 :
      MarkedE2ReflectionPositivityCompatibility

    markedE4 :
      MarkedE4ClusterCompatibility

open MarkedStressOSHypothesisMaxCut public

compileMarkedOSHypotheses :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain
      representation stressLane
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC} →
  MarkedStressOSHypothesisMaxCut
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {C = C} {S = S} Y group
    {Scale = Scale} {Volume = Volume}
    {activity = activity} {domain = domain} {representation = representation}
    stressLane
    {G = G} {X = X} {Configuration = Configuration}
    {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
    {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
    {Hilbert = Hilbert} {Vector = Vector}
    {Hamiltonian = Hamiltonian} {Algebra = Algebra}
    {Root = Root} {ContinuumFamily = ContinuumFamily} {Core = Core}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division}
    {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
    localC →
  MarkedOS.LocalCStressMarkedOSHypotheses
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {C = C} {S = S} Y group
    {Scale = Scale} {Volume = Volume}
    {activity = activity} {domain = domain} {representation = representation}
    stressLane
    {G = G} {X = X} {Configuration = Configuration}
    {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
    {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
    {Hilbert = Hilbert} {Vector = Vector}
    {Hamiltonian = Hamiltonian} {Algebra = Algebra}
    {Root = Root} {ContinuumFamily = ContinuumFamily} {Core = Core}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division}
    {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
    localC
compileMarkedOSHypotheses {localC = localC} cut = record
  { MarkedOS.LocalCStressMarkedOSHypotheses.sameFamilyOSRecovery =
      sameFamilyOSRecovery cut
  ; MarkedOS.LocalCStressMarkedOSHypotheses.markedStressCompletion =
      markedStressCompletion cut
  ; MarkedOS.LocalCStressMarkedOSHypotheses.markedStressIsPinnedLocalCStress =
      markedStressIsPinnedLocalCStress cut
  ; MarkedOS.LocalCStressMarkedOSHypotheses.MarkedE0Regularity =
      MarkedE0Regularity cut
  ; MarkedOS.LocalCStressMarkedOSHypotheses.MarkedE1EuclideanTensorCovariance =
      MarkedE1EuclideanTensorCovariance cut
  ; MarkedOS.LocalCStressMarkedOSHypotheses.MarkedE2ReflectionPositivityCompatibility =
      MarkedE2ReflectionPositivityCompatibility cut
  ; MarkedOS.LocalCStressMarkedOSHypotheses.MarkedE3SymmetryLocality =
      MarkedE3SymmetryLocality cut
  ; MarkedOS.LocalCStressMarkedOSHypotheses.MarkedE4ClusterCompatibility =
      MarkedE4ClusterCompatibility cut
  ; MarkedOS.LocalCStressMarkedOSHypotheses.markedE0 =
      nuclearContinuityToMarkedE0 cut
        (Marked.fieldNuclearContinuous
          (R109Nuclear.r109StressNuclearField
            (markedStressCompletion cut)))
  ; MarkedOS.LocalCStressMarkedOSHypotheses.markedE1 =
      markedE1 cut
  ; MarkedOS.LocalCStressMarkedOSHypotheses.markedE2 =
      markedE2 cut
  ; MarkedOS.LocalCStressMarkedOSHypotheses.markedE3 =
      localCSymmetryLocalityToMarkedE3 cut
        ( LocalC.stressTensorSymmetric localC
        , LocalC.stressTensorLocal localC )
  ; MarkedOS.LocalCStressMarkedOSHypotheses.markedE4 =
      markedE4 cut
  }

round109NuclearContinuityAlreadyOwned : Bool
round109NuclearContinuityAlreadyOwned = true

localCStressSymmetryLocalityAlreadyOwned : Bool
localCStressSymmetryLocalityAlreadyOwned = true

newMarkedAnalyticCoreCount : Nat
newMarkedAnalyticCoreCount = 3

semanticTopologyBridgeCount : Nat
semanticTopologyBridgeCount = 2
