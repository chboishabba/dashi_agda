module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound5IntegratedExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; 1ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109PhysicalScaleGeometryExact as Physical
import DASHI.Physics.YangMills.BalabanClayGate4CMP109RadiusOneSplitFibreExact as Split
import DASHI.Physics.YangMills.BalabanClayGate4CMP109RadiusOneWeightExact as Weight
import DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusFromSignedTailsExact as Signed
import DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusScalarEnvelopeExact as HalfRadius
import DASHI.Physics.YangMills.BalabanClayGate4NewtonFourChannelQuarterExact as Newton
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalFunctionalSecondVariationExact as Functional
import DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact as Wilson
import DASHI.Physics.YangMills.BalabanClayGate4WilsonPlaquetteBadCubeBudgetExact as WilsonBudget
import DASHI.Physics.YangMills.BalabanClayGate4DyadicRandomWalkTailExact as RandomWalk
import DASHI.Physics.YangMills.BalabanClayGate4FiveActivityTenthToHalfExact as Activity

------------------------------------------------------------------------
-- Round five owns the strongest concrete instantiations extracted from the
-- previous physical cut.  It does not collapse the remaining local analytic
-- estimates into anonymous propositions: signed series tails, four Newton
-- channels, physical functional atoms, Wilson entropy comparison, random-walk
-- shell decay and five activity bounds are explicit data.
------------------------------------------------------------------------

record PhysicalClosureRound5Inputs : Set₂ where
  field
    CoarseSite : Set
    fineSpacing : Nat
    radiusOneGeometry :
      Physical.CMP109PhysicalScaleGeometry
        Split.one (Split.SplitFineSite Split.one CoarseSite) CoarseSite Nat

    SU2Scalar : Set
    scalarCore : Signed.SU2HalfRadiusScalarCore SU2Scalar
    scalarSignedTails : Signed.SU2HalfRadiusSignedTailInputs scalarCore

    NewtonBound : Set
    newtonAlgebra : Newton.FourChannelQuarterAlgebra NewtonBound
    newtonClosure :
      Newton.FederbushFaddeevPopovFourChannelClosure newtonAlgebra

    FunctionalCarrier Operator : Set
    secondVariation :
      Functional.AdditiveSecondVariationCalculus FunctionalCarrier Operator
    physicalAtoms :
      Functional.PhysicalFunctionalAtoms
        FunctionalCarrier Operator secondVariation

    WilsonScale Configuration Gauge Block Plaquette : Set
    wilsonLargeField :
      Wilson.LiteralWilsonLargeFieldData
        WilsonScale Configuration Gauge Block Plaquette
    wilsonCost : Wilson.LiteralWilsonCostData wilsonLargeField
    wilsonBadCubeBudget :
      WilsonBudget.WilsonPlaquetteBadCubeBudget wilsonLargeField wilsonCost

    randomWalkOrder : RandomWalk.DyadicRandomWalkOrder
    randomWalkBounds :
      RandomWalk.DyadicRandomWalkShellBound randomWalkOrder

    activityOrder : Activity.RationalAdditiveOrder
    activityAllocation : Activity.FiveActivityTenthAllocation activityOrder

open PhysicalClosureRound5Inputs public

round5RadiusOneBlockCardinality :
  (inputs : PhysicalClosureRound5Inputs) →
  ∀ coarse →
  length
    (Physical.physicalBlockElements (radiusOneGeometry inputs) coarse)
  ≡ Split.eightyOne
round5RadiusOneBlockCardinality inputs =
  Split.radiusOnePhysicalBlockHasEightyOneSites
    (radiusOneGeometry inputs)

round5SiteWeightReciprocal :
  Weight.oneOverEightyOneℚ * Weight.eightyOneℚ ≡ 1ℚ
round5SiteWeightReciprocal = Weight.radiusOneSiteWeightIsReciprocal

round5ScalarEnvelope :
  (inputs : PhysicalClosureRound5Inputs) →
  HalfRadius.SU2HalfRadiusScalarEnvelope (SU2Scalar inputs)
round5ScalarEnvelope inputs =
  Signed.halfRadiusEnvelopeFromSignedTails (scalarSignedTails inputs)

round5FederbushContractionBelowQuarter :
  (inputs : PhysicalClosureRound5Inputs) →
  Newton.LessEqual (newtonAlgebra inputs)
    (Newton.total
      (Newton.federbushContraction (newtonClosure inputs)))
    (Newton.quarter (newtonAlgebra inputs))
round5FederbushContractionBelowQuarter inputs =
  Newton.federbushContractionBelowQuarter (newtonClosure inputs)

round5FederbushForcingBelowQuarter :
  (inputs : PhysicalClosureRound5Inputs) →
  Newton.LessEqual (newtonAlgebra inputs)
    (Newton.total (Newton.federbushForcing (newtonClosure inputs)))
    (Newton.quarter (newtonAlgebra inputs))
round5FederbushForcingBelowQuarter inputs =
  Newton.federbushForcingBelowQuarter (newtonClosure inputs)

round5FaddeevPopovContractionBelowQuarter :
  (inputs : PhysicalClosureRound5Inputs) →
  Newton.LessEqual (newtonAlgebra inputs)
    (Newton.total
      (Newton.faddeevPopovContraction (newtonClosure inputs)))
    (Newton.quarter (newtonAlgebra inputs))
round5FaddeevPopovContractionBelowQuarter inputs =
  Newton.faddeevPopovContractionBelowQuarter (newtonClosure inputs)

round5FaddeevPopovForcingBelowQuarter :
  (inputs : PhysicalClosureRound5Inputs) →
  Newton.LessEqual (newtonAlgebra inputs)
    (Newton.total (Newton.faddeevPopovForcing (newtonClosure inputs)))
    (Newton.quarter (newtonAlgebra inputs))
round5FaddeevPopovForcingBelowQuarter inputs =
  Newton.faddeevPopovForcingBelowQuarter (newtonClosure inputs)

round5SelectedFunctionalSecondVariation :
  (inputs : PhysicalClosureRound5Inputs) →
  Functional.hessian (secondVariation inputs)
    (Functional.selectedPhysicalFunctional (physicalAtoms inputs))
  ≡ Functional.selectedPhysicalHessian (physicalAtoms inputs)
round5SelectedFunctionalSecondVariation inputs =
  Functional.selectedFunctionalSecondVariationExact (physicalAtoms inputs)

round5WilsonBadPlaquettePaysPenalty :
  (inputs : PhysicalClosureRound5Inputs) →
  ∀ configuration plaquette →
  Wilson.LargePlaquette
    (wilsonLargeField inputs)
    (WilsonBudget.scale (wilsonBadCubeBudget inputs))
    configuration plaquette →
  WilsonBudget.wilsonPenaltyPerBadCube (wilsonBadCubeBudget inputs)
  ≤ Wilson.scaledWilsonPlaquetteCost
      (wilsonCost inputs)
      (WilsonBudget.scale (wilsonBadCubeBudget inputs))
      configuration plaquette
round5WilsonBadPlaquettePaysPenalty inputs =
  WilsonBudget.largePlaquettePaysWilsonBadCubePenalty
    (wilsonBadCubeBudget inputs)

round5RandomWalkPartialBelowDoubleAmplitude :
  (inputs : PhysicalClosureRound5Inputs) →
  ∀ depth →
  RandomWalk.LessEqual (randomWalkOrder inputs)
    (RandomWalk.randomWalkPartialNorm
      (RandomWalk.shellNorm (randomWalkBounds inputs)) depth)
    (RandomWalk.amplitude (randomWalkBounds inputs)
      + RandomWalk.amplitude (randomWalkBounds inputs))
round5RandomWalkPartialBelowDoubleAmplitude inputs =
  RandomWalk.randomWalkPartialBelowDoubleAmplitude
    (randomWalkBounds inputs)

round5FiveActivitiesBelowHalf :
  (inputs : PhysicalClosureRound5Inputs) →
  Activity.LessEqual (activityOrder inputs)
    (Activity.total (activityAllocation inputs))
    (Activity.delta (activityAllocation inputs) * Activity.halfℚ)
round5FiveActivitiesBelowHalf inputs =
  Activity.fiveActivityTotalBelowHalf (activityAllocation inputs)

physicalClosureRound5IntegratedCarrierLevel : ProofLevel
physicalClosureRound5IntegratedCarrierLevel = machineChecked

physicalClosureRound5ConcreteCMP109Level : ProofLevel
physicalClosureRound5ConcreteCMP109Level = machineChecked

physicalClosureRound5SignedTailAndNewtonLevel : ProofLevel
physicalClosureRound5SignedTailAndNewtonLevel = machineChecked

physicalClosureRound5FunctionalAndPolymerLevel : ProofLevel
physicalClosureRound5FunctionalAndPolymerLevel = machineChecked
