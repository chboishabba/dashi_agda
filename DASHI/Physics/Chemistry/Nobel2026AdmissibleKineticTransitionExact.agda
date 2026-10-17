module DASHI.Physics.Chemistry.Nobel2026AdmissibleKineticTransitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact as ReactionBridge
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact as Dynamics
import DASHI.Physics.Chemistry.Nobel2026SoaiMechanisticKineticWeldExact as Kinetics

------------------------------------------------------------------------
-- SOAI CHEMISTRY ON THE REPO-NATIVE ADMISSIBLE-TRANSITION SPINE
--
-- The live-PR audit showed that the chemistry branch had source-paid kinetics
-- but had not yet inhabited the already-merged proof-relevant transition
-- grammar.  This module closes that seam.  Enablement, transition identity and
-- conditional kinetic coordinates are separate; a fitted rate coordinate is
-- never used to manufacture enablement or an ODE solution.
------------------------------------------------------------------------

soaiEnvironment : Chemistry.Environment
soaiEnvironment = record
  { temperatureCarrier = "Möhler et al. 2025 source-indexed temperature/protocol coordinate"
  ; pHCarrier = "not a promoted governing coordinate for the organozinc fixture"
  ; pressureCarrier = "source protocol coordinate"
  ; humidityCarrier = "source protocol coordinate"
  ; illuminationCarrier = "not promoted as the kinetic driver"
  ; ionicStrengthCarrier = "not promoted as an aqueous ionic-strength model"
  }

soaiCondition : Chemistry.Condition
soaiCondition = record
  { conditionLabel = "source-indexed Soai asymmetric-autocatalysis reaction condition"
  ; environment = soaiEnvironment
  ; guardExpression = "finite formal fixture enabled only inside the declared source/protocol scope"
  }

pyrimidylAldehyde : Chemistry.Species
pyrimidylAldehyde = record
  { speciesId = "Soai pyrimidyl aldehyde substrate family"
  ; phase = Chemistry.dissolved
  ; chargeLabel = "source-context neutral molecular substrate"
  ; compositionLabel = "source-specific substrate identity retained outside this coarse kernel label"
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "source kinetic concentration coordinate"
  ; opticalRoleLabel = "not used as an optical observable here"
  ; evidence = Chemistry.literatureEstablished
  }

dialkylzinc : Chemistry.Species
dialkylzinc = record
  { speciesId = "dialkylzinc reagent"
  ; phase = Chemistry.dissolved
  ; chargeLabel = "organozinc reagent coordinate"
  ; compositionLabel = "source-specific dialkylzinc identity"
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "source kinetic concentration coordinate"
  ; opticalRoleLabel = "not used as an optical observable here"
  ; evidence = Chemistry.literatureEstablished
  }

chiralProductAlcohol : Chemistry.Species
chiralProductAlcohol = record
  { speciesId = "chiral pyrimidyl alkanol product/autocatalyst family"
  ; phase = Chemistry.dissolved
  ; chargeLabel = "neutral product coordinate"
  ; compositionLabel = "source-specific chiral product identity"
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "product and catalytic-feedback concentration coordinate"
  ; opticalRoleLabel = "enantiomeric excess / handedness readout"
  ; evidence = Chemistry.literatureEstablished
  }

aldehydeTerm : Chemistry.StoichiometricTerm
aldehydeTerm = record { species = pyrimidylAldehyde ; coefficient = 1 }

zincTerm : Chemistry.StoichiometricTerm
zincTerm = record { species = dialkylzinc ; coefficient = 1 }

productTerm : Chemistry.StoichiometricTerm
productTerm = record { species = chiralProductAlcohol ; coefficient = 1 }

soaiFittedRateLaw : Chemistry.RateLaw
soaiFittedRateLaw = record
  { rateLawKind = Chemistry.empirical
  ; symbolicForm = "Möhler et al. 2025 fitted 18-equation autocatalytic network plus one reductive side-reaction ODE"
  ; parameters = []
  ; validityRegime = "same reaction family and source-indexed experimental protocol; supplementary RHS bodies are not reconstructed here"
  ; evidence = Chemistry.fitted
  }

soaiAutocatalyticTransition : Chemistry.Transition
soaiAutocatalyticTransition = record
  { transitionId = "Soai asymmetric autocatalytic product-forming transition"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = aldehydeTerm ∷ zincTerm ∷ []
  ; products = productTerm ∷ []
  ; catalysts = chiralProductAlcohol ∷ []
  ; rateLaw = soaiFittedRateLaw
  ; condition = soaiCondition
  ; reversibility = Chemistry.conditionallyReversible
  ; evidence = Chemistry.fitted
  }

------------------------------------------------------------------------
-- Typed finite semantics over the already-owned five-state chiral fixture.
-- `Enabled = top` is scoped to this declared finite formal fixture.  It is not
-- a claim that every physical mixture/protocol enables the wet reaction.
------------------------------------------------------------------------

soaiFiniteSemantics : ReactionBridge.TypedReactionSemantics soaiAutocatalyticTransition
soaiFiniteSemantics = record
  { State = Dynamics.ChiralBiasState
  ; Enabled = λ state environment → ⊤
  ; step = λ state environment → Dynamics.amplifyBias state
  ; InvariantRegion = λ state → ⊤
  ; enabledPreservesInvariant = λ state environment enabled invariant → tt
  ; reactantAvailabilityReference = "finite fixture assumes the declared reactant surface; physical concentration guards remain source/protocol indexed"
  ; catalystOrCofactorReference = "product alcohol is represented in the catalyst list to retain the autocatalytic feedback role"
  ; environmentGuardReference = "Möhler/Soai protocol coordinates; no universal environment gate is inferred"
  ; compartmentCompatibilityReference = "homogeneous reaction fixture; no prebiotic compartment is manufactured"
  ; invariantReference = "five-state handedness/amplification carrier remains inside its declared finite state type"
  }

soaiFiniteAdmitted :
  (x : Dynamics.ChiralBiasState) →
  (environment : Chemistry.Environment) →
  ReactionBridge.AdmittedReaction soaiFiniteSemantics x environment
soaiFiniteAdmitted x environment = Transition.admittedStep tt tt

soaiAdmittedStepIsAmplification :
  (x : Dynamics.ChiralBiasState) →
  (environment : Chemistry.Environment) →
  ReactionBridge.step soaiFiniteSemantics x environment ≡ Dynamics.amplifyBias x
soaiAdmittedStepIsAmplification x environment = refl

------------------------------------------------------------------------
-- Kinetic coordinates are conditional weights on an enabled transition.
-- Selecting k4 here records the source's rate-determining coordinate; it does
-- not make k4 alone the complete reaction velocity or solve the 19-ODE model.
------------------------------------------------------------------------

soaiRateDeterminingCoordinateWeight :
  ReactionBridge.ConditionalReactionWeight soaiFiniteSemantics
soaiRateDeterminingCoordinateWeight =
  ReactionBridge.conditionalReactionWeight
    Kinetics.RateCoordinate
    (λ state environment enabled → Kinetics.k4)
    "Möhler et al. 2025: k4 hemiacetal formation is the rate-determining coordinate; this conditional weight is not the complete ODE flux"

soaiWeightAsGenericConditionalEdgeWeight :
  Transition.ConditionalEdgeWeight
    (ReactionBridge.reactionTransitionSystem soaiFiniteSemantics)
soaiWeightAsGenericConditionalEdgeWeight =
  ReactionBridge.conditionalWeightAsGenericEdgeWeight
    soaiRateDeterminingCoordinateWeight

selectedWeightIsK4 :
  (x : Dynamics.ChiralBiasState) →
  (environment : Chemistry.Environment) →
  (enabled : ReactionBridge.Enabled soaiFiniteSemantics x environment) →
  ReactionBridge.weight soaiRateDeterminingCoordinateWeight x environment enabled
  ≡ Kinetics.k4
selectedWeightIsK4 x environment enabled = refl

selectedK4HasBimolecularRateUnit : Kinetics.rateUnit Kinetics.k4 ≡ Kinetics.perMolarSecond
selectedK4HasBimolecularRateUnit = Kinetics.k4Unit

------------------------------------------------------------------------
-- Source mirror-rate identity and formal mirror-equivariant finite dynamics
-- now live in one typed receipt, without deriving either from the other.
------------------------------------------------------------------------

record MirrorKineticCompatibilityReceipt : Set where
  constructor mirrorKineticCompatibilityReceipt
  field
    sourceMirrorCyclesUseSameRates : Bool
    sourceMirrorCyclesUseSameRatesIsTrue : sourceMirrorCyclesUseSameRates ≡ true
    finiteStepMirrorEquivariant :
      (x : Dynamics.ChiralBiasState) →
      Dynamics.amplifyBias (Dynamics.mirrorBias x)
      ≡ Dynamics.mirrorBias (Dynamics.amplifyBias x)

canonicalMirrorKineticCompatibilityReceipt : MirrorKineticCompatibilityReceipt
canonicalMirrorKineticCompatibilityReceipt =
  mirrorKineticCompatibilityReceipt
    (Kinetics.MechanisticReceipt.mirrorCyclesUseSameRates Kinetics.mohler2025MechanisticReceipt)
    (Kinetics.MechanisticReceipt.mirrorCyclesUseSameRatesIsTrue Kinetics.mohler2025MechanisticReceipt)
    Dynamics.amplifyMirrorEquivariant

record AdmissibleKineticTransitionBoundary : Set where
  constructor admissibleKineticTransitionBoundary
  field
    transitionKernelAutocatalystRolePaid : Bool
    proofRelevantEnablementSurfacePaid : Bool
    conditionalKineticCoordinatePaid : Bool
    rateDeterminingCoordinateUnitPaid : Bool
    mirrorRateAndFiniteEquivarianceJoined : Bool
    fittedCoordinateCreatesPhysicalEnablement : Bool
    finiteStepClaimsToSolveNineteenODEs : Bool
    catalystRoleProvesPrebioticCompartment : Bool

canonicalAdmissibleKineticTransitionBoundary : AdmissibleKineticTransitionBoundary
canonicalAdmissibleKineticTransitionBoundary =
  admissibleKineticTransitionBoundary
    true true true true true false false false
