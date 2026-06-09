module DASHI.Promotion.ClassicalFieldObligations where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Constants.Registry as Registry

------------------------------------------------------------------------
-- Classical-field promotion obligations.
--
-- This module is a promotion-work surface for physical-law, Maxwell, and
-- GR field-equation lanes.  It does not promote those claims.  It records
-- the concrete obligations that must be supplied before the corresponding
-- guard can flip, and it ties those obligations back to the populated
-- constants/law registry.

data PromotionTarget : Set where
  physicalLawTarget : PromotionTarget
  maxwellFieldEquationTarget : PromotionTarget
  grFieldEquationTarget : PromotionTarget

data PromotionStage : Set where
  carrierNamed : PromotionStage
  unitsBound : PromotionStage
  boundaryConditionsBound : PromotionStage
  observableMapBound : PromotionStage
  adapterReceiptRequired : PromotionStage
  proofOrAuthorityTokenRequired : PromotionStage
  promotionGuardStillClosed : PromotionStage

data LawCarrierKind : Set where
  scalarFieldCarrier : LawCarrierKind
  vectorFieldCarrier : LawCarrierKind
  differentialFormCarrier : LawCarrierKind
  tensorFieldCarrier : LawCarrierKind
  connectionCarrier : LawCarrierKind
  metricFieldCarrier : LawCarrierKind
  stressEnergyFieldCarrier : LawCarrierKind
  sourceCurrentCarrier : LawCarrierKind

data UnitConventionKind : Set where
  siUnitConvention : UnitConventionKind
  geometricUnitConvention : UnitConventionKind
  naturalUnitConvention : UnitConventionKind
  mixedAuthorityUnitConvention : UnitConventionKind

data BoundaryConditionKind : Set where
  cauchyInitialData : BoundaryConditionKind
  dirichletBoundaryData : BoundaryConditionKind
  neumannBoundaryData : BoundaryConditionKind
  asymptoticFlatnessData : BoundaryConditionKind
  gaugeFixingData : BoundaryConditionKind
  sourceSupportData : BoundaryConditionKind
  cosmologicalBoundaryData : BoundaryConditionKind

data ObservableMapKind : Set where
  pointwiseFieldReadout : ObservableMapKind
  fluxIntegralReadout : ObservableMapKind
  stressEnergyReadout : ObservableMapKind
  geodesicDeviationReadout : ObservableMapKind
  curvatureScalarReadout : ObservableMapKind
  weakFieldLimitReadout : ObservableMapKind
  redshiftDistanceReadout : ObservableMapKind
  detectorCalibrationReadout : ObservableMapKind

data ObligationStatus : Set where
  obligationNamedOnly : ObligationStatus
  obligationAdapterMissing : ObligationStatus
  obligationAuthorityMissing : ObligationStatus
  obligationProofMissing : ObligationStatus
  obligationValidationMissing : ObligationStatus
  obligationSatisfied : ObligationStatus

data ClassicalLawFamily : Set where
  continuumMechanicsFamily : ClassicalLawFamily
  electrodynamicsFamily : ClassicalLawFamily
  gravitationFamily : ClassicalLawFamily
  thermodynamicsFamily : ClassicalLawFamily
  conservationFamily : ClassicalLawFamily

record LawCarrierObligation : Set₁ where
  field
    lawLabel : String
    registryLawSlotLabel : String
    lawFamily : ClassicalLawFamily
    carrierKind : LawCarrierKind
    carrierObject : String
    variableSignature : List String
    regularityRequirement : String
    coordinateOrGaugeChoice : String
    requiredConstants : List String
    sourceRegistry : ConstantsRegistry
    carrierSupplied : Bool
    carrierSuppliedProof : carrierSupplied ≡ true
    lawPromoted : Bool
    lawPromotedProof : lawPromoted ≡ false

open LawCarrierObligation public

record UnitBindingObligation : Set₁ where
  field
    unitLabel : String
    convention : UnitConventionKind
    baseUnits : List String
    derivedUnits : List String
    exactConstantsUsed : List String
    measuredConstantsUsed : List String
    normalizationRule : String
    authorityReceiptRequired : String
    unitBindingSupplied : Bool
    unitBindingSuppliedProof : unitBindingSupplied ≡ true
    numericMeasuredValuesPromoted : Bool
    numericMeasuredValuesPromotedProof :
      numericMeasuredValuesPromoted ≡ false

open UnitBindingObligation public

record BoundaryConditionObligation : Set₁ where
  field
    boundaryLabel : String
    boundaryKinds : List BoundaryConditionKind
    domainObject : String
    initialDataObject : String
    sourceSupportObject : String
    compatibilityConditions : List String
    globalAssumptions : List String
    boundaryReceiptRequired : String
    boundaryConditionsSupplied : Bool
    boundaryConditionsSuppliedProof : boundaryConditionsSupplied ≡ true
    theoremBoundaryPromoted : Bool
    theoremBoundaryPromotedProof : theoremBoundaryPromoted ≡ false

open BoundaryConditionObligation public

record ObservableMapObligation : Set₁ where
  field
    observableLabel : String
    observableKinds : List ObservableMapKind
    mathematicalObservable : String
    instrumentOrProviderSurface : String
    projectionLawRequired : String
    comparisonLawRequired : String
    calibrationReceiptRequired : String
    validationTarget : String
    observableMapSupplied : Bool
    observableMapSuppliedProof : observableMapSupplied ≡ true
    empiricalAdequacyPromoted : Bool
    empiricalAdequacyPromotedProof :
      empiricalAdequacyPromoted ≡ false

open ObservableMapObligation public

record ClassicalLawPromotionObligation : Set₁ where
  field
    target : PromotionTarget
    stage : PromotionStage
    carrierObligation : LawCarrierObligation
    unitObligation : UnitBindingObligation
    boundaryObligation : BoundaryConditionObligation
    observableObligation : ObservableMapObligation
    adapterReceiptsRequired : List String
    proofReceiptsRequired : List String
    authorityReceiptsRequired : List String
    validationCommands : List String
    currentStatus : ObligationStatus
    promotionGuard : Bool
    promotionGuardProof : promotionGuard ≡ false

open ClassicalLawPromotionObligation public

------------------------------------------------------------------------
-- Maxwell field-equation obligations.

data MaxwellFieldObject : Set where
  electromagneticPotentialOneForm : MaxwellFieldObject
  electromagneticCurvatureTwoForm : MaxwellFieldObject
  hodgeDualCurvatureTwoForm : MaxwellFieldObject
  electricChargeCurrentThreeForm : MaxwellFieldObject
  lorentzForceObservable : MaxwellFieldObject

record MaxwellCurvatureObligation : Set₁ where
  field
    potentialCarrier : MaxwellFieldObject
    curvatureCarrier : MaxwellFieldObject
    curvatureConstruction : String
    bianchiIdentityTarget : String
    gaugeEquivalenceReceiptRequired : String
    curvatureCarrierSupplied : Bool
    curvatureCarrierSuppliedProof : curvatureCarrierSupplied ≡ true
    curvatureEquationPromoted : Bool
    curvatureEquationPromotedProof : curvatureEquationPromoted ≡ false

open MaxwellCurvatureObligation public

record MaxwellHodgeObligation : Set₁ where
  field
    metricCarrierRequired : String
    orientationVolumeCarrierRequired : String
    hodgeStarOnTwoFormsRequired : String
    unitConventionRequired : UnitConventionKind
    epsilon0Mu0AuthorityRequired : String
    hodgeCarrierSupplied : Bool
    hodgeCarrierSuppliedProof : hodgeCarrierSupplied ≡ true
    hodgeEquationPromoted : Bool
    hodgeEquationPromotedProof : hodgeEquationPromoted ≡ false

open MaxwellHodgeObligation public

record MaxwellSourceCurrentObligation : Set₁ where
  field
    currentCarrier : MaxwellFieldObject
    chargeDensityObject : String
    currentDensityObject : String
    continuityEquationTarget : String
    sourceExtractionReceiptRequired : String
    chargeCalibrationReceiptRequired : String
    currentCarrierSupplied : Bool
    currentCarrierSuppliedProof : currentCarrierSupplied ≡ true
    sourceCurrentPromoted : Bool
    sourceCurrentPromotedProof : sourceCurrentPromoted ≡ false

open MaxwellSourceCurrentObligation public

record MaxwellFieldEquationPromotionObligation : Set₁ where
  field
    maxwellPhysicalLawObligation : ClassicalLawPromotionObligation
    maxwellCurvatureObligation : MaxwellCurvatureObligation
    hodgeObligation : MaxwellHodgeObligation
    sourceCurrentObligation : MaxwellSourceCurrentObligation
    homogeneousEquationTarget : String
    inhomogeneousEquationTarget : String
    lorentzForceAdapterRequired : String
    empiricalObservableAdapterRequired : String
    maxwellFieldEquationPromoted : Bool
    maxwellFieldEquationPromotedProof :
      maxwellFieldEquationPromoted ≡ false

open MaxwellFieldEquationPromotionObligation public

------------------------------------------------------------------------
-- General-relativity field-equation obligations.

data GRFieldObject : Set where
  lorentzianMetricObject : GRFieldObject
  leviCivitaConnectionObject : GRFieldObject
  riemannCurvatureObject : GRFieldObject
  ricciCurvatureObject : GRFieldObject
  scalarCurvatureObject : GRFieldObject
  einsteinTensorObject : GRFieldObject
  stressEnergyTensorObject : GRFieldObject

record GRMetricObligation : Set₁ where
  field
    grMetricCarrier : GRFieldObject
    manifoldObject : String
    signatureConvention : String
    nonDegeneracyProofRequired : String
    lorentzianSignatureProofRequired : String
    inverseMetricReceiptRequired : String
    metricCarrierSupplied : Bool
    metricCarrierSuppliedProof : metricCarrierSupplied ≡ true
    metricPromotion : Bool
    metricPromotionProof : metricPromotion ≡ false

open GRMetricObligation public

record GRConnectionObligation : Set₁ where
  field
    grConnectionCarrier : GRFieldObject
    torsionFreeProofRequired : String
    metricCompatibilityProofRequired : String
    christoffelSymbolReceiptRequired : String
    coordinateChangeLawRequired : String
    connectionCarrierSupplied : Bool
    connectionCarrierSuppliedProof : connectionCarrierSupplied ≡ true
    connectionPromotion : Bool
    connectionPromotionProof : connectionPromotion ≡ false

open GRConnectionObligation public

record GRCurvatureObligation : Set₁ where
  field
    riemannCarrier : GRFieldObject
    ricciCarrier : GRFieldObject
    scalarCarrier : GRFieldObject
    einsteinCarrier : GRFieldObject
    contractionReceiptsRequired : List String
    bianchiIdentityReceiptRequired : String
    weakFieldLimitReceiptRequired : String
    curvatureCarriersSupplied : Bool
    curvatureCarriersSuppliedProof : curvatureCarriersSupplied ≡ true
    curvaturePromotion : Bool
    curvaturePromotionProof : curvaturePromotion ≡ false

open GRCurvatureObligation public

record GRStressEnergyObligation : Set₁ where
  field
    grStressEnergyCarrier : GRFieldObject
    matterModelObject : String
    conservationLawTarget : String
    energyConditionBoundary : String
    sourceCouplingReceiptRequired : String
    stressEnergyCarrierSupplied : Bool
    stressEnergyCarrierSuppliedProof : stressEnergyCarrierSupplied ≡ true
    stressEnergyPromotion : Bool
    stressEnergyPromotionProof : stressEnergyPromotion ≡ false

open GRStressEnergyObligation public

record GRNormalizationObligation : Set₁ where
  field
    gravitationalConstantSlot : String
    speedOfLightSlot : String
    couplingNormalization : String
    grNormalizationUnitConvention : UnitConventionKind
    codataAuthorityReceiptRequired : String
    exactSIReceiptRequired : String
    normalizationSupplied : Bool
    normalizationSuppliedProof : normalizationSupplied ≡ true
    measuredGValuePromoted : Bool
    measuredGValuePromotedProof : measuredGValuePromoted ≡ false

open GRNormalizationObligation public

record GRFieldEquationPromotionObligation : Set₁ where
  field
    grPhysicalLawObligation : ClassicalLawPromotionObligation
    metricObligation : GRMetricObligation
    connectionObligation : GRConnectionObligation
    grCurvatureObligation : GRCurvatureObligation
    stressEnergyObligation : GRStressEnergyObligation
    normalizationObligation : GRNormalizationObligation
    einsteinEquationTarget : String
    cosmologyOrWeakFieldObservableRequired : String
    grFieldEquationPromoted : Bool
    grFieldEquationPromotedProof : grFieldEquationPromoted ≡ false

open GRFieldEquationPromotionObligation public

------------------------------------------------------------------------
-- List utilities and populated canonical rows.

listLength : {a : Level} {A : Set a} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

canonicalPhysicalLawCarrierObligation : LawCarrierObligation
canonicalPhysicalLawCarrierObligation = record
  { lawLabel = "physical-law promotion carrier package"
  ; registryLawSlotLabel =
      "registry physics law slots: conservation, Maxwell, GR, NS, YM"
  ; lawFamily = conservationFamily
  ; carrierKind = tensorFieldCarrier
  ; carrierObject =
      "lane-specific carrier with variables, equations, and validity regime"
  ; variableSignature =
      "fields"
      ∷ "sources"
      ∷ "domain"
      ∷ "time/space variables"
      ∷ []
  ; regularityRequirement =
      "regularity must be stated per law before theorem promotion"
  ; coordinateOrGaugeChoice =
      "coordinate, chart, gauge, or invariant formulation must be named"
  ; requiredConstants =
      "c"
      ∷ "h where quantum-facing"
      ∷ "G where gravitational"
      ∷ "epsilon_0/mu_0 where SI electrodynamics"
      ∷ []
  ; sourceRegistry = repoWideConstantsRegistry
  ; carrierSupplied = true
  ; carrierSuppliedProof = refl
  ; lawPromoted = false
  ; lawPromotedProof = refl
  }

canonicalClassicalUnitBindingObligation : UnitBindingObligation
canonicalClassicalUnitBindingObligation = record
  { unitLabel = "classical field unit and normalization binding"
  ; convention = siUnitConvention
  ; baseUnits =
      "s"
      ∷ "m"
      ∷ "kg"
      ∷ "A"
      ∷ []
  ; derivedUnits =
      "N"
      ∷ "J"
      ∷ "C"
      ∷ "V"
      ∷ "T"
      ∷ "Pa"
      ∷ []
  ; exactConstantsUsed =
      "c"
      ∷ "e"
      ∷ "h"
      ∷ []
  ; measuredConstantsUsed =
      "G"
      ∷ "epsilon_0"
      ∷ "mu_0"
      ∷ []
  ; normalizationRule =
      "state SI/geometric/natural convention before consuming equations"
  ; authorityReceiptRequired =
      "canonicalAuthorityConsumptionPolicyReceipt"
  ; unitBindingSupplied = true
  ; unitBindingSuppliedProof = refl
  ; numericMeasuredValuesPromoted = false
  ; numericMeasuredValuesPromotedProof = refl
  }

canonicalClassicalBoundaryConditionObligation :
  BoundaryConditionObligation
canonicalClassicalBoundaryConditionObligation = record
  { boundaryLabel = "classical field boundary and domain binding"
  ; boundaryKinds =
      cauchyInitialData
      ∷ dirichletBoundaryData
      ∷ neumannBoundaryData
      ∷ asymptoticFlatnessData
      ∷ gaugeFixingData
      ∷ sourceSupportData
      ∷ []
  ; domainObject =
      "spacetime/domain object with boundary and regularity assumptions"
  ; initialDataObject =
      "Cauchy or elliptic data appropriate to the law"
  ; sourceSupportObject =
      "compact, asymptotic, distributional, or provider-stated source support"
  ; compatibilityConditions =
      "constraint equations"
      ∷ "gauge compatibility"
      ∷ "source conservation"
      ∷ "regularity compatibility"
      ∷ []
  ; globalAssumptions =
      "orientation/time-orientation where needed"
      ∷ "topology and boundary regime"
      ∷ []
  ; boundaryReceiptRequired =
      "lane-specific boundary-condition receipt"
  ; boundaryConditionsSupplied = true
  ; boundaryConditionsSuppliedProof = refl
  ; theoremBoundaryPromoted = false
  ; theoremBoundaryPromotedProof = refl
  }

canonicalClassicalObservableMapObligation :
  ObservableMapObligation
canonicalClassicalObservableMapObligation = record
  { observableLabel = "classical field observable map"
  ; observableKinds =
      pointwiseFieldReadout
      ∷ fluxIntegralReadout
      ∷ stressEnergyReadout
      ∷ weakFieldLimitReadout
      ∷ detectorCalibrationReadout
      ∷ []
  ; mathematicalObservable =
      "field, flux, force, curvature, or stress-energy observable"
  ; instrumentOrProviderSurface =
      "provider/instrument/calibration source receipt"
  ; projectionLawRequired =
      "projection from formal carrier to measured observable"
  ; comparisonLawRequired =
      "comparison law against authority or empirical data"
  ; calibrationReceiptRequired =
      "unit, covariance, uncertainty, and instrument calibration receipt"
  ; validationTarget =
      "lane-specific executable validation or theorem check"
  ; observableMapSupplied = true
  ; observableMapSuppliedProof = refl
  ; empiricalAdequacyPromoted = false
  ; empiricalAdequacyPromotedProof = refl
  }

canonicalPhysicalLawPromotionObligation :
  ClassicalLawPromotionObligation
canonicalPhysicalLawPromotionObligation = record
  { target = physicalLawTarget
  ; stage = promotionGuardStillClosed
  ; carrierObligation = canonicalPhysicalLawCarrierObligation
  ; unitObligation = canonicalClassicalUnitBindingObligation
  ; boundaryObligation = canonicalClassicalBoundaryConditionObligation
  ; observableObligation = canonicalClassicalObservableMapObligation
  ; adapterReceiptsRequired =
      "carrier-to-law adapter"
      ∷ "unit-normalization adapter"
      ∷ "boundary-condition adapter"
      ∷ "observable projection adapter"
      ∷ []
  ; proofReceiptsRequired =
      "well-typed law statement"
      ∷ "validity-regime proof"
      ∷ "comparison theorem or accepted authority token"
      ∷ []
  ; authorityReceiptsRequired =
      "canonicalAuthorityConsumptionPolicyReceipt"
      ∷ "canonicalPhysicsAdapterKnownInputsReferenceReceipt"
      ∷ []
  ; validationCommands =
      "agda -i . DASHI/Promotion/ClassicalFieldObligations.agda"
      ∷ "agda -i . DASHI/Constants/Registry.agda"
      ∷ []
  ; currentStatus = obligationProofMissing
  ; promotionGuard = false
  ; promotionGuardProof = refl
  }

canonicalMaxwellCurvatureObligation : MaxwellCurvatureObligation
canonicalMaxwellCurvatureObligation = record
  { potentialCarrier = electromagneticPotentialOneForm
  ; curvatureCarrier = electromagneticCurvatureTwoForm
  ; curvatureConstruction =
      "F = d A, or gauge-invariant two-form carrier supplied directly"
  ; bianchiIdentityTarget =
      "d F = 0"
  ; gaugeEquivalenceReceiptRequired =
      "A -> A + d lambda equivalence and F-invariance receipt"
  ; curvatureCarrierSupplied = true
  ; curvatureCarrierSuppliedProof = refl
  ; curvatureEquationPromoted = false
  ; curvatureEquationPromotedProof = refl
  }

canonicalMaxwellHodgeObligation : MaxwellHodgeObligation
canonicalMaxwellHodgeObligation = record
  { metricCarrierRequired =
      "Lorentzian metric and orientation for Hodge star"
  ; orientationVolumeCarrierRequired =
      "volume form with sign convention"
  ; hodgeStarOnTwoFormsRequired =
      "* : two-forms -> two-forms in four spacetime dimensions"
  ; unitConventionRequired = siUnitConvention
  ; epsilon0Mu0AuthorityRequired =
      "NIST CODATA authority slots for epsilon_0 and mu_0"
  ; hodgeCarrierSupplied = true
  ; hodgeCarrierSuppliedProof = refl
  ; hodgeEquationPromoted = false
  ; hodgeEquationPromotedProof = refl
  }

canonicalMaxwellSourceCurrentObligation :
  MaxwellSourceCurrentObligation
canonicalMaxwellSourceCurrentObligation = record
  { currentCarrier = electricChargeCurrentThreeForm
  ; chargeDensityObject =
      "rho or charge-current density component under selected convention"
  ; currentDensityObject =
      "J vector/current form with continuity law"
  ; continuityEquationTarget =
      "d J = 0 or partial_mu J^mu = 0"
  ; sourceExtractionReceiptRequired =
      "matter-to-current adapter receipt"
  ; chargeCalibrationReceiptRequired =
      "charge/current calibration receipt consuming e, epsilon_0, mu_0"
  ; currentCarrierSupplied = true
  ; currentCarrierSuppliedProof = refl
  ; sourceCurrentPromoted = false
  ; sourceCurrentPromotedProof = refl
  }

canonicalMaxwellFieldEquationPromotionObligation :
  MaxwellFieldEquationPromotionObligation
canonicalMaxwellFieldEquationPromotionObligation = record
  { maxwellPhysicalLawObligation = canonicalPhysicalLawPromotionObligation
  ; maxwellCurvatureObligation = canonicalMaxwellCurvatureObligation
  ; hodgeObligation = canonicalMaxwellHodgeObligation
  ; sourceCurrentObligation = canonicalMaxwellSourceCurrentObligation
  ; homogeneousEquationTarget = "d F = 0"
  ; inhomogeneousEquationTarget = "d * F = J"
  ; lorentzForceAdapterRequired =
      "charged matter trajectory/force adapter"
  ; empiricalObservableAdapterRequired =
      "field/flux/force observable and calibration adapter"
  ; maxwellFieldEquationPromoted = false
  ; maxwellFieldEquationPromotedProof = refl
  }

canonicalGRMetricObligation : GRMetricObligation
canonicalGRMetricObligation = record
  { grMetricCarrier = lorentzianMetricObject
  ; manifoldObject =
      "smooth four-dimensional spacetime manifold or accepted substitute"
  ; signatureConvention =
      "(-,+,+,+) or (+,-,-,-), explicitly recorded"
  ; nonDegeneracyProofRequired =
      "det(g) nonzero / inverse metric receipt"
  ; lorentzianSignatureProofRequired =
      "one timelike and three spacelike directions under convention"
  ; inverseMetricReceiptRequired =
      "g^{mu nu} inverse metric and index-raising/lowering receipt"
  ; metricCarrierSupplied = true
  ; metricCarrierSuppliedProof = refl
  ; metricPromotion = false
  ; metricPromotionProof = refl
  }

canonicalGRConnectionObligation : GRConnectionObligation
canonicalGRConnectionObligation = record
  { grConnectionCarrier = leviCivitaConnectionObject
  ; torsionFreeProofRequired =
      "Gamma^rho_{mu nu} = Gamma^rho_{nu mu}"
  ; metricCompatibilityProofRequired =
      "nabla_mu g_{alpha beta} = 0"
  ; christoffelSymbolReceiptRequired =
      "Christoffel formula from metric and inverse metric"
  ; coordinateChangeLawRequired =
      "connection transformation law or invariant connection carrier"
  ; connectionCarrierSupplied = true
  ; connectionCarrierSuppliedProof = refl
  ; connectionPromotion = false
  ; connectionPromotionProof = refl
  }

canonicalGRCurvatureObligation : GRCurvatureObligation
canonicalGRCurvatureObligation = record
  { riemannCarrier = riemannCurvatureObject
  ; ricciCarrier = ricciCurvatureObject
  ; scalarCarrier = scalarCurvatureObject
  ; einsteinCarrier = einsteinTensorObject
  ; contractionReceiptsRequired =
      "Riemann from connection"
      ∷ "Ricci contraction"
      ∷ "scalar curvature contraction"
      ∷ "Einstein tensor construction"
      ∷ []
  ; bianchiIdentityReceiptRequired =
      "contracted Bianchi identity nabla_mu G^{mu nu} = 0"
  ; weakFieldLimitReceiptRequired =
      "Newtonian/weak-field known-limit comparison"
  ; curvatureCarriersSupplied = true
  ; curvatureCarriersSuppliedProof = refl
  ; curvaturePromotion = false
  ; curvaturePromotionProof = refl
  }

canonicalGRStressEnergyObligation : GRStressEnergyObligation
canonicalGRStressEnergyObligation = record
  { grStressEnergyCarrier = stressEnergyTensorObject
  ; matterModelObject =
      "matter, radiation, fluid, scalar, or effective stress-energy model"
  ; conservationLawTarget =
      "nabla_mu T^{mu nu} = 0"
  ; energyConditionBoundary =
      "energy conditions are optional assumptions, not automatic truths"
  ; sourceCouplingReceiptRequired =
      "matter-to-stress-energy adapter and conservation compatibility"
  ; stressEnergyCarrierSupplied = true
  ; stressEnergyCarrierSuppliedProof = refl
  ; stressEnergyPromotion = false
  ; stressEnergyPromotionProof = refl
  }

canonicalGRNormalizationObligation : GRNormalizationObligation
canonicalGRNormalizationObligation = record
  { gravitationalConstantSlot = "G"
  ; speedOfLightSlot = "c"
  ; couplingNormalization =
      "G_{mu nu} + Lambda g_{mu nu} = (8 pi G / c^4) T_{mu nu}"
  ; grNormalizationUnitConvention = siUnitConvention
  ; codataAuthorityReceiptRequired =
      "measured CODATA authority receipt for G"
  ; exactSIReceiptRequired =
      "exact SI authority receipt for c"
  ; normalizationSupplied = true
  ; normalizationSuppliedProof = refl
  ; measuredGValuePromoted = false
  ; measuredGValuePromotedProof = refl
  }

canonicalGRFieldEquationPromotionObligation :
  GRFieldEquationPromotionObligation
canonicalGRFieldEquationPromotionObligation = record
  { grPhysicalLawObligation = canonicalPhysicalLawPromotionObligation
  ; metricObligation = canonicalGRMetricObligation
  ; connectionObligation = canonicalGRConnectionObligation
  ; grCurvatureObligation = canonicalGRCurvatureObligation
  ; stressEnergyObligation = canonicalGRStressEnergyObligation
  ; normalizationObligation = canonicalGRNormalizationObligation
  ; einsteinEquationTarget =
      "G_{mu nu} + Lambda g_{mu nu} = (8 pi G / c^4) T_{mu nu}"
  ; cosmologyOrWeakFieldObservableRequired =
      "weak-field, geodesic, redshift-distance, or cosmology observable adapter"
  ; grFieldEquationPromoted = false
  ; grFieldEquationPromotedProof = refl
  }

canonicalClassicalPromotionObligations :
  List ClassicalLawPromotionObligation
canonicalClassicalPromotionObligations =
  canonicalPhysicalLawPromotionObligation
  ∷ []

canonicalMaxwellPromotionObligations :
  List MaxwellFieldEquationPromotionObligation
canonicalMaxwellPromotionObligations =
  canonicalMaxwellFieldEquationPromotionObligation
  ∷ []

canonicalGRPromotionObligations :
  List GRFieldEquationPromotionObligation
canonicalGRPromotionObligations =
  canonicalGRFieldEquationPromotionObligation
  ∷ []

record ClassicalFieldPromotionObligationIndex : Set₁ where
  field
    indexLabel : String
    indexSourceRegistry : ConstantsRegistry
    consumedPopulationReceipt : KnownInputsPopulationReceipt
    consumedPhysicsAdapterReceipt : PhysicsAdapterKnownInputsReferenceReceipt
    lawObligations : List ClassicalLawPromotionObligation
    maxwellObligations : List MaxwellFieldEquationPromotionObligation
    grObligations : List GRFieldEquationPromotionObligation
    promotionStages : List PromotionStage
    globalValidationCommands : List String
    physicalLawsPromoted : Bool
    physicalLawsPromotedProof : physicalLawsPromoted ≡ false
    maxwellFieldEquationsPromoted : Bool
    maxwellFieldEquationsPromotedProof :
      maxwellFieldEquationsPromoted ≡ false
    grFieldEquationsPromoted : Bool
    grFieldEquationsPromotedProof : grFieldEquationsPromoted ≡ false
    terminalClassicalFieldPromotion : Bool
    terminalClassicalFieldPromotionProof :
      terminalClassicalFieldPromotion ≡ false

open ClassicalFieldPromotionObligationIndex public

canonicalClassicalFieldPromotionObligationIndex :
  ClassicalFieldPromotionObligationIndex
canonicalClassicalFieldPromotionObligationIndex = record
  { indexLabel =
      "classical-field-promotion-obligation-index"
  ; indexSourceRegistry = repoWideConstantsRegistry
  ; consumedPopulationReceipt =
      canonicalKnownInputsPopulationReceipt
  ; consumedPhysicsAdapterReceipt =
      canonicalPhysicsAdapterKnownInputsReferenceReceipt
  ; lawObligations = canonicalClassicalPromotionObligations
  ; maxwellObligations = canonicalMaxwellPromotionObligations
  ; grObligations = canonicalGRPromotionObligations
  ; promotionStages =
      carrierNamed
      ∷ unitsBound
      ∷ boundaryConditionsBound
      ∷ observableMapBound
      ∷ adapterReceiptRequired
      ∷ proofOrAuthorityTokenRequired
      ∷ promotionGuardStillClosed
      ∷ []
  ; globalValidationCommands =
      "agda -i . DASHI/Promotion/ClassicalFieldObligations.agda"
      ∷ "agda -i . DASHI/Constants/Registry.agda"
      ∷ []
  ; physicalLawsPromoted = false
  ; physicalLawsPromotedProof = refl
  ; maxwellFieldEquationsPromoted = false
  ; maxwellFieldEquationsPromotedProof = refl
  ; grFieldEquationsPromoted = false
  ; grFieldEquationsPromotedProof = refl
  ; terminalClassicalFieldPromotion = false
  ; terminalClassicalFieldPromotionProof = refl
  }

canonicalClassicalLawObligationCountIs1 :
  listLength
    (ClassicalFieldPromotionObligationIndex.lawObligations
      canonicalClassicalFieldPromotionObligationIndex)
  ≡ suc zero
canonicalClassicalLawObligationCountIs1 = refl

canonicalMaxwellObligationCountIs1 :
  listLength
    (ClassicalFieldPromotionObligationIndex.maxwellObligations
      canonicalClassicalFieldPromotionObligationIndex)
  ≡ suc zero
canonicalMaxwellObligationCountIs1 = refl

canonicalGRObligationCountIs1 :
  listLength
    (ClassicalFieldPromotionObligationIndex.grObligations
      canonicalClassicalFieldPromotionObligationIndex)
  ≡ suc zero
canonicalGRObligationCountIs1 = refl

canonicalPromotionStageCountIs7 :
  listLength
    (ClassicalFieldPromotionObligationIndex.promotionStages
      canonicalClassicalFieldPromotionObligationIndex)
  ≡ suc (suc (suc (suc (suc (suc (suc zero))))))
canonicalPromotionStageCountIs7 = refl

classicalFieldIndexKeepsPhysicalLawsFalse :
  ClassicalFieldPromotionObligationIndex.physicalLawsPromoted
    canonicalClassicalFieldPromotionObligationIndex
  ≡ false
classicalFieldIndexKeepsPhysicalLawsFalse = refl

classicalFieldIndexKeepsMaxwellFalse :
  ClassicalFieldPromotionObligationIndex.maxwellFieldEquationsPromoted
    canonicalClassicalFieldPromotionObligationIndex
  ≡ false
classicalFieldIndexKeepsMaxwellFalse = refl

classicalFieldIndexKeepsGRFalse :
  ClassicalFieldPromotionObligationIndex.grFieldEquationsPromoted
    canonicalClassicalFieldPromotionObligationIndex
  ≡ false
classicalFieldIndexKeepsGRFalse = refl

classicalFieldIndexKeepsTerminalFalse :
  ClassicalFieldPromotionObligationIndex.terminalClassicalFieldPromotion
    canonicalClassicalFieldPromotionObligationIndex
  ≡ false
classicalFieldIndexKeepsTerminalFalse = refl
