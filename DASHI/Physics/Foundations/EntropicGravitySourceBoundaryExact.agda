{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.EntropicGravitySourceBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE / AUTHORITY BOUNDARY FOR THERMODYNAMIC AND ENTROPIC GRAVITY
--
-- Sources are kept distinct by claim type.  In particular:
--   * Bekenstein: black-hole entropy / area-information thermodynamics;
--   * Jacobson: Einstein equation as an equation of state from local-horizon
--     thermodynamic assumptions;
--   * Verlinde: heuristic entropic-force / emergent-space proposal.
--
-- None of these receipts is promoted here to a repository proof that generic
-- entropy density or residual information density is a gravitational source.
------------------------------------------------------------------------

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    author : String
    title : String
    venue : String
    year : String
    doi : String

bekenstein1973 : SourceReceipt
bekenstein1973 =
  sourceReceipt
    "Jacob D. Bekenstein"
    "Black Holes and Entropy"
    "Physical Review D 7, 2333"
    "1973"
    "10.1103/PhysRevD.7.2333"

jacobson1995 : SourceReceipt
jacobson1995 =
  sourceReceipt
    "Ted Jacobson"
    "Thermodynamics of Spacetime: The Einstein Equation of State"
    "Physical Review Letters 75, 1260"
    "1995"
    "10.1103/PhysRevLett.75.1260"

verlinde2011 : SourceReceipt
verlinde2011 =
  sourceReceipt
    "Erik P. Verlinde"
    "On the Origin of Gravity and the Laws of Newton"
    "Journal of High Energy Physics 2011, 29"
    "2011"
    "10.1007/JHEP04(2011)029"

record EntropicGravityClaimBoundary : Set where
  constructor entropicGravityClaimBoundary
  field
    bekensteinHawkingAreaEntropyIsSemiclassicalInput : Bool
    bekensteinAreaEntropyAloneDerivesEinsteinEquation : Bool

    jacobsonDerivesEinsteinEquationFromLocalHorizonThermodynamicAssumptions : Bool
    jacobsonUsesHeatEntropyTemperatureRelation : Bool
    jacobsonUsesLocalRindlerHorizonStructure : Bool
    jacobsonResultMakesGenericEntropyDensityAStressTensor : Bool

    verlindeEntropicGravityIsHeuristicEmergentGravityProposal : Bool
    verlindeUsesHolographicInformationScreenPicture : Bool
    verlindeIdentifiesGravityWithEntropicForceInThatProposal : Bool
    verlindeProposalIsEstablishedQuantumGravityTheory : Bool

    entropyDensityAloneImpliesEinsteinEquation : Bool
    residualInformationDensityAloneImpliesCurvature : Bool
    entropicGravityEliminatesDarkMatterEmpirically : Bool

canonicalEntropicGravityClaimBoundary : EntropicGravityClaimBoundary
canonicalEntropicGravityClaimBoundary =
  entropicGravityClaimBoundary
    true
    false
    true
    true
    true
    false
    true
    true
    true
    false
    false
    false
    false

record EntropicGravityPromotionFirewall : Set where
  constructor entropicGravityPromotionFirewall
  field
    blackHoleThermodynamicsIsNotEntropicGravityByDefinition : Bool
    jacobsonEquationOfStateDerivationIsNotVerlindeScreenModel : Bool
    proposedEntropicForceIsNotEmpiricalReplacementForGR : Bool
    darkMatterAlternativeNeedsIndependentPhenomenology : Bool
    informationGeometryNeedsPhysicalStressCurvatureBridge : Bool
    interpretation : String

canonicalEntropicGravityPromotionFirewall : EntropicGravityPromotionFirewall
canonicalEntropicGravityPromotionFirewall =
  entropicGravityPromotionFirewall
    true
    true
    true
    true
    true
    "Bekenstein black-hole entropy, Jacobson local-horizon thermodynamics, and Verlinde entropic gravity are related but non-identical claims with different evidential and mathematical status."
