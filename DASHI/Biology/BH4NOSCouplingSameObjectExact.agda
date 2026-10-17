module DASHI.Biology.BH4NOSCouplingSameObjectExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4CompartmentKineticStateExact as Parameters
import DASHI.Biology.NitrogenOxideSpeciesCouplingExact as NOS
import DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact as Graph
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Same-object bridge from the quantitative BH4 state into NOS coupling.
--
-- The bridge is deliberately payment-oriented.  Protein identity and BH4
-- dependence are prerequisites, but a promoted coupling transition additionally
-- requires same-object/same-compartment BH4/BH2, redox, substrate, product and
-- interventional transition coordinates.
------------------------------------------------------------------------

record BH4NOSSameObjectPayment : Set where
  constructor bh4-nos-same-object-payment
  field
    isoformReference : String
    quantitativeStateReference : String
    sameObjectReference : String
    compartmentReference : String
    bh4Bh2StatePaid : Bool
    redoxStatePaid : Bool
    substrateStatePaid : Bool
    oxygenStatePaid : Bool
    couplingTransitionPaid : Bool
    nitricOxideProductPaid : Bool
    superoxideProductPaid : Bool
    downstreamTSC2SameObjectTransportPaid : Bool
    transitionEvidenceReference : String
    residualReference : String

open BH4NOSSameObjectPayment public

unresolvedNOS1Payment : BH4NOSSameObjectPayment
unresolvedNOS1Payment =
  bh4-nos-same-object-payment
    "NOS1/P29475"
    "BH4 quantitative parameter manifest"
    "same-object NOS1 experiment not yet admitted"
    "compartment not yet paid"
    false false false false false false false false
    "no interventional NOS1 coupling transition receipt admitted yet"
    "requires same-compartment BH4/BH2 + redox + substrate/oxygen + product measurement + perturbation transition"

unresolvedNOS2Payment : BH4NOSSameObjectPayment
unresolvedNOS2Payment =
  bh4-nos-same-object-payment
    "NOS2/P35228"
    "BH4 quantitative parameter manifest"
    "same-object NOS2 experiment not yet admitted"
    "compartment not yet paid"
    false false false false false false false false
    "no interventional NOS2 coupling transition receipt admitted yet"
    "requires same-compartment BH4/BH2 + redox + substrate/oxygen + product measurement + perturbation transition"

unresolvedNOS3Payment : BH4NOSSameObjectPayment
unresolvedNOS3Payment =
  bh4-nos-same-object-payment
    "NOS3/P29474"
    "BH4 quantitative parameter manifest"
    "same-object NOS3 experiment not yet admitted"
    "compartment not yet paid"
    false false false false false false false false
    "no interventional NOS3 coupling transition receipt admitted yet"
    "requires same-compartment BH4/BH2 + redox + substrate/oxygen + product measurement + perturbation transition"

nosCouplingStateTypeAvailable : Set
nosCouplingStateTypeAvailable = NOS.NOSCouplingState

nitricOxideProduct : NOS.NitrogenOxideSpecies
nitricOxideProduct = NOS.nitricOxide

nitrousOxideAlternativeSpecies : NOS.NitrogenOxideSpecies
nitrousOxideAlternativeSpecies = NOS.nitrousOxide

nitricOxideStillNotNitrousOxide :
  nitricOxideProduct ≡ nitrousOxideAlternativeSpecies → ⊥
nitricOxideStillNotNitrousOxide = NOS.nitricOxideNotNitrousOxide

upstreamToTSC2GraphEdge : Graph.MechanisticEdgePayment
upstreamToTSC2GraphEdge = Graph.nosToTSC2Edge

record BH4NOSSameObjectBoundary : Set where
  constructor bh4-nos-same-object-boundary
  field
    proteinPresencePaysCouplingTransition : Bool
    proteinPresencePaysCouplingTransitionIsFalse :
      proteinPresencePaysCouplingTransition ≡ false
    bh4CofactorRequirementPaysCouplingTransition : Bool
    bh4CofactorRequirementPaysCouplingTransitionIsFalse :
      bh4CofactorRequirementPaysCouplingTransition ≡ false
    nitrousOxideMayStandForNitricOxideProduct : Bool
    nitrousOxideMayStandForNitricOxideProductIsFalse :
      nitrousOxideMayStandForNitricOxideProduct ≡ false
    oneIsoformTransitionPaysAllIsoforms : Bool
    oneIsoformTransitionPaysAllIsoformsIsFalse :
      oneIsoformTransitionPaysAllIsoforms ≡ false
    downstreamRelationEvidencePaysUpstreamSameObjectTransport : Bool
    downstreamRelationEvidencePaysUpstreamSameObjectTransportIsFalse :
      downstreamRelationEvidencePaysUpstreamSameObjectTransport ≡ false
    literatureParameterWithoutSameObjectCoordinatePaysTransition : Bool
    literatureParameterWithoutSameObjectCoordinatePaysTransitionIsFalse :
      literatureParameterWithoutSameObjectCoordinatePaysTransition ≡ false

open BH4NOSSameObjectBoundary public

canonicalBH4NOSSameObjectBoundary : BH4NOSSameObjectBoundary
canonicalBH4NOSSameObjectBoundary =
  bh4-nos-same-object-boundary false refl false refl false refl false refl false refl false refl

canonicalBH4NOSSameObjectReceipt : Receipt.GenericReceipt
canonicalBH4NOSSameObjectReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 -> NOS same-object coupling bridge"
    "DASHI.Biology.BH4NOSCouplingSameObjectExact"
    "same-object/same-compartment BH4/BH2 + redox + substrate + oxygen -> isoform-specific NOS coupling transition -> measured NO/superoxide product -> downstream TSC2 transport"
    "makes every prerequisite/payment coordinate explicit for NOS1/NOS2/NOS3 and reuses the existing NO != N2O theorem and downstream graph edge"
    "protein presence, BH4 dependence, generic literature bounds or downstream relation evidence do not pay a coupling transition or upstream-to-TSC2 same-object transport"
    "agda -i . DASHI/Biology/BH4NOSCouplingSameObjectExact.agda"
