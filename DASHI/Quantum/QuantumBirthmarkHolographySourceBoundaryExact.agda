{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographySourceBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE / AUTHORITY BOUNDARY FOR THE HOLOGRAPHY CROSS-POLLINATION
--
-- These receipts promote only claims directly supported by the cited source.
-- They do NOT identify DASHI's p-adic/tensor-network models with physical
-- spacetime, do not derive gravity, and do not identify birthmark memory with
-- holographic entanglement entropy.
------------------------------------------------------------------------

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    authors : String
    title : String
    venue : String
    year : String
    identifier : String

ryuTakayanagi2006 : SourceReceipt
ryuTakayanagi2006 =
  sourceReceipt
    "Shinsei Ryu; Tadashi Takayanagi"
    "Holographic Derivation of Entanglement Entropy from AdS/CFT"
    "Physical Review Letters 96, 181602"
    "2006"
    "10.1103/PhysRevLett.96.181602"

gubserKnauteParikhSambergWitaszczyk2017 : SourceReceipt
gubserKnauteParikhSambergWitaszczyk2017 =
  sourceReceipt
    "Steven S. Gubser; Johannes Knaute; Sarthak Parikh; Andreas Samberg; Przemek Witaszczyk"
    "p-Adic AdS/CFT"
    "Communications in Mathematical Physics 352, 1019-1059"
    "2017"
    "10.1007/s00220-016-2813-6 / arXiv:1605.01061"

hungLiMelbyThompson2019 : SourceReceipt
hungLiMelbyThompson2019 =
  sourceReceipt
    "Ling-Yan Hung; Wei Li; Charles M. Melby-Thompson"
    "p-adic CFT is a holographic tensor network"
    "Journal of High Energy Physics 2019, 170"
    "2019"
    "10.1007/JHEP04(2019)170 / arXiv:1902.01411"

marcolli2020 : SourceReceipt
marcolli2020 =
  sourceReceipt
    "Matilde Marcolli"
    "Holographic Codes on Bruhat-Tits buildings and Drinfeld Symmetric Spaces"
    "Pure and Applied Mathematics Quarterly 16(1), 1-33"
    "2020"
    "10.4310/PAMQ.2020.v16.n1.a1 / arXiv:1801.09623"

record HolographySourceClaimBoundary : Set where
  constructor holographySourceClaimBoundary
  field
    ryuTakayanagiMinimalSurfaceEntropyProposalSourceBacked : Bool
    ryuTakayanagiIsGenericNonAdSHolographyTheorem : Bool

    pAdicAdSCFTAnalogueSourceBacked : Bool
    bruhatTitsBulkAndPAdicBoundarySourceBacked : Bool
    pAdicAdSCFTIsPhysicalFourDimensionalSpacetime : Bool

    pAdicCFTTensorNetworkEquivalenceSourceBacked : Bool
    pAdicTensorNetworkReproducesCorrelatorsInItsFramework : Bool
    pAdicTensorNetworkProvesDASHIPhysicalBulkBoundaryDictionary : Bool

    bruhatTitsHolographicCodeConstructionsDiscussed : Bool
    holographicCodeDiscussionProvesBirthmarkErasureCorrection : Bool

    physicalSpacetimeIsPAdic : Bool
    birthmarkIsHolographicEntropy : Bool
    holographicEntropyIsResidualInformationDensityByDefinition : Bool
    holographySourcesDeriveJacobsonOrVerlindeGravityAutomatically : Bool

canonicalHolographySourceClaimBoundary : HolographySourceClaimBoundary
canonicalHolographySourceClaimBoundary =
  holographySourceClaimBoundary
    true false
    true true false
    true true false
    true false
    false false false false

record SourcePromotionFirewall : Set where
  constructor sourcePromotionFirewall
  field
    analogueIsNotOntology : Bool
    tensorNetworkEquivalenceIsFrameworkScoped : Bool
    minimalSurfaceEntropyNeedsAdSCFTDictionary : Bool
    sourceAuthorityDoesNotSupplySameObjectDASHIWeld : Bool
    physicalPromotionRequiresIndependentCarrierIdentification : Bool
    interpretation : String

canonicalSourcePromotionFirewall : SourcePromotionFirewall
canonicalSourcePromotionFirewall =
  sourcePromotionFirewall
    true true true true true
    "The p-adic and tensor-network papers provide genuine source authority for their scoped mathematical/field-theoretic dictionaries. They do not identify DASHI's finite carriers with physical spacetime, birthmark memory, or a gravitational source without an explicit same-object bridge."

pAdicAdSCFTAnalogueSourceBacked : Bool
pAdicAdSCFTAnalogueSourceBacked = true

pAdicCFTTensorNetworkEquivalenceSourceBacked : Bool
pAdicCFTTensorNetworkEquivalenceSourceBacked = true

physicalSpacetimeIsPAdic : Bool
physicalSpacetimeIsPAdic = false

birthmarkIsHolographicEntropy : Bool
birthmarkIsHolographicEntropy = false
