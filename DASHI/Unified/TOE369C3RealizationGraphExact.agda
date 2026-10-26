module DASHI.Unified.TOE369C3RealizationGraphExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFHyperfabric369 as Hyperfabric
open import DASHI.Unified.TOESectorRealizationExact

data C3Node : Set where
  universal369Phase : C3Node
  spatialXYZC3 : C3Node
  su2CartanU1Orientation : C3Node
  eisensteinOmega : C3Node
  monsterCentralPhase : C3Node
  nh3ElectronicC3 : C3Node
  matbgThreeHarmonicC3 : C3Node
  iitF3TernaryOrientation : C3Node
  oggMod3FourierPhase : C3Node

requiredC3Nodes : List C3Node
requiredC3Nodes =
  universal369Phase
  ∷ spatialXYZC3
  ∷ su2CartanU1Orientation
  ∷ eisensteinOmega
  ∷ monsterCentralPhase
  ∷ nh3ElectronicC3
  ∷ matbgThreeHarmonicC3
  ∷ iitF3TernaryOrientation
  ∷ oggMod3FourierPhase
  ∷ []

canonicalC3Nodes : List C3Node
canonicalC3Nodes = requiredC3Nodes

universal369Surface : Hyperfabric.PNFHyperfabric369Surface
universal369Surface = Hyperfabric.canonicalPNFHyperfabric369Surface

record C3Edge : Set where
  field
    source : C3Node
    target : C3Node
    kind : RealizationKind
    grade : ValidationGrade
    unpaid : List RealizationObligation
    sourceReceipt : String
    physicalPromotion : Bool
    physicalPromotionIsFalse : physicalPromotion ≡ false

open C3Edge public

edge : C3Node → C3Node → RealizationKind → ValidationGrade →
  List RealizationObligation → String → C3Edge
edge source target kind grade unpaid receipt =
  record
    { source = source
    ; target = target
    ; kind = kind
    ; grade = grade
    ; unpaid = unpaid
    ; sourceReceipt = receipt
    ; physicalPromotion = false
    ; physicalPromotionIsFalse = refl
    }

nh3MonsterRepresentation : C3Edge
nh3MonsterRepresentation =
  edge nh3ElectronicC3 monsterCentralPhase equivalenceIsomorphism
    representationIntertwiner
    (dynamicsEquivariance ∷ actionHamiltonianAgreement ∷ empiricalSameObjectAttachment ∷ [])
    "Agda PR #1162 records the exact two-sided NH3 electronic phase <-> selected Monster 3B central phase C3 representation isomorphism. This edge imports that scope only; physical Monster action on NH3 remains unpaid."

eisensteinUniversalCharacter : C3Edge
eisensteinUniversalCharacter =
  edge universal369Phase eisensteinOmega representationIntertwinerKind
    representationIntertwiner
    (dynamicsEquivariance ∷ actionHamiltonianAgreement ∷ [])
    "Existing Eisenstein/CM owners identify the mod-3/omega character action exactly at the arithmetic representation level."

spatialToGaugeCandidate : C3Edge
spatialToGaugeCandidate =
  edge spatialXYZC3 su2CartanU1Orientation representationIntertwinerKind
    representationIntertwiner
    (dynamicsEquivariance ∷ actionHamiltonianAgreement ∷ stressObservableAgreement ∷ [])
    "Current torque/Hodge/right-hand-rule work pays the oriented three-axis and SU2/U1 representation layer; common dynamics/action/stress remains the TOE test."

universalToSpatialCandidate : C3Edge
universalToSpatialCandidate =
  edge universal369Phase spatialXYZC3 conjecturalPhysicalRealization sharedCarrier
    (representationActionAgreement ∷ dynamicsEquivariance ∷ actionHamiltonianAgreement ∷ empiricalSameObjectAttachment ∷ [])
    "HAM candidate: the 369 orientation and physical spatial C3 are two realizations of one universal orientation action."

universalToMonsterCandidate : C3Edge
universalToMonsterCandidate =
  edge universal369Phase monsterCentralPhase conjecturalPhysicalRealization sharedCarrier
    (representationActionAgreement ∷ dynamicsEquivariance ∷ actionHamiltonianAgreement ∷ empiricalSameObjectAttachment ∷ [])
    "HAM candidate: the selected Monster central phase is a representation of the same universal C3 orientation carried by the 369 substrate."

universalToMATBGCandidate : C3Edge
universalToMATBGCandidate =
  edge universal369Phase matbgThreeHarmonicC3 conjecturalPhysicalRealization sharedCarrier
    (representationActionAgreement ∷ dynamicsEquivariance ∷ actionHamiltonianAgreement ∷ empiricalSameObjectAttachment ∷ [])
    "HAM candidate: MATBG three-harmonic C3 is a material Hamiltonian realization of universal orientation."

universalToIITCandidate : C3Edge
universalToIITCandidate =
  edge universal369Phase iitF3TernaryOrientation quotientFactor sharedCarrier
    (representationActionAgreement ∷ dynamicsEquivariance ∷ [])
    "The ternary observer lane preserves orientation information unavailable to binary collapse; physical identification is not inferred."

universalToOggObserver : C3Edge
universalToOggObserver =
  edge universal369Phase oggMod3FourierPhase quotientFactor sharedCarrier
    (representationActionAgreement ∷ nonDescentWitness ∷ [])
    "Ogg/mod-3 Fourier structure is treated as an observer/factor of the universal phase language; phase statistics alone do not identify the fine state."

characterDoesNotForceSameAction : C3Edge
characterDoesNotForceSameAction =
  edge monsterCentralPhase eisensteinOmega sharedCharacterOnly sharedCarrier
    (representationActionAgreement ∷ dynamicsEquivariance ∷ actionHamiltonianAgreement ∷ nonDescentWitness ∷ [])
    "Equal C3 character data is explicitly non-descent for full action identity."

basisCountDoesNotForcePhysicalIdentity : C3Edge
basisCountDoesNotForcePhysicalIdentity =
  edge universal369Phase monsterCentralPhase refutedNonDescent conjecturalStructural
    (nonDescentWitness ∷ empiricalSameObjectAttachment ∷ [])
    "Cardinality identities such as 729*90=65610 are not maps between full linear state spaces and cannot promote a physical Monster realization."

canonicalC3Edges : List C3Edge
canonicalC3Edges =
  nh3MonsterRepresentation
  ∷ eisensteinUniversalCharacter
  ∷ spatialToGaugeCandidate
  ∷ universalToSpatialCandidate
  ∷ universalToMonsterCandidate
  ∷ universalToMATBGCandidate
  ∷ universalToIITCandidate
  ∷ universalToOggObserver
  ∷ characterDoesNotForceSameAction
  ∷ basisCountDoesNotForcePhysicalIdentity
  ∷ []
