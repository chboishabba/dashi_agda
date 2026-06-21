module DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_)
open import Ontology.GodelLattice using (Vec15)

open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)

open import DASHI.Foundations.Base369MobiusTransport using
  (positive; negative)
open import DASHI.Foundations.HexTruthPolarityFactor as HexFactor using
  (Polarity; hexTruthToFactor)
open import DASHI.Foundations.SSPPrimeLane369Signature as Signature using
  (Prime369Signature; prime369Signature)
import DASHI.Foundations.SSPPrimeLaneSymmetryProfile as Symmetry
open import DASHI.Foundations.StageAtlasZeroToEleven as StageAtlas using
  ( StageAtlasTopologicalReading
  ; StageAtlasZeroToEleven
  ; atlas-6
  ; atlas-7
  ; atlas-10
  ; atlas-11
  )
open import DASHI.Physics.Closure.CarrierPhaseStructureReceipt using
  (CarrierPhaseStructureReceipt; canonicalCarrierPhaseStructureReceipt)
open import DASHI.TrackedPrimes using (mapTrackedPrimes15; trackedPrimeList)
open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)

record SSPPrimeLane369PhaseBridge : Set where
  constructor mkSSPPrimeLane369PhaseBridge
  field
    primeIdentity : SSP
    residueSignature : Prime369Signature
    residueSignatureMatchesPrimeIdentity :
      Signature.prime residueSignature ≡ primeIdentity
    primeIdentityStage : StageAtlasZeroToEleven
    primeIdentityStageMatches :
      primeIdentityStage ≡ Symmetry.primeIdentityStage primeIdentity
    primeIdentityTopologicalReading : StageAtlasTopologicalReading
    primeIdentityTopologicalReadingMatches :
      primeIdentityTopologicalReading ≡
      Symmetry.primeIdentityReading primeIdentity
    unitOrder : Nat
    unitOrderMatches :
      unitOrder ≡ Symmetry.unitSymmetryOrder primeIdentity
    unitOrderStage : StageAtlasZeroToEleven
    unitOrderStageMatches :
      unitOrderStage ≡ Symmetry.unitSymmetryStage primeIdentity
    unitOrderTopologicalReading : StageAtlasTopologicalReading
    unitOrderTopologicalReadingMatches :
      unitOrderTopologicalReading ≡ Symmetry.unitSymmetryReading primeIdentity
    residueHexFactor : TriTruth × HexFactor.Polarity
    residueHexFactorMatches :
      residueHexFactor ≡
      hexTruthToFactor (Signature.hexResidue residueSignature)
    carrierPhaseReceipt : CarrierPhaseStructureReceipt
    carrierPhaseReceiptMatchesCanonical :
      carrierPhaseReceipt ≡ canonicalCarrierPhaseStructureReceipt
    bridgeBoundary : List String

open SSPPrimeLane369PhaseBridge public

primeLane369PhaseBridge : SSP → SSPPrimeLane369PhaseBridge
primeLane369PhaseBridge p = record
  { primeIdentity = p
  ; residueSignature = residue
  ; residueSignatureMatchesPrimeIdentity = refl
  ; primeIdentityStage = Symmetry.primeIdentityStage p
  ; primeIdentityStageMatches = refl
  ; primeIdentityTopologicalReading = Symmetry.primeIdentityReading p
  ; primeIdentityTopologicalReadingMatches = refl
  ; unitOrder = Symmetry.unitSymmetryOrder p
  ; unitOrderMatches = refl
  ; unitOrderStage = Symmetry.unitSymmetryStage p
  ; unitOrderStageMatches = refl
  ; unitOrderTopologicalReading = Symmetry.unitSymmetryReading p
  ; unitOrderTopologicalReadingMatches = refl
  ; residueHexFactor =
      hexTruthToFactor (Signature.hexResidue residue)
  ; residueHexFactorMatches = refl
  ; carrierPhaseReceipt = canonicalCarrierPhaseStructureReceipt
  ; carrierPhaseReceiptMatchesCanonical = refl
  ; bridgeBoundary =
      "The residue signature, prime-identity stage, and unit-order stage are bridged as a single typed phase profile." ∷
      "The stage coordinates land in StageAtlasZeroToEleven and expose StageAtlasTopologicalReading consumers directly." ∷
      "HexTruthPolarityFactor supplies the residue phase factorization, while CarrierPhaseStructureReceipt remains the canonical carrier-phase seam." ∷
      []
  }
  where
    residue : Prime369Signature
    residue = prime369Signature p

canonicalSSPPrimeLane369PhaseBridgeVec15 : Vec15 SSPPrimeLane369PhaseBridge
canonicalSSPPrimeLane369PhaseBridgeVec15 =
  mapTrackedPrimes15 primeLane369PhaseBridge

canonicalSSPPrimeLane369PrimeList : List SSP
canonicalSSPPrimeLane369PrimeList = trackedPrimeList

p7SSPPrimeLane369PhaseBridge : SSPPrimeLane369PhaseBridge
p7SSPPrimeLane369PhaseBridge = primeLane369PhaseBridge p7

p11SSPPrimeLane369PhaseBridge : SSPPrimeLane369PhaseBridge
p11SSPPrimeLane369PhaseBridge = primeLane369PhaseBridge p11

p7PrimeIdentityStageIsAtlas7 :
  primeIdentityStage p7SSPPrimeLane369PhaseBridge ≡ atlas-7
p7PrimeIdentityStageIsAtlas7 = refl

p7UnitOrderIs6 :
  unitOrder p7SSPPrimeLane369PhaseBridge ≡ 6
p7UnitOrderIs6 = refl

p7UnitOrderStageIsAtlas6 :
  unitOrderStage p7SSPPrimeLane369PhaseBridge ≡ atlas-6
p7UnitOrderStageIsAtlas6 = refl

p7ResidueHexFactorIsMidPositive :
  residueHexFactor p7SSPPrimeLane369PhaseBridge ≡ (tri-mid , positive)
p7ResidueHexFactorIsMidPositive = refl

p7CarrierPhaseReceiptIsCanonical :
  carrierPhaseReceipt p7SSPPrimeLane369PhaseBridge
  ≡ canonicalCarrierPhaseStructureReceipt
p7CarrierPhaseReceiptIsCanonical = refl

p11PrimeIdentityStageIsAtlas11 :
  primeIdentityStage p11SSPPrimeLane369PhaseBridge ≡ atlas-11
p11PrimeIdentityStageIsAtlas11 = refl

p11UnitOrderIs10 :
  unitOrder p11SSPPrimeLane369PhaseBridge ≡ 10
p11UnitOrderIs10 = refl

p11UnitOrderStageIsAtlas10 :
  unitOrderStage p11SSPPrimeLane369PhaseBridge ≡ atlas-10
p11UnitOrderStageIsAtlas10 = refl

p11ResidueHexFactorIsHighNegative :
  residueHexFactor p11SSPPrimeLane369PhaseBridge ≡ (tri-high , negative)
p11ResidueHexFactorIsHighNegative = refl

p11CarrierPhaseReceiptIsCanonical :
  carrierPhaseReceipt p11SSPPrimeLane369PhaseBridge
  ≡ canonicalCarrierPhaseStructureReceipt
p11CarrierPhaseReceiptIsCanonical = refl
