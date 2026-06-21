module DASHI.Foundations.SSPPrimeLane369Signature where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  ; tri-index
  ; HexTruth
  ; hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  ; hex-index
  ; NonaryTruth
  ; non-0
  ; non-1
  ; non-2
  ; non-3
  ; non-4
  ; non-5
  ; non-6
  ; non-7
  ; non-8
  ; nonary-index
  )

open import DASHI.Foundations.Base369Nat using (_%_)
open import DASHI.TrackedPrimes using (mapTrackedPrimes15)
open import MonsterOntos using
  ( SSP
  ; p2
  ; p3
  ; p5
  ; p7
  ; p11
  ; p13
  ; p17
  ; p19
  ; p23
  ; p29
  ; p31
  ; p41
  ; p47
  ; p59
  ; p71
  ; toNat
  )
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

------------------------------------------------------------------------
-- Typed 3/6/9 signature for each tracked SSP prime lane.
--
-- The record keeps the concrete prime together with the exact typed
-- residues mod 3, mod 6, and mod 9.  Each witness is a closed equality
-- against the corresponding Base369 carrier index.

record Prime369Signature : Set where
  constructor mkPrime369Signature
  field
    prime : SSP
    triResidue : TriTruth
    hexResidue : HexTruth
    nonaryResidue : NonaryTruth
    triResidueWitness : toNat prime % 3 ≡ tri-index triResidue
    hexResidueWitness : toNat prime % 6 ≡ hex-index hexResidue
    nonaryResidueWitness : toNat prime % 9 ≡ nonary-index nonaryResidue

open Prime369Signature public

------------------------------------------------------------------------
-- Lane projections.

prime369TriResidue : SSP → TriTruth
prime369TriResidue p2  = tri-high
prime369TriResidue p3  = tri-low
prime369TriResidue p5  = tri-high
prime369TriResidue p7  = tri-mid
prime369TriResidue p11 = tri-high
prime369TriResidue p13 = tri-mid
prime369TriResidue p17 = tri-high
prime369TriResidue p19 = tri-mid
prime369TriResidue p23 = tri-high
prime369TriResidue p29 = tri-high
prime369TriResidue p31 = tri-mid
prime369TriResidue p41 = tri-high
prime369TriResidue p47 = tri-high
prime369TriResidue p59 = tri-high
prime369TriResidue p71 = tri-high

prime369HexResidue : SSP → HexTruth
prime369HexResidue p2  = hex-2
prime369HexResidue p3  = hex-3
prime369HexResidue p5  = hex-5
prime369HexResidue p7  = hex-1
prime369HexResidue p11 = hex-5
prime369HexResidue p13 = hex-1
prime369HexResidue p17 = hex-5
prime369HexResidue p19 = hex-1
prime369HexResidue p23 = hex-5
prime369HexResidue p29 = hex-5
prime369HexResidue p31 = hex-1
prime369HexResidue p41 = hex-5
prime369HexResidue p47 = hex-5
prime369HexResidue p59 = hex-5
prime369HexResidue p71 = hex-5

prime369NonaryResidue : SSP → NonaryTruth
prime369NonaryResidue p2  = non-2
prime369NonaryResidue p3  = non-3
prime369NonaryResidue p5  = non-5
prime369NonaryResidue p7  = non-7
prime369NonaryResidue p11 = non-2
prime369NonaryResidue p13 = non-4
prime369NonaryResidue p17 = non-8
prime369NonaryResidue p19 = non-1
prime369NonaryResidue p23 = non-5
prime369NonaryResidue p29 = non-2
prime369NonaryResidue p31 = non-4
prime369NonaryResidue p41 = non-5
prime369NonaryResidue p47 = non-2
prime369NonaryResidue p59 = non-5
prime369NonaryResidue p71 = non-8

prime369TriResidueWitness :
  (p : SSP) →
  toNat p % 3 ≡ tri-index (prime369TriResidue p)
prime369TriResidueWitness p2  = refl
prime369TriResidueWitness p3  = refl
prime369TriResidueWitness p5  = refl
prime369TriResidueWitness p7  = refl
prime369TriResidueWitness p11 = refl
prime369TriResidueWitness p13 = refl
prime369TriResidueWitness p17 = refl
prime369TriResidueWitness p19 = refl
prime369TriResidueWitness p23 = refl
prime369TriResidueWitness p29 = refl
prime369TriResidueWitness p31 = refl
prime369TriResidueWitness p41 = refl
prime369TriResidueWitness p47 = refl
prime369TriResidueWitness p59 = refl
prime369TriResidueWitness p71 = refl

prime369HexResidueWitness :
  (p : SSP) →
  toNat p % 6 ≡ hex-index (prime369HexResidue p)
prime369HexResidueWitness p2  = refl
prime369HexResidueWitness p3  = refl
prime369HexResidueWitness p5  = refl
prime369HexResidueWitness p7  = refl
prime369HexResidueWitness p11 = refl
prime369HexResidueWitness p13 = refl
prime369HexResidueWitness p17 = refl
prime369HexResidueWitness p19 = refl
prime369HexResidueWitness p23 = refl
prime369HexResidueWitness p29 = refl
prime369HexResidueWitness p31 = refl
prime369HexResidueWitness p41 = refl
prime369HexResidueWitness p47 = refl
prime369HexResidueWitness p59 = refl
prime369HexResidueWitness p71 = refl

prime369NonaryResidueWitness :
  (p : SSP) →
  toNat p % 9 ≡ nonary-index (prime369NonaryResidue p)
prime369NonaryResidueWitness p2  = refl
prime369NonaryResidueWitness p3  = refl
prime369NonaryResidueWitness p5  = refl
prime369NonaryResidueWitness p7  = refl
prime369NonaryResidueWitness p11 = refl
prime369NonaryResidueWitness p13 = refl
prime369NonaryResidueWitness p17 = refl
prime369NonaryResidueWitness p19 = refl
prime369NonaryResidueWitness p23 = refl
prime369NonaryResidueWitness p29 = refl
prime369NonaryResidueWitness p31 = refl
prime369NonaryResidueWitness p41 = refl
prime369NonaryResidueWitness p47 = refl
prime369NonaryResidueWitness p59 = refl
prime369NonaryResidueWitness p71 = refl

------------------------------------------------------------------------
-- Signature constructor and tracked-order table.

prime369Signature : SSP → Prime369Signature
prime369Signature p =
  mkPrime369Signature
    p
    (prime369TriResidue p)
    (prime369HexResidue p)
    (prime369NonaryResidue p)
    (prime369TriResidueWitness p)
    (prime369HexResidueWitness p)
    (prime369NonaryResidueWitness p)

prime369SignatureVec15 : Vec15 Prime369Signature
prime369SignatureVec15 = mapTrackedPrimes15 prime369Signature

prime369SignatureList : List Prime369Signature
prime369SignatureList =
  prime369Signature p2
  ∷ prime369Signature p3
  ∷ prime369Signature p5
  ∷ prime369Signature p7
  ∷ prime369Signature p11
  ∷ prime369Signature p13
  ∷ prime369Signature p17
  ∷ prime369Signature p19
  ∷ prime369Signature p23
  ∷ prime369Signature p29
  ∷ prime369Signature p31
  ∷ prime369Signature p41
  ∷ prime369Signature p47
  ∷ prime369Signature p59
  ∷ prime369Signature p71
  ∷ []

------------------------------------------------------------------------
-- Compact lane-fingerprint text surface.

prime369LaneFingerprintText : SSP → String
prime369LaneFingerprintText p2  = "p2 -> (2,2,2)"
prime369LaneFingerprintText p3  = "p3 -> (0,3,3)"
prime369LaneFingerprintText p5  = "p5 -> (2,5,5)"
prime369LaneFingerprintText p7  = "p7 -> (1,1,7)"
prime369LaneFingerprintText p11 = "p11 -> (2,5,2)"
prime369LaneFingerprintText p13 = "p13 -> (1,1,4)"
prime369LaneFingerprintText p17 = "p17 -> (2,5,8)"
prime369LaneFingerprintText p19 = "p19 -> (1,1,1)"
prime369LaneFingerprintText p23 = "p23 -> (2,5,5)"
prime369LaneFingerprintText p29 = "p29 -> (2,5,2)"
prime369LaneFingerprintText p31 = "p31 -> (1,1,4)"
prime369LaneFingerprintText p41 = "p41 -> (2,5,5)"
prime369LaneFingerprintText p47 = "p47 -> (2,5,2)"
prime369LaneFingerprintText p59 = "p59 -> (2,5,5)"
prime369LaneFingerprintText p71 = "p71 -> (2,5,8)"

prime369LaneFingerprintTextVec15 : Vec15 String
prime369LaneFingerprintTextVec15 = mapTrackedPrimes15 prime369LaneFingerprintText

prime369SignatureText : Prime369Signature → String
prime369SignatureText (mkPrime369Signature p _ _ _ _ _ _) =
  prime369LaneFingerprintText p

------------------------------------------------------------------------
-- Explicit examples requested for the tracked lanes.

p7Prime369Signature : Prime369Signature
p7Prime369Signature = prime369Signature p7

p11Prime369Signature : Prime369Signature
p11Prime369Signature = prime369Signature p11

p71Prime369Signature : Prime369Signature
p71Prime369Signature = prime369Signature p71

p7FingerprintText : String
p7FingerprintText = prime369LaneFingerprintText p7

p11FingerprintText : String
p11FingerprintText = prime369LaneFingerprintText p11

p71FingerprintText : String
p71FingerprintText = prime369LaneFingerprintText p71
