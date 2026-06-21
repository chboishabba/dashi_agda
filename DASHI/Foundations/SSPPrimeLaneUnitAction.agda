module DASHI.Foundations.SSPPrimeLaneUnitAction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Base369 using
  ( TriTruth
  ; HexTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  ; hex-0
  ; hex-5
  )

open import DASHI.Foundations.Base369Nat using (NonZero; nonZero; _%_)
open import DASHI.Foundations.HexTruthPolarityFactor using
  ( Polarity
  ; flipPolarity
  ; hexFactorToTruth
  ; hexTruthToFactor
  )
open import DASHI.Foundations.SSPPrimeLane369Refinement as Ref using
  ( Lane369Address
  ; Lane369Digit
  ; SSPPrimeLane369Refinement
  ; address
  ; addressDepth
  ; digit-3
  ; digit-6
  ; digit-9
  ; extend
  ; mkSSPPrimeLane369Refinement
  ; root
  ; canonicalThreeSixNineAddress
  )
open import DASHI.Foundations.SSPPrimeLane369Signature as Signature using
  ( Prime369Signature
  ; prime369Signature
  ; hexResidue
  )
open import DASHI.Foundations.SSPPrimeLaneSymmetryProfile as Symmetry using
  ( PrimeLaneSymmetryProfile
  ; primeLaneSymmetryProfile
  ; unitSymmetryOrder
  )
open import DASHI.TrackedPrimes using
  ( SSP
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )

unitSymmetryOrderNonZero : (p : SSP) → NonZero (unitSymmetryOrder p)
unitSymmetryOrderNonZero p2 = nonZero
unitSymmetryOrderNonZero p3 = nonZero
unitSymmetryOrderNonZero p5 = nonZero
unitSymmetryOrderNonZero p7 = nonZero
unitSymmetryOrderNonZero p11 = nonZero
unitSymmetryOrderNonZero p13 = nonZero
unitSymmetryOrderNonZero p17 = nonZero
unitSymmetryOrderNonZero p19 = nonZero
unitSymmetryOrderNonZero p23 = nonZero
unitSymmetryOrderNonZero p29 = nonZero
unitSymmetryOrderNonZero p31 = nonZero
unitSymmetryOrderNonZero p41 = nonZero
unitSymmetryOrderNonZero p47 = nonZero
unitSymmetryOrderNonZero p59 = nonZero
unitSymmetryOrderNonZero p71 = nonZero

UnitActionStep : Set
UnitActionStep = Nat

normalizedUnitStep : SSP → UnitActionStep → Nat
normalizedUnitStep p step =
  _%_ step (unitSymmetryOrder p) {{ unitSymmetryOrderNonZero p }}

triadicActionStep : SSP → UnitActionStep → Nat
triadicActionStep p step = normalizedUnitStep p step % 3

polarityActionStep : SSP → UnitActionStep → Nat
polarityActionStep p step = normalizedUnitStep p step % 2

flipsPolarity : SSP → UnitActionStep → Bool
flipsPolarity p step with polarityActionStep p step
... | zero = false
... | _ = true

rotateTriTruthOnce : TriTruth → TriTruth
rotateTriTruthOnce tri-low = tri-mid
rotateTriTruthOnce tri-mid = tri-high
rotateTriTruthOnce tri-high = tri-low

rotateTriTruthTwice : TriTruth → TriTruth
rotateTriTruthTwice tri-low = tri-high
rotateTriTruthTwice tri-mid = tri-low
rotateTriTruthTwice tri-high = tri-mid

rotateTriTruthBy : Nat → TriTruth → TriTruth
rotateTriTruthBy zero t = t
rotateTriTruthBy (suc zero) t = rotateTriTruthOnce t
rotateTriTruthBy _ t = rotateTriTruthTwice t

rotateLane369DigitOnce : Lane369Digit → Lane369Digit
rotateLane369DigitOnce digit-3 = digit-6
rotateLane369DigitOnce digit-6 = digit-9
rotateLane369DigitOnce digit-9 = digit-3

rotateLane369DigitTwice : Lane369Digit → Lane369Digit
rotateLane369DigitTwice digit-3 = digit-9
rotateLane369DigitTwice digit-6 = digit-3
rotateLane369DigitTwice digit-9 = digit-6

rotateLane369DigitBy : Nat → Lane369Digit → Lane369Digit
rotateLane369DigitBy zero d = d
rotateLane369DigitBy (suc zero) d = rotateLane369DigitOnce d
rotateLane369DigitBy _ d = rotateLane369DigitTwice d

actOnPolarity : SSP → UnitActionStep → Polarity → Polarity
actOnPolarity p step polarity with flipsPolarity p step
... | false = polarity
... | true = flipPolarity polarity

actOnHexTruth : SSP → UnitActionStep → HexTruth → HexTruth
actOnHexTruth p step h =
  hexFactorToTruth
    (rotateTriTruthBy (triadicActionStep p step) tri)
    (actOnPolarity p step polarity)
  where
    tri : TriTruth
    tri = proj₁ (hexTruthToFactor h)

    polarity : Polarity
    polarity = proj₂ (hexTruthToFactor h)

actOnHexFactor :
  SSP → UnitActionStep → HexTruth → TriTruth × Polarity
actOnHexFactor p step h =
  hexTruthToFactor (actOnHexTruth p step h)

actOnAddress :
  ∀ {d : Nat} →
  SSP →
  UnitActionStep →
  Lane369Address d →
  Lane369Address d
actOnAddress p step root = root
actOnAddress p step (extend path digit) =
  extend
    (actOnAddress p step path)
    (rotateLane369DigitBy (triadicActionStep p step) digit)

actOnRefinement :
  ∀ {d : Nat} →
  SSP →
  UnitActionStep →
  SSPPrimeLane369Refinement d →
  SSPPrimeLane369Refinement d
actOnRefinement p step refinement =
  mkSSPPrimeLane369Refinement
    (SSPPrimeLane369Refinement.primeLane refinement)
    (actOnAddress p step (address refinement))

record SSPPrimeLaneUnitActionProfile : Set where
  constructor mkSSPPrimeLaneUnitActionProfile
  field
    primeIdentity : SSP
    symmetryProfile : PrimeLaneSymmetryProfile
    symmetryProfileMatchesPrime :
      PrimeLaneSymmetryProfile.primeIdentity symmetryProfile ≡ primeIdentity
    residueSignature : Prime369Signature
    residueSignatureMatchesPrime :
      Prime369Signature.prime residueSignature ≡ primeIdentity
    rawStep : UnitActionStep
    normalizedStep : Nat
    normalizedStepMatches :
      normalizedStep ≡ normalizedUnitStep primeIdentity rawStep
    triadicStep : Nat
    triadicStepMatches :
      triadicStep ≡ triadicActionStep primeIdentity rawStep
    flipsPolarityBit : Bool
    flipsPolarityBitMatches :
      flipsPolarityBit ≡ flipsPolarity primeIdentity rawStep
    actedHexTruth : HexTruth
    actedHexTruthMatches :
      actedHexTruth ≡
      actOnHexTruth primeIdentity rawStep
        (Signature.hexResidue residueSignature)
    actedHexFactor : TriTruth × Polarity
    actedHexFactorMatches :
      actedHexFactor ≡ hexTruthToFactor actedHexTruth

open SSPPrimeLaneUnitActionProfile public

primeLaneUnitActionProfile :
  SSP →
  UnitActionStep →
  SSPPrimeLaneUnitActionProfile
primeLaneUnitActionProfile p step =
  mkSSPPrimeLaneUnitActionProfile
    p
    (primeLaneSymmetryProfile p)
    refl
    (prime369Signature p)
    refl
    step
    (normalizedUnitStep p step)
    refl
    (triadicActionStep p step)
    refl
    (flipsPolarity p step)
    refl
    (actOnHexTruth p step (Signature.hexResidue (prime369Signature p)))
    refl
    (hexTruthToFactor
      (actOnHexTruth p step (Signature.hexResidue (prime369Signature p))))
    refl

canonicalGeneratorStep : UnitActionStep
canonicalGeneratorStep = suc zero

p7GeneratorUnitActionProfile : SSPPrimeLaneUnitActionProfile
p7GeneratorUnitActionProfile =
  primeLaneUnitActionProfile p7 canonicalGeneratorStep

p11GeneratorUnitActionProfile : SSPPrimeLaneUnitActionProfile
p11GeneratorUnitActionProfile =
  primeLaneUnitActionProfile p11 canonicalGeneratorStep

p7GeneratorNormalizedStepIs1 :
  normalizedStep p7GeneratorUnitActionProfile ≡ 1
p7GeneratorNormalizedStepIs1 = refl

p7GeneratorTriadicStepIs1 :
  triadicStep p7GeneratorUnitActionProfile ≡ 1
p7GeneratorTriadicStepIs1 = refl

p7GeneratorFlipsPolarity :
  flipsPolarityBit p7GeneratorUnitActionProfile ≡ true
p7GeneratorFlipsPolarity = refl

p7GeneratorActsOnHexTruth :
  actedHexTruth p7GeneratorUnitActionProfile ≡ hex-5
p7GeneratorActsOnHexTruth = refl

p11GeneratorNormalizedStepIs1 :
  normalizedStep p11GeneratorUnitActionProfile ≡ 1
p11GeneratorNormalizedStepIs1 = refl

p11GeneratorTriadicStepIs1 :
  triadicStep p11GeneratorUnitActionProfile ≡ 1
p11GeneratorTriadicStepIs1 = refl

p11GeneratorFlipsPolarity :
  flipsPolarityBit p11GeneratorUnitActionProfile ≡ true
p11GeneratorFlipsPolarity = refl

p11GeneratorActsOnHexTruth :
  actedHexTruth p11GeneratorUnitActionProfile ≡ hex-0
p11GeneratorActsOnHexTruth = refl

p7GeneratorActsOnCanonicalThreeSixNine :
  actOnAddress p7 canonicalGeneratorStep canonicalThreeSixNineAddress
  ≡ extend (extend (extend root digit-6) digit-9) digit-3
p7GeneratorActsOnCanonicalThreeSixNine = refl

p11GeneratorActsOnCanonicalThreeSixNine :
  actOnAddress p11 canonicalGeneratorStep canonicalThreeSixNineAddress
  ≡ extend (extend (extend root digit-6) digit-9) digit-3
p11GeneratorActsOnCanonicalThreeSixNine = refl

actionPreservesAddressDepth :
  ∀ {d : Nat} (p : SSP) (step : UnitActionStep) (a : Lane369Address d) →
  addressDepth (actOnAddress p step a) ≡ addressDepth a
actionPreservesAddressDepth p step a = refl
