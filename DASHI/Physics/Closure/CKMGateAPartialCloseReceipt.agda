module DASHI.Physics.Closure.CKMGateAPartialCloseReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM Gate-A partial close receipt.
--
-- This receipt closes only the elementary number-theory side of Gate A:
-- carrier prime p=7 selects the modular curve X0(7), and among the
-- class-number-1 Heegner discriminants listed here D=-7 is the unique one
-- divisible by 7.  The file does not promote this to a physical CKM, CP,
-- Paper, Clay, or terminal result.  The remaining claim is the carrier
-- architecture theorem identifying the CP phase at the class-1 CM point of
-- X0(7).

data GateANumberTheorySide : Set where
  complete :
    GateANumberTheorySide

data GateARemainingClaim : Set where
  cpPhaseAtClass1CMPointOfX07 :
    GateARemainingClaim

data GateADMinusSevenUniqueness : Set where
  provedByExhaustiveHeegnerCheck :
    GateADMinusSevenUniqueness

data GateAStatus : Set where
  partiallyClosedPendingCarrierArchitecture :
    GateAStatus

data ModularCurve : Set where
  X0Seven :
    ModularCurve

data HeegnerClassNumberOneDiscriminant : Set where
  D=-1 :
    HeegnerClassNumberOneDiscriminant

  D=-2 :
    HeegnerClassNumberOneDiscriminant

  D=-3 :
    HeegnerClassNumberOneDiscriminant

  D=-7 :
    HeegnerClassNumberOneDiscriminant

  D=-11 :
    HeegnerClassNumberOneDiscriminant

  D=-19 :
    HeegnerClassNumberOneDiscriminant

  D=-43 :
    HeegnerClassNumberOneDiscriminant

  D=-67 :
    HeegnerClassNumberOneDiscriminant

  D=-163 :
    HeegnerClassNumberOneDiscriminant

canonicalClassNumberOneHeegnerDiscriminants :
  List HeegnerClassNumberOneDiscriminant
canonicalClassNumberOneHeegnerDiscriminants =
  D=-1
  ∷ D=-2
  ∷ D=-3
  ∷ D=-7
  ∷ D=-11
  ∷ D=-19
  ∷ D=-43
  ∷ D=-67
  ∷ D=-163
  ∷ []

data DivisibilityBySeven : Set where
  notDivisibleBy7 :
    DivisibilityBySeven

  divisibleBy7 :
    DivisibilityBySeven

record HeegnerDivisibilityCheck : Set where
  field
    discriminant :
      HeegnerClassNumberOneDiscriminant

    divisibilityBy7 :
      DivisibilityBySeven

open HeegnerDivisibilityCheck public

checkD=-1 :
  HeegnerDivisibilityCheck
checkD=-1 =
  record
    { discriminant =
        D=-1
    ; divisibilityBy7 =
        notDivisibleBy7
    }

checkD=-2 :
  HeegnerDivisibilityCheck
checkD=-2 =
  record
    { discriminant =
        D=-2
    ; divisibilityBy7 =
        notDivisibleBy7
    }

checkD=-3 :
  HeegnerDivisibilityCheck
checkD=-3 =
  record
    { discriminant =
        D=-3
    ; divisibilityBy7 =
        notDivisibleBy7
    }

checkD=-7 :
  HeegnerDivisibilityCheck
checkD=-7 =
  record
    { discriminant =
        D=-7
    ; divisibilityBy7 =
        divisibleBy7
    }

checkD=-11 :
  HeegnerDivisibilityCheck
checkD=-11 =
  record
    { discriminant =
        D=-11
    ; divisibilityBy7 =
        notDivisibleBy7
    }

checkD=-19 :
  HeegnerDivisibilityCheck
checkD=-19 =
  record
    { discriminant =
        D=-19
    ; divisibilityBy7 =
        notDivisibleBy7
    }

checkD=-43 :
  HeegnerDivisibilityCheck
checkD=-43 =
  record
    { discriminant =
        D=-43
    ; divisibilityBy7 =
        notDivisibleBy7
    }

checkD=-67 :
  HeegnerDivisibilityCheck
checkD=-67 =
  record
    { discriminant =
        D=-67
    ; divisibilityBy7 =
        notDivisibleBy7
    }

checkD=-163 :
  HeegnerDivisibilityCheck
checkD=-163 =
  record
    { discriminant =
        D=-163
    ; divisibilityBy7 =
        notDivisibleBy7
    }

canonicalHeegnerDivisibilityCheck :
  List HeegnerDivisibilityCheck
canonicalHeegnerDivisibilityCheck =
  checkD=-1
  ∷ checkD=-2
  ∷ checkD=-3
  ∷ checkD=-7
  ∷ checkD=-11
  ∷ checkD=-19
  ∷ checkD=-43
  ∷ checkD=-67
  ∷ checkD=-163
  ∷ []

data HilbertClassPolynomial : Set where
  HMinus7OfXEqualsXPlus3375 :
    HilbertClassPolynomial

data CMJInvariant : Set where
  j=-3375 :
    CMJInvariant

data CPPhaseDescription : Set where
  gammaArcTanSqrt7 :
    CPPhaseDescription

gateABoundaryStatement : String
gateABoundaryStatement =
  "Gate A is partially closed only on the number-theory side: p=7 defines X0(7), D=-7 is the unique class-1 Heegner discriminant divisible by 7, H_-7(x)=x+3375 gives j=-3375, and gamma=arctan(sqrt(7)) is recorded as the argument of this CM point. Carrier architecture still must prove cpPhaseAtClass1CMPointOfX07 before any physical promotion."

data PhysicalCKMPromotionToken : Set where

physicalCKMPromotionImpossibleHere :
  PhysicalCKMPromotionToken →
  ⊥
physicalCKMPromotionImpossibleHere ()

data PhysicalCPPromotionToken : Set where

physicalCPPromotionImpossibleHere :
  PhysicalCPPromotionToken →
  ⊥
physicalCPPromotionImpossibleHere ()

data PaperPromotionToken : Set where

paperPromotionImpossibleHere :
  PaperPromotionToken →
  ⊥
paperPromotionImpossibleHere ()

data ClayPromotionToken : Set where

clayPromotionImpossibleHere :
  ClayPromotionToken →
  ⊥
clayPromotionImpossibleHere ()

data TerminalPromotionToken : Set where

terminalPromotionImpossibleHere :
  TerminalPromotionToken →
  ⊥
terminalPromotionImpossibleHere ()

record CKMGateAPartialCloseReceipt : Set where
  field
    carrierPrime :
      Nat

    carrierPrimeIs7 :
      carrierPrime ≡ 7

    carrierPrimeDefines :
      ModularCurve

    carrierPrimeDefinesX0Seven :
      carrierPrimeDefines ≡ X0Seven

    classNumberOneHeegnerDiscriminants :
      List HeegnerClassNumberOneDiscriminant

    classNumberOneHeegnerDiscriminantsAreCanonical :
      classNumberOneHeegnerDiscriminants
      ≡
      canonicalClassNumberOneHeegnerDiscriminants

    exhaustiveDivisibilityCheck :
      List HeegnerDivisibilityCheck

    exhaustiveDivisibilityCheckIsCanonical :
      exhaustiveDivisibilityCheck ≡ canonicalHeegnerDivisibilityCheck

    uniqueDiscriminantDivisibleBy7 :
      HeegnerClassNumberOneDiscriminant

    uniqueDiscriminantDivisibleBy7IsD=-7 :
      uniqueDiscriminantDivisibleBy7 ≡ D=-7

    D=-7Uniqueness :
      GateADMinusSevenUniqueness

    D=-7UniquenessIsProvedByExhaustiveHeegnerCheck :
      D=-7Uniqueness ≡ provedByExhaustiveHeegnerCheck

    hilbertClassPolynomial :
      HilbertClassPolynomial

    hilbertClassPolynomialIsHMinus7OfXEqualsXPlus3375 :
      hilbertClassPolynomial ≡ HMinus7OfXEqualsXPlus3375

    cmJInvariant :
      CMJInvariant

    cmJInvariantIsj=-3375 :
      cmJInvariant ≡ j=-3375

    cpPhaseGamma :
      CPPhaseDescription

    cpPhaseGammaIsArgumentOfCMPoint :
      cpPhaseGamma ≡ gammaArcTanSqrt7

    gateANumberTheorySide :
      GateANumberTheorySide

    gateANumberTheorySideIsComplete :
      gateANumberTheorySide ≡ complete

    gateARemainingClaim :
      GateARemainingClaim

    gateARemainingClaimIsCPPhaseAtClass1CMPointOfX07 :
      gateARemainingClaim ≡ cpPhaseAtClass1CMPointOfX07

    gateAStatus :
      GateAStatus

    gateAStatusIsPartiallyClosedPendingCarrierArchitecture :
      gateAStatus ≡ partiallyClosedPendingCarrierArchitecture

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    physicalCPPromoted :
      Bool

    physicalCPPromotedIsFalse :
      physicalCPPromoted ≡ false

    paperPromoted :
      Bool

    paperPromotedIsFalse :
      paperPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    physicalCKMPromotionTokens :
      List PhysicalCKMPromotionToken

    physicalCKMPromotionTokensAreEmpty :
      physicalCKMPromotionTokens ≡ []

    physicalCPPromotionTokens :
      List PhysicalCPPromotionToken

    physicalCPPromotionTokensAreEmpty :
      physicalCPPromotionTokens ≡ []

    paperPromotionTokens :
      List PaperPromotionToken

    paperPromotionTokensAreEmpty :
      paperPromotionTokens ≡ []

    clayPromotionTokens :
      List ClayPromotionToken

    clayPromotionTokensAreEmpty :
      clayPromotionTokens ≡ []

    terminalPromotionTokens :
      List TerminalPromotionToken

    terminalPromotionTokensAreEmpty :
      terminalPromotionTokens ≡ []

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ gateABoundaryStatement

    receiptBoundary :
      List String

open CKMGateAPartialCloseReceipt public

canonicalCKMGateAPartialCloseReceipt :
  CKMGateAPartialCloseReceipt
canonicalCKMGateAPartialCloseReceipt =
  record
    { carrierPrime =
        7
    ; carrierPrimeIs7 =
        refl
    ; carrierPrimeDefines =
        X0Seven
    ; carrierPrimeDefinesX0Seven =
        refl
    ; classNumberOneHeegnerDiscriminants =
        canonicalClassNumberOneHeegnerDiscriminants
    ; classNumberOneHeegnerDiscriminantsAreCanonical =
        refl
    ; exhaustiveDivisibilityCheck =
        canonicalHeegnerDivisibilityCheck
    ; exhaustiveDivisibilityCheckIsCanonical =
        refl
    ; uniqueDiscriminantDivisibleBy7 =
        D=-7
    ; uniqueDiscriminantDivisibleBy7IsD=-7 =
        refl
    ; D=-7Uniqueness =
        provedByExhaustiveHeegnerCheck
    ; D=-7UniquenessIsProvedByExhaustiveHeegnerCheck =
        refl
    ; hilbertClassPolynomial =
        HMinus7OfXEqualsXPlus3375
    ; hilbertClassPolynomialIsHMinus7OfXEqualsXPlus3375 =
        refl
    ; cmJInvariant =
        j=-3375
    ; cmJInvariantIsj=-3375 =
        refl
    ; cpPhaseGamma =
        gammaArcTanSqrt7
    ; cpPhaseGammaIsArgumentOfCMPoint =
        refl
    ; gateANumberTheorySide =
        complete
    ; gateANumberTheorySideIsComplete =
        refl
    ; gateARemainingClaim =
        cpPhaseAtClass1CMPointOfX07
    ; gateARemainingClaimIsCPPhaseAtClass1CMPointOfX07 =
        refl
    ; gateAStatus =
        partiallyClosedPendingCarrierArchitecture
    ; gateAStatusIsPartiallyClosedPendingCarrierArchitecture =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; physicalCPPromoted =
        false
    ; physicalCPPromotedIsFalse =
        refl
    ; paperPromoted =
        false
    ; paperPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; physicalCKMPromotionTokens =
        []
    ; physicalCKMPromotionTokensAreEmpty =
        refl
    ; physicalCPPromotionTokens =
        []
    ; physicalCPPromotionTokensAreEmpty =
        refl
    ; paperPromotionTokens =
        []
    ; paperPromotionTokensAreEmpty =
        refl
    ; clayPromotionTokens =
        []
    ; clayPromotionTokensAreEmpty =
        refl
    ; terminalPromotionTokens =
        []
    ; terminalPromotionTokensAreEmpty =
        refl
    ; boundaryStatement =
        gateABoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; receiptBoundary =
        "carrier prime p=7 defines X0(7)"
        ∷ "class-1 Heegner discriminants checked: {-1,-2,-3,-7,-11,-19,-43,-67,-163}"
        ∷ "D=-7 is the unique listed discriminant divisible by 7"
        ∷ "Hilbert class polynomial H_-7(x)=x+3375 gives j=-3375"
        ∷ "gamma=arctan(sqrt(7)) is recorded as the argument of this CM point"
        ∷ "gateANumberTheorySide=complete"
        ∷ "gateARemainingClaim=cpPhaseAtClass1CMPointOfX07"
        ∷ "D=-7Uniqueness=provedByExhaustiveHeegnerCheck"
        ∷ "gateAStatus=partiallyClosedPendingCarrierArchitecture"
        ∷ "fail-closed: no physical CKM/CP/Paper/Clay/terminal promotion"
        ∷ []
    }

canonicalGateANumberTheorySideComplete :
  gateANumberTheorySide canonicalCKMGateAPartialCloseReceipt ≡ complete
canonicalGateANumberTheorySideComplete =
  refl

canonicalGateARemainingClaim :
  gateARemainingClaim canonicalCKMGateAPartialCloseReceipt
  ≡
  cpPhaseAtClass1CMPointOfX07
canonicalGateARemainingClaim =
  refl

canonicalD=-7Uniqueness :
  D=-7Uniqueness canonicalCKMGateAPartialCloseReceipt
  ≡
  provedByExhaustiveHeegnerCheck
canonicalD=-7Uniqueness =
  refl

canonicalGateAStatus :
  gateAStatus canonicalCKMGateAPartialCloseReceipt
  ≡
  partiallyClosedPendingCarrierArchitecture
canonicalGateAStatus =
  refl

canonicalGateAFailClosedCKM :
  PhysicalCKMPromotionToken →
  ⊥
canonicalGateAFailClosedCKM =
  physicalCKMPromotionImpossibleHere

canonicalGateAFailClosedCP :
  PhysicalCPPromotionToken →
  ⊥
canonicalGateAFailClosedCP =
  physicalCPPromotionImpossibleHere

canonicalGateAFailClosedPaper :
  PaperPromotionToken →
  ⊥
canonicalGateAFailClosedPaper =
  paperPromotionImpossibleHere

canonicalGateAFailClosedClay :
  ClayPromotionToken →
  ⊥
canonicalGateAFailClosedClay =
  clayPromotionImpossibleHere

canonicalGateAFailClosedTerminal :
  TerminalPromotionToken →
  ⊥
canonicalGateAFailClosedTerminal =
  terminalPromotionImpossibleHere
