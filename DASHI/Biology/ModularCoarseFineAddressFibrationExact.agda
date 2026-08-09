module DASHI.Biology.ModularCoarseFineAddressFibrationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Separate address depth from carrier cardinality.  One coarse ternary
-- coordinate and ten fine sector coordinates give eleven address coordinates,
-- while their finite state counts multiply as 3^1 * 3^10 = 3^11.
-- The ten fine sectors are the already constructed T^2 disjoint-union {j}
-- carrier.  Fine data are therefore an indexed field over those ten sectors,
-- not ten additional scalar j-invariants.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

jCoarseAddressDepth : Nat
jCoarseAddressDepth = 1

jFineAddressDepth : Nat
jFineAddressDepth = 10

jAbsoluteAddressDepth : Nat
jAbsoluteAddressDepth = 11

jAbsoluteAddressDepthReconstructs :
  jAbsoluteAddressDepth ≡ jCoarseAddressDepth + jFineAddressDepth
jAbsoluteAddressDepthReconstructs = refl

jCoarseStateCount : Nat
jCoarseStateCount = pow 3 jCoarseAddressDepth

jFineStateCount : Nat
jFineStateCount = pow 3 jFineAddressDepth

jAbsoluteStateCount : Nat
jAbsoluteStateCount = pow 3 jAbsoluteAddressDepth

jCoarseStateCountIsThree : jCoarseStateCount ≡ 3
jCoarseStateCountIsThree = refl

jFineStateCountIsThreePowerTen : jFineStateCount ≡ 59049
jFineStateCountIsThreePowerTen = refl

jAbsoluteStateCountIsThreePowerEleven :
  jAbsoluteStateCount ≡ 177147
jAbsoluteStateCountIsThreePowerEleven = refl

jAbsoluteStateCountFactors :
  jAbsoluteStateCount ≡ jCoarseStateCount * jFineStateCount
jAbsoluteStateCountFactors = refl

CoarseAddress : Set
CoarseAddress = Harmonic.BalancedTrit

FineSector : Set
FineSector = Quotient.DecimalCompletionState

FineAddress : Set
FineAddress = FineSector → Harmonic.BalancedTrit

FineFibre : CoarseAddress → Set
FineFibre coarse = FineAddress

AbsoluteAddress : Set
AbsoluteAddress = Σ CoarseAddress FineFibre

forgetFine : AbsoluteAddress → CoarseAddress
forgetFine absolute = fst absolute

finePart : (absolute : AbsoluteAddress) → FineFibre (forgetFine absolute)
finePart absolute = snd absolute

constantFineAddress : Harmonic.BalancedTrit → FineAddress
constantFineAddress value sector = value

sectionAtFineValue :
  CoarseAddress →
  Harmonic.BalancedTrit →
  AbsoluteAddress
sectionAtFineValue coarse value = coarse , constantFineAddress value

sectionForgetsToBase :
  (coarse : CoarseAddress) →
  (value : Harmonic.BalancedTrit) →
  forgetFine (sectionAtFineValue coarse value) ≡ coarse
sectionForgetsToBase coarse value = refl

ordinaryFineSectorCount : Nat
ordinaryFineSectorCount = 9

completionFineSectorCount : Nat
completionFineSectorCount = 1

fineSectorCount : Nat
fineSectorCount = ordinaryFineSectorCount + completionFineSectorCount

fineSectorCountIsTen : fineSectorCount ≡ 10
fineSectorCountIsTen = refl

completionSector : FineSector
completionSector = Quotient.j9

frickeComplement : FineAddress → FineAddress
frickeComplement assignment sector =
  assignment (Quotient.complementState sector)

frickeComplementPointwiseInvolutive :
  (assignment : FineAddress) →
  (sector : FineSector) →
  frickeComplement (frickeComplement assignment) sector
  ≡ assignment sector
frickeComplementPointwiseInvolutive assignment sector
  rewrite Quotient.complementStateInvolutive sector = refl

SSPLevelFibre : SSP.SSPPrime → CoarseAddress → Set
SSPLevelFibre prime coarse = FineAddress

sspForgetfulTotal : SSP.SSPPrime → Set
sspForgetfulTotal prime = Σ CoarseAddress (SSPLevelFibre prime)

sspForgetfulMap :
  (prime : SSP.SSPPrime) →
  sspForgetfulTotal prime →
  CoarseAddress
sspForgetfulMap prime total = fst total

sspFibreOver :
  (prime : SSP.SSPPrime) →
  CoarseAddress →
  Set
sspFibreOver prime coarse = SSPLevelFibre prime coarse

sspFineSection :
  (prime : SSP.SSPPrime) →
  (coarse : CoarseAddress) →
  (value : Harmonic.BalancedTrit) →
  sspForgetfulTotal prime
sspFineSection prime coarse value = coarse , constantFineAddress value

sspFineSectionForgets :
  (prime : SSP.SSPPrime) →
  (coarse : CoarseAddress) →
  (value : Harmonic.BalancedTrit) →
  sspForgetfulMap prime (sspFineSection prime coarse value) ≡ coarse
sspFineSectionForgets prime coarse value = refl

------------------------------------------------------------------------
-- The finite fibration is an exact internal model.  It does not reconstruct
-- the moduli stack, prove X_0(p)^+ has genus zero, or construct a Hauptmodul.
-- Those external statements remain separate mathematical authority.
------------------------------------------------------------------------

record ModularAddressBoundary : Set where
  constructor modularAddressBoundary
  field
    coarseDepth : Nat
    fineDepth : Nat
    absoluteDepth : Nat
    depthLaw : absoluteDepth ≡ coarseDepth + fineDepth
    stateCountLaw :
      pow 3 absoluteDepth ≡ pow 3 coarseDepth * pow 3 fineDepth
    fineCoordinatesAreTenIndependentJInvariants : Bool
    fineCoordinatesAreTenIndependentJInvariantsIsFalse :
      fineCoordinatesAreTenIndependentJInvariants ≡ false
    finiteAddressFibrationIsLiteralX0p : Bool
    finiteAddressFibrationIsLiteralX0pIsFalse :
      finiteAddressFibrationIsLiteralX0p ≡ false
    genusZeroProvedInternally : Bool
    genusZeroProvedInternallyIsFalse : genusZeroProvedInternally ≡ false
    hauptmodulConstructedInternally : Bool
    hauptmodulConstructedInternallyIsFalse :
      hauptmodulConstructedInternally ≡ false

canonicalModularAddressBoundary : ModularAddressBoundary
canonicalModularAddressBoundary =
  modularAddressBoundary
    jCoarseAddressDepth
    jFineAddressDepth
    jAbsoluteAddressDepth
    jAbsoluteAddressDepthReconstructs
    jAbsoluteStateCountFactors
    false refl
    false refl
    false refl
    false refl
