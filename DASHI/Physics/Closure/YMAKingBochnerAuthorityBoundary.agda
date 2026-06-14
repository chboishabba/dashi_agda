module DASHI.Physics.Closure.YMAKingBochnerAuthorityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

------------------------------------------------------------------------
-- YM-A King/Bochner authority boundary.
--
-- This module separates external authority input from local algebraic input.
-- King 1986 is recorded only as an authority string for a spectral-gap lower
-- bound formula.  The Bochner/Casimir adjoint constants below are local
-- algebraic rows for SU(2) and SU(3).  Neither input is transported to the
-- DASHI domain theorem here, and no YM-A or Clay Yang-Mills theorem is
-- promoted by this boundary.

kingAuthorityInputRecorded : Bool
kingAuthorityInputRecorded = true

bochnerCasimirInputRecorded : Bool
bochnerCasimirInputRecorded = true

kingBoundTransportedToDashiDomain : Bool
kingBoundTransportedToDashiDomain = false

bochnerWeitzenbockProofInternalized : Bool
bochnerWeitzenbockProofInternalized = false

ymATheoremPromoted : Bool
ymATheoremPromoted = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

kingAuthorityInputRecordedIsTrue :
  kingAuthorityInputRecorded ≡ true
kingAuthorityInputRecordedIsTrue = refl

bochnerCasimirInputRecordedIsTrue :
  bochnerCasimirInputRecorded ≡ true
bochnerCasimirInputRecordedIsTrue = refl

kingBoundTransportedToDashiDomainIsFalse :
  kingBoundTransportedToDashiDomain ≡ false
kingBoundTransportedToDashiDomainIsFalse = refl

bochnerWeitzenbockProofInternalizedIsFalse :
  bochnerWeitzenbockProofInternalized ≡ false
bochnerWeitzenbockProofInternalizedIsFalse = refl

ymATheoremPromotedIsFalse :
  ymATheoremPromoted ≡ false
ymATheoremPromotedIsFalse = refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

king1986SpectralGapLowerBoundFormula : String
king1986SpectralGapLowerBoundFormula =
  "King 1986 authority input: spectral-gap lower-bound formula recorded as Delta_King(G,beta,L) >= c_King(G,beta,L) > 0 on its source domain."

king1986AuthorityBoundaryStatement : String
king1986AuthorityBoundaryStatement =
  "King 1986 is recorded as external authority text only; this module does not transport that lower bound to the DASHI domain theorem."

bochnerCasimirBoundaryStatement : String
bochnerCasimirBoundaryStatement =
  "Bochner/Casimir adjoint constants are recorded as local algebraic SU(2) and SU(3) rows only; the Bochner-Weitzenbock proof is not internalized here."

data YMACompactGroup : Set where
  SU2 :
    YMACompactGroup
  SU3 :
    YMACompactGroup

record BochnerCasimirAdjointRow : Set where
  constructor mkBochnerCasimirAdjointRow
  field
    group :
      YMACompactGroup
    groupName :
      String
    adjointCasimirConstant :
      Nat
    adjointCasimirFormula :
      String
    algebraicLocalInput :
      Bool
    algebraicLocalInputIsTrue :
      algebraicLocalInput ≡ true

open BochnerCasimirAdjointRow public

su2BochnerCasimirAdjointRow : BochnerCasimirAdjointRow
su2BochnerCasimirAdjointRow =
  mkBochnerCasimirAdjointRow
    SU2
    "SU(2)"
    2
    "C2(ad SU(2)) = 2"
    true
    refl

su3BochnerCasimirAdjointRow : BochnerCasimirAdjointRow
su3BochnerCasimirAdjointRow =
  mkBochnerCasimirAdjointRow
    SU3
    "SU(3)"
    3
    "C2(ad SU(3)) = 3"
    true
    refl

canonicalBochnerCasimirAdjointRows :
  List BochnerCasimirAdjointRow
canonicalBochnerCasimirAdjointRows =
  su2BochnerCasimirAdjointRow
  ∷ su3BochnerCasimirAdjointRow
  ∷ []

record YMAKingBochnerAuthorityBoundary : Set where
  field
    kingFormulaAuthorityText :
      String
    kingFormulaAuthorityTextIsCanonical :
      kingFormulaAuthorityText ≡ king1986SpectralGapLowerBoundFormula

    bochnerCasimirRows :
      List BochnerCasimirAdjointRow
    bochnerCasimirRowsAreCanonical :
      bochnerCasimirRows ≡ canonicalBochnerCasimirAdjointRows

    kingAuthorityInputRecordedHere :
      kingAuthorityInputRecorded ≡ true
    bochnerCasimirInputRecordedHere :
      bochnerCasimirInputRecorded ≡ true

    kingBoundNotTransportedToDashiDomain :
      kingBoundTransportedToDashiDomain ≡ false
    bochnerWeitzenbockProofNotInternalized :
      bochnerWeitzenbockProofInternalized ≡ false
    ymATheoremNotPromoted :
      ymATheoremPromoted ≡ false
    clayYangMillsNotPromoted :
      clayYangMillsPromoted ≡ false

    kingBoundaryText :
      String
    kingBoundaryTextIsCanonical :
      kingBoundaryText ≡ king1986AuthorityBoundaryStatement

    bochnerBoundaryText :
      String
    bochnerBoundaryTextIsCanonical :
      bochnerBoundaryText ≡ bochnerCasimirBoundaryStatement

open YMAKingBochnerAuthorityBoundary public

canonicalYMAKingBochnerAuthorityBoundary :
  YMAKingBochnerAuthorityBoundary
canonicalYMAKingBochnerAuthorityBoundary =
  record
    { kingFormulaAuthorityText =
        king1986SpectralGapLowerBoundFormula
    ; kingFormulaAuthorityTextIsCanonical =
        refl
    ; bochnerCasimirRows =
        canonicalBochnerCasimirAdjointRows
    ; bochnerCasimirRowsAreCanonical =
        refl
    ; kingAuthorityInputRecordedHere =
        refl
    ; bochnerCasimirInputRecordedHere =
        refl
    ; kingBoundNotTransportedToDashiDomain =
        refl
    ; bochnerWeitzenbockProofNotInternalized =
        refl
    ; ymATheoremNotPromoted =
        refl
    ; clayYangMillsNotPromoted =
        refl
    ; kingBoundaryText =
        king1986AuthorityBoundaryStatement
    ; kingBoundaryTextIsCanonical =
        refl
    ; bochnerBoundaryText =
        bochnerCasimirBoundaryStatement
    ; bochnerBoundaryTextIsCanonical =
        refl
    }
