module DASHI.Physics.Closure.UniformProjectionNonlocalityGapFinite where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Finite uniform projection/nonlocality gap receipt.
--
-- This surface unifies the finite NS rank-one projection commutator sample
-- and the YM/Bruhat-Tits p=2 and p=3 finite Hodge-gauge defect samples as a
-- single finite receipt.  It records a positive rational gap only on the
-- included nonzero finite samples.  It does not promote a continuum uniform
-- theorem, semantic unification theorem, Clay Yang-Mills theorem, or Clay
-- Navier-Stokes theorem.

data Domain : Set where
  nsRankOne :
    Domain

  ymBTp2 :
    Domain

  ymBTp3 :
    Domain

canonicalDomains : List Domain
canonicalDomains =
  nsRankOne
  ∷ ymBTp2
  ∷ ymBTp3
  ∷ []

domainCount : Nat
domainCount =
  3

domainName : Domain → String
domainName nsRankOne =
  "nsRankOne"
domainName ymBTp2 =
  "ymBTp2"
domainName ymBTp3 =
  "ymBTp3"

data FiniteNonzeroSample : Domain → Set where
  nsRankOneOffDiagonalLeakage :
    FiniteNonzeroSample nsRankOne

  ymBTp2HodgeDefect :
    FiniteNonzeroSample ymBTp2

  ymBTp3HodgeDefect :
    FiniteNonzeroSample ymBTp3

sampleName : {domain : Domain} → FiniteNonzeroSample domain → String
sampleName nsRankOneOffDiagonalLeakage =
  "nsRankOneOffDiagonalLeakage"
sampleName ymBTp2HodgeDefect =
  "ymBTp2HodgeDefect"
sampleName ymBTp3HodgeDefect =
  "ymBTp3HodgeDefect"

gapNumerator : Domain → Nat
gapNumerator nsRankOne =
  1
gapNumerator ymBTp2 =
  1
gapNumerator ymBTp3 =
  2

gapDenominator : Domain → Nat
gapDenominator nsRankOne =
  2
gapDenominator ymBTp2 =
  4
gapDenominator ymBTp3 =
  9

gapNumeratorPositive : Domain → Bool
gapNumeratorPositive nsRankOne =
  true
gapNumeratorPositive ymBTp2 =
  true
gapNumeratorPositive ymBTp3 =
  true

gapDenominatorPositive : Domain → Bool
gapDenominatorPositive nsRankOne =
  true
gapDenominatorPositive ymBTp2 =
  true
gapDenominatorPositive ymBTp3 =
  true

gapPositiveAwayFromZeroMode : Domain → Bool
gapPositiveAwayFromZeroMode nsRankOne =
  true
gapPositiveAwayFromZeroMode ymBTp2 =
  true
gapPositiveAwayFromZeroMode ymBTp3 =
  true

zeroModeExcluded : Domain → Bool
zeroModeExcluded nsRankOne =
  true
zeroModeExcluded ymBTp2 =
  true
zeroModeExcluded ymBTp3 =
  true

data FiniteGapRole : Set where
  nsProjectionPressureNonlocality :
    FiniteGapRole

  ymBTHodgeGaugeDefectP2 :
    FiniteGapRole

  ymBTHodgeGaugeDefectP3 :
    FiniteGapRole

gapRole : Domain → FiniteGapRole
gapRole nsRankOne =
  nsProjectionPressureNonlocality
gapRole ymBTp2 =
  ymBTHodgeGaugeDefectP2
gapRole ymBTp3 =
  ymBTHodgeGaugeDefectP3

data GapReceiptStatus : Set where
  finiteUniformProjectionNonlocalityGapRecorded :
    GapReceiptStatus

  nonzeroSamplesOnly :
    GapReceiptStatus

  continuumUniformGapNotPromoted :
    GapReceiptStatus

  clayPromotionsHeldFalse :
    GapReceiptStatus

canonicalGapReceiptStatus : List GapReceiptStatus
canonicalGapReceiptStatus =
  finiteUniformProjectionNonlocalityGapRecorded
  ∷ nonzeroSamplesOnly
  ∷ continuumUniformGapNotPromoted
  ∷ clayPromotionsHeldFalse
  ∷ []

finiteUniformProjectionNonlocalityGap : Bool
finiteUniformProjectionNonlocalityGap =
  true

continuumUniformProjectionNonlocalityGap : Bool
continuumUniformProjectionNonlocalityGap =
  false

semanticUnificationPromoted : Bool
semanticUnificationPromoted =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

finiteUniformProjectionNonlocalityGapIsTrue :
  finiteUniformProjectionNonlocalityGap ≡ true
finiteUniformProjectionNonlocalityGapIsTrue =
  refl

continuumUniformProjectionNonlocalityGapIsFalse :
  continuumUniformProjectionNonlocalityGap ≡ false
continuumUniformProjectionNonlocalityGapIsFalse =
  refl

semanticUnificationPromotedIsFalse :
  semanticUnificationPromoted ≡ false
semanticUnificationPromotedIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse =
  refl

nsRankOneGapNumeratorIsOne :
  gapNumerator nsRankOne ≡ 1
nsRankOneGapNumeratorIsOne =
  refl

nsRankOneGapDenominatorIsTwo :
  gapDenominator nsRankOne ≡ 2
nsRankOneGapDenominatorIsTwo =
  refl

ymBTp2GapNumeratorIsOne :
  gapNumerator ymBTp2 ≡ 1
ymBTp2GapNumeratorIsOne =
  refl

ymBTp2GapDenominatorIsFour :
  gapDenominator ymBTp2 ≡ 4
ymBTp2GapDenominatorIsFour =
  refl

ymBTp3GapNumeratorIsTwo :
  gapNumerator ymBTp3 ≡ 2
ymBTp3GapNumeratorIsTwo =
  refl

ymBTp3GapDenominatorIsNine :
  gapDenominator ymBTp3 ≡ 9
ymBTp3GapDenominatorIsNine =
  refl

record UniformGapRow : Set where
  constructor uniformGapRow
  field
    domain :
      Domain
    name :
      String
    role :
      FiniteGapRole
    numerator :
      Nat
    denominator :
      Nat
    numeratorPositive :
      Bool
    numeratorPositiveIsTrue :
      numeratorPositive ≡ true
    denominatorPositive :
      Bool
    denominatorPositiveIsTrue :
      denominatorPositive ≡ true
    zeroModeRemoved :
      Bool
    zeroModeRemovedIsTrue :
      zeroModeRemoved ≡ true
    finiteGapPositive :
      Bool
    finiteGapPositiveIsTrue :
      finiteGapPositive ≡ true

open UniformGapRow public

rowFor : (domain : Domain) → UniformGapRow
rowFor nsRankOne =
  uniformGapRow
    nsRankOne
    (domainName nsRankOne)
    (gapRole nsRankOne)
    (gapNumerator nsRankOne)
    (gapDenominator nsRankOne)
    (gapNumeratorPositive nsRankOne)
    refl
    (gapDenominatorPositive nsRankOne)
    refl
    (zeroModeExcluded nsRankOne)
    refl
    (gapPositiveAwayFromZeroMode nsRankOne)
    refl
rowFor ymBTp2 =
  uniformGapRow
    ymBTp2
    (domainName ymBTp2)
    (gapRole ymBTp2)
    (gapNumerator ymBTp2)
    (gapDenominator ymBTp2)
    (gapNumeratorPositive ymBTp2)
    refl
    (gapDenominatorPositive ymBTp2)
    refl
    (zeroModeExcluded ymBTp2)
    refl
    (gapPositiveAwayFromZeroMode ymBTp2)
    refl
rowFor ymBTp3 =
  uniformGapRow
    ymBTp3
    (domainName ymBTp3)
    (gapRole ymBTp3)
    (gapNumerator ymBTp3)
    (gapDenominator ymBTp3)
    (gapNumeratorPositive ymBTp3)
    refl
    (gapDenominatorPositive ymBTp3)
    refl
    (zeroModeExcluded ymBTp3)
    refl
    (gapPositiveAwayFromZeroMode ymBTp3)
    refl

nsRankOneRow : UniformGapRow
nsRankOneRow =
  rowFor nsRankOne

ymBTp2Row : UniformGapRow
ymBTp2Row =
  rowFor ymBTp2

ymBTp3Row : UniformGapRow
ymBTp3Row =
  rowFor ymBTp3

canonicalUniformGapRows : List UniformGapRow
canonicalUniformGapRows =
  nsRankOneRow
  ∷ ymBTp2Row
  ∷ ymBTp3Row
  ∷ []

O : String
O =
  "O: finite receipt over Domain = nsRankOne | ymBTp2 | ymBTp3."

R : String
R =
  "R: expose rational finite gap numerators and denominators with positivity only away from included zero modes."

C : String
C =
  "C: UniformProjectionNonlocalityGapFinite.agda defines Domain, rows, finite gap values, nonzero samples, and status flags."

S : String
S =
  "S: finiteUniformProjectionNonlocalityGap is true; continuum and promotion gates are false."

L : String
L =
  "L: NS rank-one projection nonlocality and YM/BT p=2,p=3 Hodge defect samples share the finite positive-gap lattice."

P : String
P =
  "P: treat this as a finite analytic receipt, not as a continuum theorem."

G : String
G =
  "G: semantic, Clay Yang-Mills, and Clay Navier-Stokes promotion flags are fail-closed."

F : String
F =
  "F: missing lift is a continuum uniform projection-nonlocality lower bound and downstream Clay authority."

record UniformProjectionNonlocalityGapReceipt : Set where
  constructor uniformProjectionNonlocalityGapReceipt
  field
    domains :
      List Domain
    domainsAreCanonical :
      domains ≡ canonicalDomains
    rows :
      List UniformGapRow
    rowsAreCanonical :
      rows ≡ canonicalUniformGapRows
    status :
      List GapReceiptStatus
    statusIsCanonical :
      status ≡ canonicalGapReceiptStatus
    finiteUniformFlag :
      finiteUniformProjectionNonlocalityGap ≡ true
    continuumUniformFlag :
      continuumUniformProjectionNonlocalityGap ≡ false
    semanticPromotionFlag :
      semanticUnificationPromoted ≡ false
    clayYMFlag :
      clayYangMillsPromoted ≡ false
    clayNSFlag :
      clayNavierStokesPromoted ≡ false
    OReceipt :
      String
    OReceiptIsCanonical :
      OReceipt ≡ O
    RReceipt :
      String
    RReceiptIsCanonical :
      RReceipt ≡ R
    CReceipt :
      String
    CReceiptIsCanonical :
      CReceipt ≡ C
    SReceipt :
      String
    SReceiptIsCanonical :
      SReceipt ≡ S
    LReceipt :
      String
    LReceiptIsCanonical :
      LReceipt ≡ L
    PReceipt :
      String
    PReceiptIsCanonical :
      PReceipt ≡ P
    GReceipt :
      String
    GReceiptIsCanonical :
      GReceipt ≡ G
    FReceipt :
      String
    FReceiptIsCanonical :
      FReceipt ≡ F

open UniformProjectionNonlocalityGapReceipt public

canonicalUniformProjectionNonlocalityGapReceipt :
  UniformProjectionNonlocalityGapReceipt
canonicalUniformProjectionNonlocalityGapReceipt =
  uniformProjectionNonlocalityGapReceipt
    canonicalDomains
    refl
    canonicalUniformGapRows
    refl
    canonicalGapReceiptStatus
    refl
    refl
    refl
    refl
    refl
    refl
    O
    refl
    R
    refl
    C
    refl
    S
    refl
    L
    refl
    P
    refl
    G
    refl
    F
    refl
