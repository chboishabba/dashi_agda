module DASHI.Physics.Closure.YMAHolonomyWilsonLocalArithmetic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Local arithmetic boundary for the q = 0.23178 Wilson/holonomy row.
--
-- Agda builtins provide neither real logarithms nor real exponentials here.
-- This receipt therefore records the sourced decimal and logarithmic values
-- as authority-input rational rows.  The reading q = exp(-S_W / N) is a
-- convention accepted as input, not a theorem proved by this receipt.

record AuthorityRationalRow : Set where
  constructor mkAuthorityRationalRow
  field
    label :
      String

    numerator :
      Nat

    denominator :
      Nat

    authorityInput :
      Bool

    authorityInputIsTrue :
      authorityInput ≡ true

open AuthorityRationalRow public

qApproxNumerator : Nat
qApproxNumerator =
  23178189475262734

qApproxDenominator : Nat
qApproxDenominator =
  100000000000000000

qApprox : AuthorityRationalRow
qApprox =
  mkAuthorityRationalRow
    "qApprox = 23178189475262734 / 100000000000000000"
    qApproxNumerator
    qApproxDenominator
    true
    refl

qApproxNumeratorIsRecorded :
  numerator qApprox ≡ 23178189475262734
qApproxNumeratorIsRecorded =
  refl

qApproxDenominatorIsRecorded :
  denominator qApprox ≡ 100000000000000000
qApproxDenominatorIsRecorded =
  refl

negLogQApprox : AuthorityRationalRow
negLogQApprox =
  mkAuthorityRationalRow
    "negLogQApprox = 1462 / 1000"
    1462
    1000
    true
    refl

negLogQApproxNumeratorIs1462 :
  numerator negLogQApprox ≡ 1462
negLogQApproxNumeratorIs1462 =
  refl

negLogQApproxDenominatorIs1000 :
  denominator negLogQApprox ≡ 1000
negLogQApproxDenominatorIs1000 =
  refl

SWminOverN : AuthorityRationalRow
SWminOverN =
  negLogQApprox

SWminOverNIsNegLogQApprox :
  SWminOverN ≡ negLogQApprox
SWminOverNIsNegLogQApprox =
  refl

data GaugeGroup : Set where
  SU2 :
    GaugeGroup

  SU3 :
    GaugeGroup

c2SU2 : AuthorityRationalRow
c2SU2 =
  mkAuthorityRationalRow
    "c2 SU2 = 1462 / 1000"
    1462
    1000
    true
    refl

c2SU3 : AuthorityRationalRow
c2SU3 =
  mkAuthorityRationalRow
    "c2 SU3 = 1462 / 1000"
    1462
    1000
    true
    refl

c2 : GaugeGroup → AuthorityRationalRow
c2 SU2 =
  c2SU2
c2 SU3 =
  c2SU3

c2SU2NumeratorIs1462 :
  numerator c2SU2 ≡ 1462
c2SU2NumeratorIs1462 =
  refl

c2SU3NumeratorIs1462 :
  numerator c2SU3 ≡ 1462
c2SU3NumeratorIs1462 =
  refl

c2SU2DenominatorIs1000 :
  denominator c2SU2 ≡ 1000
c2SU2DenominatorIs1000 =
  refl

c2SU3DenominatorIs1000 :
  denominator c2SU3 ≡ 1000
c2SU3DenominatorIs1000 =
  refl

SWminSU2 : AuthorityRationalRow
SWminSU2 =
  mkAuthorityRationalRow
    "SWmin SU2 = 2924 / 1000"
    2924
    1000
    true
    refl

SWminSU3 : AuthorityRationalRow
SWminSU3 =
  mkAuthorityRationalRow
    "SWmin SU3 = 4386 / 1000"
    4386
    1000
    true
    refl

SWmin : GaugeGroup → AuthorityRationalRow
SWmin SU2 =
  SWminSU2
SWmin SU3 =
  SWminSU3

SWminSU2NumeratorIs2924 :
  numerator SWminSU2 ≡ 2924
SWminSU2NumeratorIs2924 =
  refl

SWminSU3NumeratorIs4386 :
  numerator SWminSU3 ≡ 4386
SWminSU3NumeratorIs4386 =
  refl

SWminSU2DenominatorIs1000 :
  denominator SWminSU2 ≡ 1000
SWminSU2DenominatorIs1000 =
  refl

SWminSU3DenominatorIs1000 :
  denominator SWminSU3 ≡ 1000
SWminSU3DenominatorIs1000 =
  refl

qInterpretationBoundaryStatement : String
qInterpretationBoundaryStatement =
  "Boundary: q = exp(-S_W / N) is recorded only as a convention/authority input accepted by this receipt; the receipt proves no logarithm, real exponential, holonomy separation theorem, finite domination theorem, continuum transfer, or Clay Yang-Mills promotion."

SWminOverNAuthorityStatement : String
SWminOverNAuthorityStatement =
  "Authority row: SWmin/N = negLogQApprox = 1462 / 1000. This equality is receipt bookkeeping over supplied rationals, not an analytic logarithm computation."

wilsonArithmeticRecorded : Bool
wilsonArithmeticRecorded =
  true

qInterpretationAcceptedAsInput : Bool
qInterpretationAcceptedAsInput =
  true

holonomySeparationTheoremProved : Bool
holonomySeparationTheoremProved =
  false

finiteDominationTheoremProved : Bool
finiteDominationTheoremProved =
  false

continuumTransferProved : Bool
continuumTransferProved =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

wilsonArithmeticRecordedIsTrue :
  wilsonArithmeticRecorded ≡ true
wilsonArithmeticRecordedIsTrue =
  refl

qInterpretationAcceptedAsInputIsTrue :
  qInterpretationAcceptedAsInput ≡ true
qInterpretationAcceptedAsInputIsTrue =
  refl

holonomySeparationTheoremProvedIsFalse :
  holonomySeparationTheoremProved ≡ false
holonomySeparationTheoremProvedIsFalse =
  refl

finiteDominationTheoremProvedIsFalse :
  finiteDominationTheoremProved ≡ false
finiteDominationTheoremProvedIsFalse =
  refl

continuumTransferProvedIsFalse :
  continuumTransferProved ≡ false
continuumTransferProvedIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

record YMAHolonomyWilsonLocalArithmeticReceipt : Set where
  constructor mkYMAHolonomyWilsonLocalArithmeticReceipt
  field
    qApproxRow :
      AuthorityRationalRow

    qApproxRowIsCanonical :
      qApproxRow ≡ qApprox

    negLogQApproxRow :
      AuthorityRationalRow

    negLogQApproxRowIsCanonical :
      negLogQApproxRow ≡ negLogQApprox

    SWminOverNRow :
      AuthorityRationalRow

    SWminOverNRowIsNegLogQApprox :
      SWminOverNRow ≡ negLogQApprox

    c2SU2Row :
      AuthorityRationalRow

    c2SU2RowIsCanonical :
      c2SU2Row ≡ c2SU2

    c2SU3Row :
      AuthorityRationalRow

    c2SU3RowIsCanonical :
      c2SU3Row ≡ c2SU3

    SWminSU2Row :
      AuthorityRationalRow

    SWminSU2RowIsCanonical :
      SWminSU2Row ≡ SWminSU2

    SWminSU3Row :
      AuthorityRationalRow

    SWminSU3RowIsCanonical :
      SWminSU3Row ≡ SWminSU3

    interpretationBoundary :
      String

    interpretationBoundaryIsCanonical :
      interpretationBoundary ≡ qInterpretationBoundaryStatement

    SWminOverNStatement :
      String

    SWminOverNStatementIsCanonical :
      SWminOverNStatement ≡ SWminOverNAuthorityStatement

    receiptWilsonArithmeticRecorded :
      wilsonArithmeticRecorded ≡ true

    receiptQInterpretationAcceptedAsInput :
      qInterpretationAcceptedAsInput ≡ true

    receiptHolonomySeparationTheoremProved :
      holonomySeparationTheoremProved ≡ false

    receiptFiniteDominationTheoremProved :
      finiteDominationTheoremProved ≡ false

    receiptContinuumTransferProved :
      continuumTransferProved ≡ false

    receiptClayYangMillsPromoted :
      clayYangMillsPromoted ≡ false

open YMAHolonomyWilsonLocalArithmeticReceipt public

canonicalYMAHolonomyWilsonLocalArithmeticReceipt :
  YMAHolonomyWilsonLocalArithmeticReceipt
canonicalYMAHolonomyWilsonLocalArithmeticReceipt =
  mkYMAHolonomyWilsonLocalArithmeticReceipt
    qApprox
    refl
    negLogQApprox
    refl
    SWminOverN
    refl
    c2SU2
    refl
    c2SU3
    refl
    SWminSU2
    refl
    SWminSU3
    refl
    qInterpretationBoundaryStatement
    refl
    SWminOverNAuthorityStatement
    refl
    refl
    refl
    refl
    refl
    refl
    refl

O : String
O =
  "O: local arithmetic boundary for the q = 0.23178 Wilson/holonomy calculation"

R : String
R =
  "R: encode sourced decimal and logarithmic values as rational authority-input rows"

C : String
C =
  "C: Agda builtins lack real logs and exponentials in this no-libraries receipt"

S : String
S =
  "S: qApprox, negLogQApprox, SWminOverN, c2, and SWmin rows are inhabited"

L : String
L =
  "L: q = exp(-S_W / N) is accepted as an input convention, not proved here"

P : String
P =
  "P: promote only the arithmetic recording and input-acceptance flags"

G : String
G =
  "G: holonomy separation, finite domination, continuum transfer, and Clay promotion stay false"

F : String
F =
  "F: fail-closed typed receipt with no real-analysis theorem manufactured"

canonicalYMAHolonomyWilsonLocalArithmeticORCSLPGF : List String
canonicalYMAHolonomyWilsonLocalArithmeticORCSLPGF =
  O
  ∷ R
  ∷ C
  ∷ S
  ∷ L
  ∷ P
  ∷ G
  ∷ F
  ∷ []
