module DASHI.Geometry.FlatLorentzianModel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)

import DASHI.Geometry.LorentzianLeviCivitaConditional as Conditional

------------------------------------------------------------------------
-- A finite, concrete 1+3 signature carrier.
--
-- This is a checked flat model, not a derivation of physical spacetime from
-- valuation.  It supplies one exact producer for the conditional interfaces:
-- four named directions, a diagonal 1+3 sign pattern, and a zero Cartesian
-- connection.


data Axis4 : Set where
  timeAxis : Axis4
  xAxis : Axis4
  yAxis : Axis4
  zAxis : Axis4


data MetricSign : Set where
  timelikeSign : MetricSign
  spacelikeSign : MetricSign

signature13 : Axis4 → MetricSign
signature13 timeAxis = timelikeSign
signature13 xAxis = spacelikeSign
signature13 yAxis = spacelikeSign
signature13 zAxis = spacelikeSign

timeIsTimelike : signature13 timeAxis ≡ timelikeSign
timeIsTimelike = refl

xIsSpacelike : signature13 xAxis ≡ spacelikeSign
xIsSpacelike = refl

yIsSpacelike : signature13 yAxis ≡ spacelikeSign
yIsSpacelike = refl

zIsSpacelike : signature13 zAxis ≡ spacelikeSign
zIsSpacelike = refl

timelikeDirectionIsUnique :
  (a : Axis4) → signature13 a ≡ timelikeSign → a ≡ timeAxis
timelikeDirectionIsUnique timeAxis refl = refl
timelikeDirectionIsUnique xAxis ()
timelikeDirectionIsUnique yAxis ()
timelikeDirectionIsUnique zAxis ()

record Signature13Receipt : Set where
  constructor mkSignature13Receipt
  field
    timeReceipt : signature13 timeAxis ≡ timelikeSign
    xReceipt : signature13 xAxis ≡ spacelikeSign
    yReceipt : signature13 yAxis ≡ spacelikeSign
    zReceipt : signature13 zAxis ≡ spacelikeSign
    uniqueTimeReceipt :
      (a : Axis4) → signature13 a ≡ timelikeSign → a ≡ timeAxis

open Signature13Receipt public

flatSignature13Receipt : Signature13Receipt
flatSignature13Receipt =
  mkSignature13Receipt
    timeIsTimelike
    xIsSpacelike
    yIsSpacelike
    zIsSpacelike
    timelikeDirectionIsUnique

------------------------------------------------------------------------
-- Balanced-ternary diagonal metric table.
--
-- tri-low  records the negative/timelike diagonal entry,
-- tri-high records the positive/spacelike diagonal entries,
-- tri-mid  records zero off-diagonal entries.

flatMetricEntry : Axis4 → Axis4 → TriTruth
flatMetricEntry timeAxis timeAxis = tri-low
flatMetricEntry timeAxis xAxis = tri-mid
flatMetricEntry timeAxis yAxis = tri-mid
flatMetricEntry timeAxis zAxis = tri-mid
flatMetricEntry xAxis timeAxis = tri-mid
flatMetricEntry xAxis xAxis = tri-high
flatMetricEntry xAxis yAxis = tri-mid
flatMetricEntry xAxis zAxis = tri-mid
flatMetricEntry yAxis timeAxis = tri-mid
flatMetricEntry yAxis xAxis = tri-mid
flatMetricEntry yAxis yAxis = tri-high
flatMetricEntry yAxis zAxis = tri-mid
flatMetricEntry zAxis timeAxis = tri-mid
flatMetricEntry zAxis xAxis = tri-mid
flatMetricEntry zAxis yAxis = tri-mid
flatMetricEntry zAxis zAxis = tri-high


data NonZeroMetricEntry : TriTruth → Set where
  negativeEntry : NonZeroMetricEntry tri-low
  positiveEntry : NonZeroMetricEntry tri-high

diagonalEntryNonzero :
  (a : Axis4) → NonZeroMetricEntry (flatMetricEntry a a)
diagonalEntryNonzero timeAxis = negativeEntry
diagonalEntryNonzero xAxis = positiveEntry
diagonalEntryNonzero yAxis = positiveEntry
diagonalEntryNonzero zAxis = positiveEntry


data DistinctAxis : Axis4 → Axis4 → Set where
  time-x : DistinctAxis timeAxis xAxis
  time-y : DistinctAxis timeAxis yAxis
  time-z : DistinctAxis timeAxis zAxis
  x-time : DistinctAxis xAxis timeAxis
  x-y : DistinctAxis xAxis yAxis
  x-z : DistinctAxis xAxis zAxis
  y-time : DistinctAxis yAxis timeAxis
  y-x : DistinctAxis yAxis xAxis
  y-z : DistinctAxis yAxis zAxis
  z-time : DistinctAxis zAxis timeAxis
  z-x : DistinctAxis zAxis xAxis
  z-y : DistinctAxis zAxis yAxis

metricOffDiagonalZero :
  ∀ {a b : Axis4} → DistinctAxis a b → flatMetricEntry a b ≡ tri-mid
metricOffDiagonalZero time-x = refl
metricOffDiagonalZero time-y = refl
metricOffDiagonalZero time-z = refl
metricOffDiagonalZero x-time = refl
metricOffDiagonalZero x-y = refl
metricOffDiagonalZero x-z = refl
metricOffDiagonalZero y-time = refl
metricOffDiagonalZero y-x = refl
metricOffDiagonalZero y-z = refl
metricOffDiagonalZero z-time = refl
metricOffDiagonalZero z-x = refl
metricOffDiagonalZero z-y = refl

record FlatLorentzianMetricReceipt : Set where
  constructor mkFlatLorentzianMetricReceipt
  field
    signatureReceipt : Signature13Receipt
    nondegenerateDiagonal :
      (a : Axis4) → NonZeroMetricEntry (flatMetricEntry a a)
    offDiagonalReceipt :
      ∀ {a b : Axis4} → DistinctAxis a b → flatMetricEntry a b ≡ tri-mid
    modelScope : String

open FlatLorentzianMetricReceipt public

flatLorentzianMetricReceipt : FlatLorentzianMetricReceipt
flatLorentzianMetricReceipt =
  mkFlatLorentzianMetricReceipt
    flatSignature13Receipt
    diagonalEntryNonzero
    metricOffDiagonalZero
    "finite flat 1+3 carrier; not a valuation-to-spacetime derivation"

------------------------------------------------------------------------
-- Flat Cartesian connection.

Connection : Set
Connection = Axis4 → Axis4 → Axis4 → TriTruth

flatConnection : Connection
flatConnection _ _ _ = tri-mid

PointwiseZeroConnection : Connection → Set
PointwiseZeroConnection connection =
  (a b c : Axis4) → connection a b c ≡ tri-mid

flatConnectionIsPointwiseZero : PointwiseZeroConnection flatConnection
flatConnectionIsPointwiseZero _ _ _ = refl

TorsionFree : Connection → Set
TorsionFree connection =
  (a b c : Axis4) → connection a b c ≡ connection b a c

flatConnectionTorsionFree : TorsionFree flatConnection
flatConnectionTorsionFree _ _ _ = refl

-- For this constant diagonal metric in the named Cartesian frame, the local
-- compatibility certificate is represented by vanishing connection
-- coefficients.  This is deliberately model-specific.
MetricCompatibleWithFlatMetric : Connection → Set
MetricCompatibleWithFlatMetric = PointwiseZeroConnection

flatConnectionMetricCompatible :
  MetricCompatibleWithFlatMetric flatConnection
flatConnectionMetricCompatible = flatConnectionIsPointwiseZero

PointwiseConnectionEqual : Connection → Connection → Set
PointwiseConnectionEqual left right =
  (a b c : Axis4) → left a b c ≡ right a b c

pointwiseZeroConnectionUnique :
  (connection : Connection) →
  PointwiseZeroConnection connection →
  PointwiseConnectionEqual connection flatConnection
pointwiseZeroConnectionUnique connection zeroReceipt a b c =
  zeroReceipt a b c

record FlatLeviCivitaReceipt : Set where
  constructor mkFlatLeviCivitaReceipt
  field
    torsionReceipt : TorsionFree flatConnection
    metricCompatibilityReceipt :
      MetricCompatibleWithFlatMetric flatConnection
    pointwiseUniquenessReceipt :
      (connection : Connection) →
      PointwiseZeroConnection connection →
      PointwiseConnectionEqual connection flatConnection
    receiptScope : String

open FlatLeviCivitaReceipt public

flatLeviCivitaReceipt : FlatLeviCivitaReceipt
flatLeviCivitaReceipt =
  mkFlatLeviCivitaReceipt
    flatConnectionTorsionFree
    flatConnectionMetricCompatible
    pointwiseZeroConnectionUnique
    "zero Cartesian connection on the finite flat metric carrier"

------------------------------------------------------------------------
-- Adapter back into the conditional ladder.

conditionalLorentzianReceipt :
  Conditional.LorentzianMetricReceipt
    Conditional.canonicalConditionalLorentzianWitness
conditionalLorentzianReceipt =
  Conditional.canonicalConditionalLorentzianReceipt

conditionalLeviCivitaReceipt :
  Conditional.LeviCivitaReceipt
    Conditional.canonicalConditionalLorentzianWitness
    Conditional.canonicalConditionalLorentzianReceipt
    Conditional.canonicalConditionalConnection
conditionalLeviCivitaReceipt =
  Conditional.canonicalConditionalLeviCivitaReceipt
