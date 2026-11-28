module DASHI.Cognition.PNF.X369FullNativeE8LeechPriorWeldExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Reuse original full 369 fabric and existing E8/Leech PRIOR owners.
-- An 8D wave coordinate chart is not the E8 ROOT LATTICE, and
-- three E8 ambient blocks are not a constructed Leech lattice.
-- The executable actual chosen Fourier map lives in LeechTransformer
-- scripts/check_x369_full_native_e8_leech_chart.py.
-- Kernel checking deliberately deferred.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_*_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as H
import DASHI.Foundations.Base369NineCoordinateAggregateBridgeExact as Nine
import DASHI.Reasoning.LeechE8PriorStrataBidiExact as E8
import DASHI.Reasoning.Leech369TrialecticWaveLearningArchitectureBidiExact as Lila
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

Native : Set
Native = H.TernaryHyperformalPoint

-- Reuse the ACTUAL original nine labelled trits; no invented 9 carrier.
toNine : Native → Nine.NineTrits
toNine = H.fabricToNineTrits

fromNine : Nine.NineTrits → Native
fromNine = H.nineTritsToFabric

nativeAfterNine : (p : Native) → fromNine (toNine p) ≡ p
nativeAfterNine = H.fabricNineRoundTrip

nineAfterNative : (p : Nine.NineTrits) → toNine (fromNine p) ≡ p
nineAfterNative = H.nineFabricRoundTrip

-- SOURCE-PROVIDED explicit Fourier coefficients with retained centre.
-- No attempt to prove trig/SymPy orthogonality via a cardinality equation.
module ChosenWaveChart
  (Wave8 Centre : Set)
  (encode : Nine.NineTrits → Wave8 × Centre)
  (decode : Wave8 × Centre → Nine.NineTrits)
  (decodeEncode : (x : Nine.NineTrits) → decode (encode x) ≡ x) where

  nativeEncode : Native → Wave8 × Centre
  nativeEncode x = encode (toNine x)

  nativeDecode : Wave8 × Centre → Native
  nativeDecode w = fromNine (decode w)

  nativeReopens : (x : Native) →
    nativeDecode (nativeEncode x) ≡ x
  nativeReopens x =
    trans (Future.cong fromNine (decodeEncode (toNine x)))
      (nativeAfterNine x)
    where
      trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
      trans refl q = q

  -- If a genuine E8 wave action moves an encoded source point outside
  -- the image of nativeEncode, a native-only action cannot represent it.
  module WeylAction
    (act : Wave8 → Wave8) where

    actPacket : Wave8 × Centre → Wave8 × Centre
    actPacket (w , c) = (act w , c)

    record NativeActionClosure : Set where
      field
        action : Native → Native
        closed : (x : Native) →
          nativeEncode (action x) ≡ actPacket (nativeEncode x)

    -- A concrete witness of nonclosure is a proof about THIS chart,
    -- not a disproof of the E8 lattice or of the 369 fabric.
    module Nonclosure
      (witness : Native)
      (outside : (y : Native) →
        nativeEncode y ≡ actPacket (nativeEncode witness) → ⊥) where

      impossibleToClose :
        (nativeAction : Native → Native) →
        ((x : Native) →
          nativeEncode (nativeAction x) ≡ actPacket (nativeEncode x)) → ⊥
      impossibleToClose nativeAction transport =
        outside (nativeAction witness) (transport witness)

-- Prior owner E8: rank 8 and 240 roots are real root-lattice facts,
-- not a declaration of an equivariant action on ternary9.
e8RankWitness : E8.rankE8 ≡ 8
e8RankWitness = E8.rankE8IsEight

e8RootCountWitness : E8.rootCountE8 ≡ 240
e8RootCountWitness = E8.E8Has240Roots

-- Existing Leech-LILA 384D architecture packs 16 contiguous 24D blocks;
-- each 24D block may carry three 8D ambient charts. It does not become
-- an actual Leech lattice without a gluing/coset/isometry proof.
lila24DChartCount : 384 ≡ 16 * 24
lila24DChartCount = Lila.d384IsSixteen24Blocks

-- Full nine-site wave chart has an independent DC/centre amplitude.
-- If two real native address vectors have the same eight non-DC
-- coordinates but different centres, no eight-only reader can reopen
-- that centre. Exact SymPy fixture: all-zero and all-one 9-site rows.
module CentreResidualNecessity
  {Wave8 Centre : Set}
  (wave : Native → Wave8)
  (centre : Native → Centre)
  (zero one : Native)
  (sameWave : wave zero ≡ wave one)
  (distinctCentre : centre zero ≡ centre one → ⊥) where

  sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
  sym refl = refl

  trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans refl q = q

  noNonDCOnlyReopening :
    (reader : Wave8 → Centre) →
    ((native : Native) → reader (wave native) ≡ centre native) →
    ⊥
  noNonDCOnlyReopening reader faithful =
    distinctCentre
      (trans (sym (faithful zero))
        (trans (Future.cong reader sameWave) (faithful one)))

-- 384 = 16 blocks of 24 = 48 ambient 8D Fourier/E8 charts.
-- Forty-eight independent nine-site centre amplitudes are NOT inside
-- those 384 wave slots. Their retention is required for exact BIDI
-- on arbitrary original nine-site amplitudes.
lilaWaveCharts : 384 ≡ 48 * 8
lilaWaveCharts = refl

lilaIndependentCentreCount : 48 ≡ 16 * 3
lilaIndependentCentreCount = refl
