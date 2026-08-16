module DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Field Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- DASHI CONTRIBUTION
--
-- Tie the repository's five physical H-R_beta channels directly to the finite
-- quartic beta enclosure consumed by the source-normalized coupling history.
-- The five channels are determinant, interaction, chart, gauge and
-- localization.  A physical proof now only has to establish, cell-by-cell,
--
--     - c_{cell,channel} g^4 <= r_{cell,channel},
--     0 <= c_{cell,channel}.
--
-- This module constructs the finite interaction atom family itself and proves
-- that its betaInt is definitionally the nested physical five-channel sum.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; -_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta

data PhysicalBetaChannel : Set where
  determinant interaction chart gauge localization : PhysicalBetaChannel

channels : List PhysicalBetaChannel
channels = determinant ∷ interaction ∷ chart ∷ gauge ∷ localization ∷ []

record FiveChannelQuarticBetaData (Cell : Set) : Set₁ where
  field
    cells : List Cell
    coupling : ℚ

    determinantRemainder interactionRemainder chartRemainder
      gaugeRemainder localizationRemainder : Cell → ℚ

    determinantCoefficient interactionCoefficient chartCoefficient
      gaugeCoefficient localizationCoefficient : Cell → ℚ

    determinantCoefficientNN : ∀ cell → 0ℚ ≤ determinantCoefficient cell
    interactionCoefficientNN : ∀ cell → 0ℚ ≤ interactionCoefficient cell
    chartCoefficientNN : ∀ cell → 0ℚ ≤ chartCoefficient cell
    gaugeCoefficientNN : ∀ cell → 0ℚ ≤ gaugeCoefficient cell
    localizationCoefficientNN : ∀ cell → 0ℚ ≤ localizationCoefficient cell

    determinantLower : ∀ cell →
      - (determinantCoefficient cell * Beta.power4 coupling)
      ≤ determinantRemainder cell
    interactionLower : ∀ cell →
      - (interactionCoefficient cell * Beta.power4 coupling)
      ≤ interactionRemainder cell
    chartLower : ∀ cell →
      - (chartCoefficient cell * Beta.power4 coupling)
      ≤ chartRemainder cell
    gaugeLower : ∀ cell →
      - (gaugeCoefficient cell * Beta.power4 coupling)
      ≤ gaugeRemainder cell
    localizationLower : ∀ cell →
      - (localizationCoefficient cell * Beta.power4 coupling)
      ≤ localizationRemainder cell

open FiveChannelQuarticBetaData public

channelRemainder :
  ∀ {Cell} → FiveChannelQuarticBetaData Cell →
  Cell → PhysicalBetaChannel → ℚ
channelRemainder data cell determinant = determinantRemainder data cell
channelRemainder data cell interaction = interactionRemainder data cell
channelRemainder data cell chart = chartRemainder data cell
channelRemainder data cell gauge = gaugeRemainder data cell
channelRemainder data cell localization = localizationRemainder data cell

channelCoefficient :
  ∀ {Cell} → FiveChannelQuarticBetaData Cell →
  Cell → PhysicalBetaChannel → ℚ
channelCoefficient data cell determinant = determinantCoefficient data cell
channelCoefficient data cell interaction = interactionCoefficient data cell
channelCoefficient data cell chart = chartCoefficient data cell
channelCoefficient data cell gauge = gaugeCoefficient data cell
channelCoefficient data cell localization = localizationCoefficient data cell

channelCoefficientNN :
  ∀ {Cell} (data : FiveChannelQuarticBetaData Cell) cell channel →
  0ℚ ≤ channelCoefficient data cell channel
channelCoefficientNN data cell determinant = determinantCoefficientNN data cell
channelCoefficientNN data cell interaction = interactionCoefficientNN data cell
channelCoefficientNN data cell chart = chartCoefficientNN data cell
channelCoefficientNN data cell gauge = gaugeCoefficientNN data cell
channelCoefficientNN data cell localization = localizationCoefficientNN data cell

channelLower :
  ∀ {Cell} (data : FiveChannelQuarticBetaData Cell) cell channel →
  - (channelCoefficient data cell channel * Beta.power4 (coupling data))
  ≤ channelRemainder data cell channel
channelLower data cell determinant = determinantLower data cell
channelLower data cell interaction = interactionLower data cell
channelLower data cell chart = chartLower data cell
channelLower data cell gauge = gaugeLower data cell
channelLower data cell localization = localizationLower data cell

localRemainder :
  ∀ {Cell} → FiveChannelQuarticBetaData Cell → Cell → ℚ
localRemainder data cell =
  Sums.sumRational channels (channelRemainder data cell)

localCoefficient :
  ∀ {Cell} → FiveChannelQuarticBetaData Cell → Cell → ℚ
localCoefficient data cell =
  Sums.sumRational channels (channelCoefficient data cell)

betaInt : ∀ {Cell} → FiveChannelQuarticBetaData Cell → ℚ
betaInt data = Sums.sumRational (cells data) (localRemainder data)

coefficientTotal : ∀ {Cell} → FiveChannelQuarticBetaData Cell → ℚ
coefficientTotal data = Sums.sumRational (cells data) (localCoefficient data)

sumNonnegative :
  ∀ {A : Set} (indices : List A) (value : A → ℚ) →
  (∀ index → 0ℚ ≤ value index) →
  0ℚ ≤ Sums.sumRational indices value
sumNonnegative [] value pointwise = ℚP.≤-refl
sumNonnegative (x ∷ xs) value pointwise =
  ℚP.+-mono-≤ (pointwise x) (sumNonnegative xs value pointwise)

localCoefficientNN :
  ∀ {Cell} (data : FiveChannelQuarticBetaData Cell) cell →
  0ℚ ≤ localCoefficient data cell
localCoefficientNN data cell =
  sumNonnegative channels (channelCoefficient data cell)
    (channelCoefficientNN data cell)

coefficientTotalNN :
  ∀ {Cell} (data : FiveChannelQuarticBetaData Cell) →
  0ℚ ≤ coefficientTotal data
coefficientTotalNN data =
  sumNonnegative (cells data) (localCoefficient data)
    (localCoefficientNN data)

localQuarticLower :
  ∀ {Cell} (data : FiveChannelQuarticBetaData Cell) cell →
  - (localCoefficient data cell * Beta.power4 (coupling data))
  ≤ localRemainder data cell
localQuarticLower data cell =
  let
    fourth = Beta.power4 (coupling data)
    pointwiseSum :
      Sums.sumRational channels
        (λ channel → - (channelCoefficient data cell channel * fourth))
      ≤ localRemainder data cell
    pointwiseSum = Beta.sumMonotone
      channels
      (λ channel → - (channelCoefficient data cell channel * fourth))
      (channelRemainder data cell)
      (channelLower data cell)

    identify :
      Sums.sumRational channels
        (λ channel → - (channelCoefficient data cell channel * fourth))
      ≡ - (localCoefficient data cell * fourth)
    identify = trans
      (Sums.sumRationalNegate channels
        (λ channel → channelCoefficient data cell channel * fourth))
      (cong -_
        (trans
          (Sums.sumRationalCong channels
            (λ channel → channelCoefficient data cell channel * fourth)
            (λ channel → fourth * channelCoefficient data cell channel)
            (λ channel → ℚRing.solve-∀
              (channelCoefficient data cell channel) fourth))
          (trans
            (Sums.sumRationalScale fourth channels
              (channelCoefficient data cell))
            (ℚRing.solve-∀ fourth (localCoefficient data cell)))))
  in
  subst (λ lower → lower ≤ localRemainder data cell)
    identify pointwiseSum

globalQuarticLower :
  ∀ {Cell} (data : FiveChannelQuarticBetaData Cell) →
  - (coefficientTotal data * Beta.power4 (coupling data))
  ≤ betaInt data
globalQuarticLower data =
  let
    fourth = Beta.power4 (coupling data)
    pointwiseSum :
      Sums.sumRational (cells data)
        (λ cell → - (localCoefficient data cell * fourth))
      ≤ betaInt data
    pointwiseSum = Beta.sumMonotone
      (cells data)
      (λ cell → - (localCoefficient data cell * fourth))
      (localRemainder data)
      (localQuarticLower data)

    identify :
      Sums.sumRational (cells data)
        (λ cell → - (localCoefficient data cell * fourth))
      ≡ - (coefficientTotal data * fourth)
    identify = trans
      (Sums.sumRationalNegate (cells data)
        (λ cell → localCoefficient data cell * fourth))
      (cong -_
        (trans
          (Sums.sumRationalCong (cells data)
            (λ cell → localCoefficient data cell * fourth)
            (λ cell → fourth * localCoefficient data cell)
            (λ cell → ℚRing.solve-∀ (localCoefficient data cell) fourth))
          (trans
            (Sums.sumRationalScale fourth (cells data) (localCoefficient data))
            (ℚRing.solve-∀ fourth (coefficientTotal data)))))
  in
  subst (λ lower → lower ≤ betaInt data)
    identify pointwiseSum

asFiniteInteractionAtomEnclosure :
  ∀ {Cell} (data : FiveChannelQuarticBetaData Cell) →
  Beta.FiniteInteractionAtomEnclosure Cell
asFiniteInteractionAtomEnclosure data = record
  { Beta.FiniteInteractionAtomEnclosure.atoms = cells data
  ; Beta.FiniteInteractionAtomEnclosure.coupling = coupling data
  ; Beta.FiniteInteractionAtomEnclosure.betaInt = betaInt data
  ; Beta.FiniteInteractionAtomEnclosure.interactionAtom = localRemainder data
  ; Beta.FiniteInteractionAtomEnclosure.coefficient = localCoefficient data
  ; Beta.FiniteInteractionAtomEnclosure.betaIntExact = refl
  ; Beta.FiniteInteractionAtomEnclosure.coefficientNonnegative = localCoefficientNN data
  ; Beta.FiniteInteractionAtomEnclosure.atomLower = localQuarticLower data
  }

yM4FiveChannelQuarticBetaAdapterLevel : ProofLevel
yM4FiveChannelQuarticBetaAdapterLevel = machineChecked

yM4FiveChannelPhysicalEstimatesLevel : ProofLevel
yM4FiveChannelPhysicalEstimatesLevel = conditional
