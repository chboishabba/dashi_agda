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
  determinant : PhysicalBetaChannel
  interaction : PhysicalBetaChannel
  chart : PhysicalBetaChannel
  gauge : PhysicalBetaChannel
  localization : PhysicalBetaChannel

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
channelRemainder dat cell determinant = determinantRemainder dat cell
channelRemainder dat cell interaction = interactionRemainder dat cell
channelRemainder dat cell chart = chartRemainder dat cell
channelRemainder dat cell gauge = gaugeRemainder dat cell
channelRemainder dat cell localization = localizationRemainder dat cell

channelCoefficient :
  ∀ {Cell} → FiveChannelQuarticBetaData Cell →
  Cell → PhysicalBetaChannel → ℚ
channelCoefficient dat cell determinant = determinantCoefficient dat cell
channelCoefficient dat cell interaction = interactionCoefficient dat cell
channelCoefficient dat cell chart = chartCoefficient dat cell
channelCoefficient dat cell gauge = gaugeCoefficient dat cell
channelCoefficient dat cell localization = localizationCoefficient dat cell

channelCoefficientNN :
  ∀ {Cell} (dat : FiveChannelQuarticBetaData Cell) cell channel →
  0ℚ ≤ channelCoefficient dat cell channel
channelCoefficientNN dat cell determinant = determinantCoefficientNN dat cell
channelCoefficientNN dat cell interaction = interactionCoefficientNN dat cell
channelCoefficientNN dat cell chart = chartCoefficientNN dat cell
channelCoefficientNN dat cell gauge = gaugeCoefficientNN dat cell
channelCoefficientNN dat cell localization = localizationCoefficientNN dat cell

channelLower :
  ∀ {Cell} (dat : FiveChannelQuarticBetaData Cell) cell channel →
  - (channelCoefficient dat cell channel * Beta.power4 (coupling dat))
  ≤ channelRemainder dat cell channel
channelLower dat cell determinant = determinantLower dat cell
channelLower dat cell interaction = interactionLower dat cell
channelLower dat cell chart = chartLower dat cell
channelLower dat cell gauge = gaugeLower dat cell
channelLower dat cell localization = localizationLower dat cell

localRemainder :
  ∀ {Cell} → FiveChannelQuarticBetaData Cell → Cell → ℚ
localRemainder dat cell =
  Sums.sumRational channels (channelRemainder dat cell)

localCoefficient :
  ∀ {Cell} → FiveChannelQuarticBetaData Cell → Cell → ℚ
localCoefficient dat cell =
  Sums.sumRational channels (channelCoefficient dat cell)

betaInt : ∀ {Cell} → FiveChannelQuarticBetaData Cell → ℚ
betaInt dat = Sums.sumRational (cells dat) (localRemainder dat)

coefficientTotal : ∀ {Cell} → FiveChannelQuarticBetaData Cell → ℚ
coefficientTotal dat = Sums.sumRational (cells dat) (localCoefficient dat)

sumNonnegative :
  ∀ {A : Set} (indices : List A) (value : A → ℚ) →
  (∀ index → 0ℚ ≤ value index) →
  0ℚ ≤ Sums.sumRational indices value
sumNonnegative [] value pointwise = ℚP.≤-refl
sumNonnegative (x ∷ xs) value pointwise =
  ℚP.+-mono-≤ (pointwise x) (sumNonnegative xs value pointwise)

localCoefficientNN :
  ∀ {Cell} (dat : FiveChannelQuarticBetaData Cell) cell →
  0ℚ ≤ localCoefficient dat cell
localCoefficientNN dat cell =
  sumNonnegative channels (channelCoefficient dat cell)
    (channelCoefficientNN dat cell)

coefficientTotalNN :
  ∀ {Cell} (dat : FiveChannelQuarticBetaData Cell) →
  0ℚ ≤ coefficientTotal dat
coefficientTotalNN dat =
  sumNonnegative (cells dat) (localCoefficient dat)
    (localCoefficientNN dat)

localQuarticLower :
  ∀ {Cell} (dat : FiveChannelQuarticBetaData Cell) cell →
  - (localCoefficient dat cell * Beta.power4 (coupling dat))
  ≤ localRemainder dat cell
localQuarticLower dat cell =
  let
    fourth = Beta.power4 (coupling dat)
    pointwiseSum :
      Sums.sumRational channels
        (λ channel → - (channelCoefficient dat cell channel * fourth))
      ≤ localRemainder dat cell
    pointwiseSum = Beta.sumMonotone
      channels
      (λ channel → - (channelCoefficient dat cell channel * fourth))
      (channelRemainder dat cell)
      (channelLower dat cell)

    identify :
      Sums.sumRational channels
        (λ channel → - (channelCoefficient dat cell channel * fourth))
      ≡ - (localCoefficient dat cell * fourth)
    identify = trans
      (Sums.sumRationalNegate channels
        (λ channel → channelCoefficient dat cell channel * fourth))
      (cong -_
        (trans
          (Sums.sumRationalCong channels
            (λ channel → channelCoefficient dat cell channel * fourth)
            (λ channel → fourth * channelCoefficient dat cell channel)
            (λ channel → ℚRing.solve-∀
              (channelCoefficient dat cell channel) fourth))
          (trans
            (Sums.sumRationalScale fourth channels
              (channelCoefficient dat cell))
            (ℚRing.solve-∀ fourth (localCoefficient dat cell)))))
  in
  subst (λ lower → lower ≤ localRemainder dat cell)
    identify pointwiseSum

globalQuarticLower :
  ∀ {Cell} (dat : FiveChannelQuarticBetaData Cell) →
  - (coefficientTotal dat * Beta.power4 (coupling dat))
  ≤ betaInt dat
globalQuarticLower dat =
  let
    fourth = Beta.power4 (coupling dat)
    pointwiseSum :
      Sums.sumRational (cells dat)
        (λ cell → - (localCoefficient dat cell * fourth))
      ≤ betaInt dat
    pointwiseSum = Beta.sumMonotone
      (cells dat)
      (λ cell → - (localCoefficient dat cell * fourth))
      (localRemainder dat)
      (localQuarticLower dat)

    identify :
      Sums.sumRational (cells dat)
        (λ cell → - (localCoefficient dat cell * fourth))
      ≡ - (coefficientTotal dat * fourth)
    identify = trans
      (Sums.sumRationalNegate (cells dat)
        (λ cell → localCoefficient dat cell * fourth))
      (cong -_
        (trans
          (Sums.sumRationalCong (cells dat)
            (λ cell → localCoefficient dat cell * fourth)
            (λ cell → fourth * localCoefficient dat cell)
            (λ cell → ℚRing.solve-∀ (localCoefficient dat cell) fourth))
          (trans
            (Sums.sumRationalScale fourth (cells dat) (localCoefficient dat))
            (ℚRing.solve-∀ fourth (coefficientTotal dat)))))
  in
  subst (λ lower → lower ≤ betaInt dat)
    identify pointwiseSum

asFiniteInteractionAtomEnclosure :
  ∀ {Cell} (dat : FiveChannelQuarticBetaData Cell) →
  Beta.FiniteInteractionAtomEnclosure Cell
asFiniteInteractionAtomEnclosure dat = record
  { Beta.FiniteInteractionAtomEnclosure.atoms = cells dat
  ; Beta.FiniteInteractionAtomEnclosure.coupling = coupling dat
  ; Beta.FiniteInteractionAtomEnclosure.betaInt = betaInt dat
  ; Beta.FiniteInteractionAtomEnclosure.interactionAtom = localRemainder dat
  ; Beta.FiniteInteractionAtomEnclosure.coefficient = localCoefficient dat
  ; Beta.FiniteInteractionAtomEnclosure.betaIntExact = refl
  ; Beta.FiniteInteractionAtomEnclosure.coefficientNonnegative = localCoefficientNN dat
  ; Beta.FiniteInteractionAtomEnclosure.atomLower = localQuarticLower dat
  }

yM4FiveChannelQuarticBetaAdapterLevel : ProofLevel
yM4FiveChannelQuarticBetaAdapterLevel = machineChecked

yM4FiveChannelPhysicalEstimatesLevel : ProofLevel
yM4FiveChannelPhysicalEstimatesLevel = conditional
