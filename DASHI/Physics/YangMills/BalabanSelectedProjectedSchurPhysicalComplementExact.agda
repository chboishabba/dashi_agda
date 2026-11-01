module DASHI.Physics.YangMills.BalabanSelectedProjectedSchurPhysicalComplementExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Identify the projected padded Schur operator with the literal reduced
-- physical Schur complement of the selected 12 + 765 combined constraint
-- Gram.  On a reduced gauge multiplier gamma,
--
--   P_g (K_g,A gamma - (1/256) C_A C_A^T gamma)
--     = K_0 gamma + P_g Q_A gamma
--     = S~_A gamma.
--
-- This closes the operator same-object seam needed before the finite Schur
-- Green may be used to reconstruct the actual reduced multiplier inverse.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean
import DASHI.Physics.YangMills.BalabanSelectedGaugeCenteringLinearityExact as Center
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGramPreservesReducedExact as FlatReduced
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeOperatorDecompositionExact as GaugeOperator
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationActionExact as GaugePerturbation
import DASHI.Physics.YangMills.BalabanSelectedSchurPerturbationActionExact as SchurAction
import DASHI.Physics.YangMills.BalabanSelectedProjectedSchurGreenFiniteExact as SchurGreen
import DASHI.Physics.YangMills.BalabanSelectedProjectedPaddedSchurReducedSameObjectExact as ReducedSame
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical

GaugeMultiplier : Set
GaugeMultiplier = FlatFloor.GaugeMultiplier

physicalSchurComplementApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
physicalSchurComplementApply background multiplier row =
  GaugeOperator.backgroundGaugeGramApply background multiplier row
  - SchurAction.schurCorrectionApply background multiplier row

flatPlusSchurPerturbationIsPhysicalComplement :
  ∀ background multiplier row →
  FlatGreen.flatGaugeGramApply multiplier row
    + SchurAction.schurPerturbationApply background multiplier row
  ≡ physicalSchurComplementApply background multiplier row
flatPlusSchurPerturbationIsPhysicalComplement background multiplier row =
  let
    flat = FlatGreen.flatGaugeGramApply multiplier row
    correction = SchurAction.schurCorrectionApply background multiplier row
    explicit = GaugeOperator.explicitGaugeGramPerturbation background multiplier row
  in
  trans
    (cong (flat +_)
      (SchurAction.schurPerturbationApplyDifferenceExact
        background multiplier row))
    (trans
      (cong
        (λ e → flat + (e - correction))
        (GaugePerturbation.selectedGaugeGramPerturbationActsAsExplicitEA
          background multiplier row))
      (trans
        (ℚRing.solve-∀ flat explicit correction)
        (cong (_- correction)
          (sym
            (GaugeOperator.backgroundGaugeGramDecomposition
              background multiplier row)))))

constantProjectionRespectsPointwise :
  ∀ {left right : GaugeMultiplier} →
  (∀ row → left row ≡ right row) →
  ∀ coordinate site →
  Mean.constantProjection left (Torus.pair coordinate site)
  ≡ Mean.constantProjection right (Torus.pair coordinate site)
constantProjectionRespectsPointwise {left} {right} pointwise coordinate site =
  cong (GlobalAverage.oneTwoFiftySix *_)
    (Periodic.sumSitesCong
      (FlatFloor.gaugeMultiplierField left coordinate)
      (FlatFloor.gaugeMultiplierField right coordinate)
      (λ current → pointwise (Torus.pair coordinate current)))

centeredMultiplierRespectsPointwise :
  ∀ {left right : GaugeMultiplier} →
  (∀ row → left row ≡ right row) →
  ∀ coordinate site →
  Mean.centeredMultiplier left (Torus.pair coordinate site)
  ≡ Mean.centeredMultiplier right (Torus.pair coordinate site)
centeredMultiplierRespectsPointwise {left} {right} pointwise coordinate site =
  trans
    (cong
      (_- Mean.constantProjection left (Torus.pair coordinate site))
      (pointwise (Torus.pair coordinate site)))
    (cong
      (right (Torus.pair coordinate site) -_)
      (constantProjectionRespectsPointwise pointwise coordinate site))

centeredPhysicalComplementAsFlatPlusProjectedQ :
  ∀ background multiplier →
  FlatFloor.FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate site →
  Mean.centeredMultiplier
    (physicalSchurComplementApply background multiplier)
    (Torus.pair coordinate site)
  ≡ FlatGreen.flatGaugeGramApply multiplier (Torus.pair coordinate site)
    + Mean.centeredMultiplier
        (SchurAction.schurPerturbationApply background multiplier)
        (Torus.pair coordinate site)
centeredPhysicalComplementAsFlatPlusProjectedQ
    background multiplier reduced coordinate site =
  let
    flat = FlatGreen.flatGaugeGramApply multiplier
    q = SchurAction.schurPerturbationApply background multiplier
    sum = Center.addMultiplier flat q

    uncentered : ∀ row →
      sum row ≡ physicalSchurComplementApply background multiplier row
    uncentered row =
      flatPlusSchurPerturbationIsPhysicalComplement background multiplier row
  in
  trans
    (sym
      (centeredMultiplierRespectsPointwise
        uncentered coordinate site))
    (trans
      (Center.centeredMultiplierAddExact flat q coordinate site)
      (cong
        (_+ Mean.centeredMultiplier q (Torus.pair coordinate site))
        (FlatReduced.flatGaugeGramCenteredExact multiplier coordinate site)))

projectedPaddedSchurIsReducedPhysicalComplement :
  ∀ background multiplier →
  FlatFloor.FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate site →
  SchurGreen.projectedPaddedSchurApply background multiplier
    (Torus.pair coordinate site)
  ≡ Mean.centeredMultiplier
      (physicalSchurComplementApply background multiplier)
      (Torus.pair coordinate site)
projectedPaddedSchurIsReducedPhysicalComplement
    background multiplier reduced coordinate site =
  trans
    (ReducedSame.projectedPaddedSchurReducedPhysicalActionExact
      background multiplier reduced coordinate site)
    (sym
      (centeredPhysicalComplementAsFlatPlusProjectedQ
        background multiplier reduced coordinate site))

selectedProjectedSchurPhysicalComplementLevel : ProofLevel
selectedProjectedSchurPhysicalComplementLevel = machineChecked
