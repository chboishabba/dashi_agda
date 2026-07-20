module DASHI.Biology.DNACompiledOperatorsRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Vec using ([]; _∷_)

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Biology.DNAChemistryEnergyAlgebra as Energy
import DASHI.Biology.DNAChemistryFeatureQuotient as Quotient
import DASHI.Biology.DNACrossRankInteraction as CrossRank
import DASHI.Foundations.DNATetrationalClosure as Tower
import DASHI.Geometry.DNAFourAdicSheetLift as Lift
import DASHI.Geometry.DNAFourAdicUltrametric as Metric
import DASHI.Geometry.DNAFourWayLiftOperators as Operators

address : Metric.Address (suc (suc zero))
address = DNA.A ∷ DNA.C ∷ []

ultrametricIdentity : Metric.distance address address ≡ zero
ultrametricIdentity = Metric.distance-self-zero address

quadExample : Lift.Quad DNA.DNABase
quadExample = Lift.quad DNA.A DNA.C DNA.G DNA.T

quadReconstruction :
  Operators.reconstruct (Operators.project quadExample) (Operators.residual quadExample)
  ≡ quadExample
quadReconstruction = Operators.reconstruction quadExample

quadReverseComplementInvolutive :
  Operators.reverseComplementQuad (Operators.reverseComplementQuad quadExample)
  ≡ quadExample
quadReverseComplementInvolutive =
  Operators.reverseComplementQuad-involutive quadExample

featureEquivalenceReflexive :
  ∀ Φ xs → Quotient.FeatureFibreQuotient Φ xs xs
featureEquivalenceReflexive = Quotient.feature-refl

basinEquivalenceTransitive :
  ∀ {Φ basin x y z} →
  Quotient.BasinQuotient Φ basin x y →
  Quotient.BasinQuotient Φ basin y z →
  Quotient.BasinQuotient Φ basin x z
basinEquivalenceTransitive = Quotient.basin-trans

zeroHamiltonianRegression :
  ∀ xs → Energy.Hamiltonian Energy.canonicalOperationalModel xs ≡ zero
zeroHamiltonianRegression = Energy.canonicalHamiltonianIsZero

towerBaseRegression : Tower.tower zero ≡ Tower.four
towerBaseRegression = Tower.tower-zero

crossRankEnergyCarrier : CrossRank.AdditiveEnergy _
crossRankEnergyCarrier = CrossRank.natAdditiveEnergy
