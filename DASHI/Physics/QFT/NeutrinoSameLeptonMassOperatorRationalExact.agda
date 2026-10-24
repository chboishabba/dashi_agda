module DASHI.Physics.QFT.NeutrinoSameLeptonMassOperatorRationalExact where

------------------------------------------------------------------------
-- SAME-LEPTON-SPACE MASS-OPERATOR CONSTRUCTION (EXACT RATIONAL WITNESS)
--
-- Attribution:
-- PMNS=U_l^dagger U_nu and residual G_e vs G_nu are standard physics,
-- not an original DASHI discovery.  Mathematical context:
-- Fonseca and Grimus, JHEP 09 (2014) 033,
-- DOI 10.1007/JHEP09(2014)033;
-- Hagedorn and Koenig, Phys Rev D 100 (2019) 075036,
-- DOI 10.1103/PhysRevD.100.075036.
-- Observable comparisons: NuFIT 6.1 (2025), IC24 with SK.
--
-- DASHI CONTRIBUTION:
-- A *post-hoc chosen*, exactly orthogonal rational near-data mixing
-- matrix on the same three-dimensional flavour space; exact
-- mass-squared operator and its diagonalization, two inherited
-- neutrino involutions, and a separate charged-lepton C3 action.
-- The fitted inputs are premises, not algebraic predictions.
-- This is a CP-EVEN real construction: J_CP = 0 by construction.
-- NO physical Dirac or Majorana mass-mechanism claim and NO finite
-- flavour group generated jointly by T and S is asserted.
--
-- Rational PDG angles (sin,cos):
-- 12 : (161/289,240/289)
-- 13 : (240/1609,1591/1609)
-- 23 : (20/29,21/29)
--
-- U = R23 R13 R12, delta_CP=0, represented by integer M / D;
-- D = 289*1609*29 = 13485029.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as Three
import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Reasoning.RelationalTernaryPhaseGeometry as Eisenstein

open Three using (Flavour; electron; muon; tau;
                  MassBasis; mass1; mass2; mass3)

commonDenominator : ℤ
commonDenominator = + 13485029

mixNum : Flavour → MassBasis → ℤ
mixNum electron mass1 = + 11073360
mixNum electron mass2 = + 7428379
mixNum electron mass3 = + 2011440
mixNum muon mass1 = - (+ 6592029)
mixNum muon mass2 = + 7336560
mixNum muon mass3 = + 9195980
mixNum tau mass1 = + 3971380
mixNum tau mass2 = - (+ 8534640)
mixNum tau mass3 = + 9655779

denominatorSquared : ℤ
denominatorSquared = commonDenominator * commonDenominator

denominatorSquaredValue :
  denominatorSquared ≡ + 181846007130841
denominatorSquaredValue = refl

gramRows : Flavour → Flavour → ℤ
gramRows a b =
  mixNum a mass1 * mixNum b mass1 +
  (mixNum a mass2 * mixNum b mass2 +
   mixNum a mass3 * mixNum b mass3)

gramColumns : MassBasis → MassBasis → ℤ
gramColumns i j =
  mixNum electron i * mixNum electron j +
  (mixNum muon i * mixNum muon j +
   mixNum tau i * mixNum tau j)

flavourKronecker : Flavour → Flavour → ℤ
flavourKronecker electron electron = + 1
flavourKronecker muon muon = + 1
flavourKronecker tau tau = + 1
flavourKronecker _ _ = + 0

massKronecker : MassBasis → MassBasis → ℤ
massKronecker mass1 mass1 = + 1
massKronecker mass2 mass2 = + 1
massKronecker mass3 mass3 = + 1
massKronecker _ _ = + 0

-- All nine exact integer row/column Gram identities. The symbolic
-- matrix is NOT stipulated orthogonal: check its computed dot products.
rowsOrthogonal :
  (a b : Flavour) →
  gramRows a b ≡ denominatorSquared * flavourKronecker a b
rowsOrthogonal electron electron = refl
rowsOrthogonal electron muon = refl
rowsOrthogonal electron tau = refl
rowsOrthogonal muon electron = refl
rowsOrthogonal muon muon = refl
rowsOrthogonal muon tau = refl
rowsOrthogonal tau electron = refl
rowsOrthogonal tau muon = refl
rowsOrthogonal tau tau = refl

columnsOrthogonal :
  (i j : MassBasis) →
  gramColumns i j ≡ denominatorSquared * massKronecker i j
columnsOrthogonal mass1 mass1 = refl
columnsOrthogonal mass1 mass2 = refl
columnsOrthogonal mass1 mass3 = refl
columnsOrthogonal mass2 mass1 = refl
columnsOrthogonal mass2 mass2 = refl
columnsOrthogonal mass2 mass3 = refl
columnsOrthogonal mass3 mass1 = refl
columnsOrthogonal mass3 mass2 = refl
columnsOrthogonal mass3 mass3 = refl

------------------------------------------------------------------------
-- A neutral-sector positive mass-squared Hamiltonian selected from
-- *external measured* NuFIT difference parameters.  A common additive
-- mass-squared offset is deliberately set to 0, since oscillations
-- alone do not determine the absolute mass scale.
--
-- Eigenvalues in units 10^-8 eV²: (0,7537,251100), NOT absolute
-- neutrino masses.  The matrix here is H_nu numerator times D^-2.
------------------------------------------------------------------------

deltaMassSquared : MassBasis → ℤ
deltaMassSquared mass1 = + 0
deltaMassSquared mass2 = + 7537
deltaMassSquared mass3 = + 251100

massSquaredNum : Flavour → Flavour → ℤ
massSquaredNum a b =
  mixNum a mass1 * deltaMassSquared mass1 * mixNum b mass1 +
  (mixNum a mass2 * deltaMassSquared mass2 * mixNum b mass2 +
   mixNum a mass3 * deltaMassSquared mass3 * mixNum b mass3)

massSquaredSymmetric :
  (a b : Flavour) →
  massSquaredNum a b ≡ massSquaredNum b a
massSquaredSymmetric electron electron = refl
massSquaredSymmetric electron muon = refl
massSquaredSymmetric electron tau = refl
massSquaredSymmetric muon electron = refl
massSquaredSymmetric muon muon = refl
massSquaredSymmetric muon tau = refl
massSquaredSymmetric tau electron = refl
massSquaredSymmetric tau muon = refl
massSquaredSymmetric tau tau = refl

massSquaredOnColumn : Flavour → MassBasis → ℤ
massSquaredOnColumn a i =
  massSquaredNum a electron * mixNum electron i +
  (massSquaredNum a muon * mixNum muon i +
   massSquaredNum a tau * mixNum tau i)

-- True eigen-equation H M_i = D^2 lambda_i M_i:
-- no invented PMNS mass scale or kernel-implied phenomenology.
massSquaredEigenEquation :
  (a : Flavour) (i : MassBasis) →
  massSquaredOnColumn a i ≡
    denominatorSquared * deltaMassSquared i * mixNum a i
massSquaredEigenEquation electron mass1 = refl
massSquaredEigenEquation electron mass2 = refl
massSquaredEigenEquation electron mass3 = refl
massSquaredEigenEquation muon mass1 = refl
massSquaredEigenEquation muon mass2 = refl
massSquaredEigenEquation muon mass3 = refl
massSquaredEigenEquation tau mass1 = refl
massSquaredEigenEquation tau mass2 = refl
massSquaredEigenEquation tau mass3 = refl

nonzeroLeptonOffDiagonal :
  massSquaredNum electron muon ≡ + 5055394446468860880
nonzeroLeptonOffDiagonal = refl

------------------------------------------------------------------------
-- Two neutrino-sector residual Z2 involutions, obtained from the
-- chosen mass eigenvectors.  Together these generate the Klein four
-- on the *same* flavour coordinates.  Since they are constructed
-- FROM M, their existence is NOT an independent mechanism selecting M.
------------------------------------------------------------------------

data NuResidual : Set where
  firstInvolution secondInvolution thirdInvolution : NuResidual

residualEigenSign : NuResidual → MassBasis → ℤ
residualEigenSign firstInvolution mass1 = + 1
residualEigenSign firstInvolution mass2 = - (+ 1)
residualEigenSign firstInvolution mass3 = - (+ 1)
residualEigenSign secondInvolution mass1 = - (+ 1)
residualEigenSign secondInvolution mass2 = + 1
residualEigenSign secondInvolution mass3 = - (+ 1)
residualEigenSign thirdInvolution mass1 = - (+ 1)
residualEigenSign thirdInvolution mass2 = - (+ 1)
residualEigenSign thirdInvolution mass3 = + 1

residualNum : NuResidual → Flavour → Flavour → ℤ
residualNum t a b =
  mixNum a mass1 * residualEigenSign t mass1 * mixNum b mass1 +
  (mixNum a mass2 * residualEigenSign t mass2 * mixNum b mass2 +
   mixNum a mass3 * residualEigenSign t mass3 * mixNum b mass3)

productNum :
  (Flavour → Flavour → ℤ) →
  (Flavour → Flavour → ℤ) →
  Flavour → Flavour → ℤ
productNum A B a b =
  A a electron * B electron b +
  (A a muon * B muon b + A a tau * B tau b)

firstSquareIsIdentity :
  (a b : Flavour) →
  productNum (residualNum firstInvolution)
             (residualNum firstInvolution) a b
    ≡ denominatorSquared * denominatorSquared *
        flavourKronecker a b
firstSquareIsIdentity electron electron = refl
firstSquareIsIdentity electron muon = refl
firstSquareIsIdentity electron tau = refl
firstSquareIsIdentity muon electron = refl
firstSquareIsIdentity muon muon = refl
firstSquareIsIdentity muon tau = refl
firstSquareIsIdentity tau electron = refl
firstSquareIsIdentity tau muon = refl
firstSquareIsIdentity tau tau = refl

secondSquareIsIdentity :
  (a b : Flavour) →
  productNum (residualNum secondInvolution)
             (residualNum secondInvolution) a b
    ≡ denominatorSquared * denominatorSquared *
        flavourKronecker a b
secondSquareIsIdentity electron electron = refl
secondSquareIsIdentity electron muon = refl
secondSquareIsIdentity electron tau = refl
secondSquareIsIdentity muon electron = refl
secondSquareIsIdentity muon muon = refl
secondSquareIsIdentity muon tau = refl
secondSquareIsIdentity tau electron = refl
secondSquareIsIdentity tau muon = refl
secondSquareIsIdentity tau tau = refl

residualKleinProduct :
  (a b : Flavour) →
  productNum (residualNum firstInvolution)
             (residualNum secondInvolution) a b
    ≡ denominatorSquared * residualNum thirdInvolution a b
residualKleinProduct electron electron = refl
residualKleinProduct electron muon = refl
residualKleinProduct electron tau = refl
residualKleinProduct muon electron = refl
residualKleinProduct muon muon = refl
residualKleinProduct muon tau = refl
residualKleinProduct tau electron = refl
residualKleinProduct tau muon = refl
residualKleinProduct tau tau = refl

residualMassCommutes :
  (a b : Flavour) →
  productNum (residualNum firstInvolution) massSquaredNum a b
  ≡ productNum massSquaredNum (residualNum firstInvolution) a b
residualMassCommutes electron electron = refl
residualMassCommutes electron muon = refl
residualMassCommutes electron tau = refl
residualMassCommutes muon electron = refl
residualMassCommutes muon muon = refl
residualMassCommutes muon tau = refl
residualMassCommutes tau electron = refl
residualMassCommutes tau muon = refl
residualMassCommutes tau tau = refl

------------------------------------------------------------------------
-- Charged-lepton sector: same three flavour labels, a *distinct*
-- diagonal mass-squared operator and C3 residual action T.
-- C3 is reused from the original depth-one character owner.
-- T preserves H_l because both are diagonal in this chosen basis.
------------------------------------------------------------------------

chargedMassSquared : Flavour → ℤ
chargedMassSquared electron = + 1
chargedMassSquared muon = + 4
chargedMassSquared tau = + 9

chargedMassNum : Flavour → Flavour → ℤ
chargedMassNum electron electron = chargedMassSquared electron
chargedMassNum muon muon = chargedMassSquared muon
chargedMassNum tau tau = chargedMassSquared tau
chargedMassNum _ _ = + 0

chargedC3Phase : Flavour → C3.C3Phase
chargedC3Phase electron = C3.phase0
chargedC3Phase muon = C3.phase1
chargedC3Phase tau = C3.phase2

chargedC3ThirdPower :
  (a : Flavour) →
  C3.multiplyPhase (chargedC3Phase a)
    (C3.multiplyPhase (chargedC3Phase a)
                      (chargedC3Phase a))
  ≡ C3.phase0
chargedC3ThirdPower electron = refl
chargedC3ThirdPower muon = refl
chargedC3ThirdPower tau = refl

data EIsUnit : C3.C3Phase → Set where
  unitOne : EIsUnit C3.phase0
  unitZeta : EIsUnit C3.phase1
  unitZetaSquared : EIsUnit C3.phase2

chargedResidualHasUnitPhases :
  (a : Flavour) → EIsUnit (chargedC3Phase a)
chargedResidualHasUnitPhases electron = unitOne
chargedResidualHasUnitPhases muon = unitZeta
chargedResidualHasUnitPhases tau = unitZetaSquared

------------------------------------------------------------------------
-- Crucial nonpromotion:
-- * one rational near-data choice is not a prediction from C3/369;
-- * neutrino H_nu mass squared does not decide Dirac vs Majorana;
-- * the group jointly generated by T and residual S is not proved
--   finite, and a model that supplies its actual dynamics is absent;
-- * deltaCP=0, while continuous best-fit CP input is not zero.
------------------------------------------------------------------------

data PhysicalLeptonTheoryPromotion : Set where

noPhysicalLeptonTheoryPromotion :
  PhysicalLeptonTheoryPromotion → ⊥
noPhysicalLeptonTheoryPromotion ()
