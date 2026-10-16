module DASHI.Physics.Chemistry.AmmoniaHamiltonianWavefunctionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as Electronic

------------------------------------------------------------------------
-- NH3 SAME-OBJECT HAMILTONIAN / WAVEFUNCTION CARRIER
--
-- This module owns a source-backed SYMBOLIC molecular-Hamiltonian expression
-- on the NH3 object and a literal closed-shell occupation-basis state.  It does
-- not pretend that a symbolic expression is an evaluated energy operator,
-- numerical matrix, eigenproblem solution, or real-space wavefunction.
------------------------------------------------------------------------

meyer2002MolecularHamiltonian : Source.AttributedSource
meyer2002MolecularHamiltonian =
  Source.mkDOISource
    "Henning Meyer"
    "The Molecular Hamiltonian"
    "Annual Review of Physical Chemistry 53 (2002) 141-172"
    "2002"
    "10.1146/annurev.physchem.53.082201.124330"
    "https://doi.org/10.1146/annurev.physchem.53.082201.124330"
    Source.academicArticleSource
    "general authority for molecular Hamiltonian construction in normal/internal coordinates; not NH3-specific numerical data and not a DASHI proof"
    Source.publicAttribution

rashevMoule2006NH3Hamiltonian : Source.AttributedSource
rashevMoule2006NH3Hamiltonian =
  Source.mkDOISource
    "Svetoslav Rashev; David C. Moule"
    "Hamiltonian description and 6D calculations on the ammonia vibrational levels"
    "Journal of Molecular Spectroscopy 235 (2006) 93-103"
    "2006"
    "10.1016/j.jms.2005.10.007"
    "https://doi.org/10.1016/j.jms.2005.10.007"
    Source.academicArticleSource
    "NH3-specific authority for a fully symmetrized 6D vibrational Hamiltonian, inversion potential, intermode couplings and symmetrized vibrational basis; not authority for a DASHI electronic eigenvector"
    Source.publicAttribution

marquardtEtAl2013NH3PES : Source.AttributedSource
marquardtEtAl2013NH3PES =
  Source.mkDOISource
    "Roberto Marquardt; Kenneth Sagui; Jingjing Zheng; Walter Thiel; David Luckhaus; Sergey Yurchenko; Fabio Mariotti; Martin Quack"
    "Global Analytical Potential Energy Surface for the Electronic Ground State of NH3 from High Level ab Initio Calculations"
    "Journal of Physical Chemistry A 117 (2013) 7502-7522"
    "2013"
    "10.1021/jp4016728"
    "https://doi.org/10.1021/jp4016728"
    Source.academicArticleSource
    "NH3-specific authority for a global full-dimensional analytical PES of the lowest adiabatic electronic state fitted to high-level ab initio energies; not a literal DASHI wavefunction"
    Source.publicAttribution

data NH3HamiltonianTerm : Set where
  nuclearKinetic electronicKinetic electronNuclearAttraction
  electronElectronRepulsion nuclearNuclearRepulsion
  rovibrationalKinetic groundElectronicPES inversionPotential
  anharmonicIntermodeCoupling : NH3HamiltonianTerm

canonicalNH3HamiltonianTerms : List NH3HamiltonianTerm
canonicalNH3HamiltonianTerms =
  nuclearKinetic ∷ electronicKinetic ∷ electronNuclearAttraction ∷
  electronElectronRepulsion ∷ nuclearNuclearRepulsion ∷
  rovibrationalKinetic ∷ groundElectronicPES ∷ inversionPotential ∷
  anharmonicIntermodeCoupling ∷ []

record NH3MolecularHamiltonian : Set₁ where
  constructor nh3MolecularHamiltonian
  field
    MolecularState : Set
    OperatorExpression : Set
    symbolicExpression : MolecularState → OperatorExpression
    terms : List NH3HamiltonianTerm
    expressionIsUnevaluated : Bool
    expressionIsUnevaluatedIsTrue : expressionIsUnevaluated ≡ true
    molecularFormula : String
    nuclei : Nat
    electrons : Nat
    vibrationalDegreesOfFreedom : Nat
    pointGroup : String
    molecularHamiltonianAuthority : Source.AttributedSource
    ammoniaHamiltonianAuthority : Source.AttributedSource
    groundStatePESAuthority : Source.AttributedSource
    c3SymmetryCommutationObligation : Set
    hermiticityOrSelfAdjointnessObligation : Set

open NH3MolecularHamiltonian public

canonicalNH3MolecularHamiltonian : NH3MolecularHamiltonian
canonicalNH3MolecularHamiltonian =
  nh3MolecularHamiltonian
    String
    (List NH3HamiltonianTerm)
    (λ _ → canonicalNH3HamiltonianTerms)
    canonicalNH3HamiltonianTerms
    true refl
    "NH3"
    4
    10
    6
    "C3v"
    meyer2002MolecularHamiltonian
    rashevMoule2006NH3Hamiltonian
    marquardtEtAl2013NH3PES
    ⊤
    ⊤

data NH3OccupiedSpinOrbital : Set where
  oneA1Alpha oneA1Beta
  twoA1Alpha twoA1Beta
  oneEXAlpha oneEXBeta
  oneEYAlpha oneEYBeta
  threeA1Alpha threeA1Beta : NH3OccupiedSpinOrbital

canonicalOccupiedSpinOrbitals : List NH3OccupiedSpinOrbital
canonicalOccupiedSpinOrbitals =
  oneA1Alpha ∷ oneA1Beta ∷
  twoA1Alpha ∷ twoA1Beta ∷
  oneEXAlpha ∷ oneEXBeta ∷
  oneEYAlpha ∷ oneEYBeta ∷
  threeA1Alpha ∷ threeA1Beta ∷ []

record NH3OccupationState : Set where
  constructor nh3OccupationState
  field
    stateLabel : String
    orbitalConfiguration : String
    occupiedSpinOrbitals : List NH3OccupiedSpinOrbital
    occupiedSpinOrbitalCount : Nat
    totalElectronCount : Nat
    totalSpinMultiplicity : Nat
    spatialGroundIrrep : Electronic.C3vIrrep
    c3Phase : Electronic.ElectronicC3Phase
    antisymmetrizedDeterminantConvention : String
    sourceElectronicReceipt : Electronic.NeutralElectronicReceipt

open NH3OccupationState public

canonicalNH3OccupationState : NH3OccupationState
canonicalNH3OccupationState =
  nh3OccupationState
    "closed-shell NH3 configuration-state carrier"
    "(1a1)^2(2a1)^2(1e)^4(3a1)^2"
    canonicalOccupiedSpinOrbitals
    10
    10
    1
    Electronic.A1
    Electronic.invariant
    "single closed-shell Slater-determinant occupation convention over named spin-orbitals; spatial orbital functions and numerical coefficients remain external"
    Electronic.canonicalNeutralElectronicReceipt

record HamiltonianWavefunctionBoundary : Set where
  constructor hamiltonianWavefunctionBoundary
  field
    sameObjectSymbolicHamiltonianExpressionPaid : Bool
    sameObjectSymbolicHamiltonianExpressionPaidIsTrue :
      sameObjectSymbolicHamiltonianExpressionPaid ≡ true
    energyValuedHamiltonianOperatorPaid : Bool
    energyValuedHamiltonianOperatorPaidIsFalse :
      energyValuedHamiltonianOperatorPaid ≡ false
    sourceBackedGroundElectronicPESPaid : Bool
    sourceBackedGroundElectronicPESPaidIsTrue :
      sourceBackedGroundElectronicPESPaid ≡ true
    literalOccupationBasisStatePaid : Bool
    literalOccupationBasisStatePaidIsTrue : literalOccupationBasisStatePaid ≡ true
    c3SymmetryAdapterPaid : Bool
    c3SymmetryAdapterPaidIsTrue : c3SymmetryAdapterPaid ≡ true
    numericRealSpaceWavefunctionCoefficientsPaid : Bool
    numericRealSpaceWavefunctionCoefficientsPaidIsFalse :
      numericRealSpaceWavefunctionCoefficientsPaid ≡ false
    numericHamiltonianDiagonalizationPaid : Bool
    numericHamiltonianDiagonalizationPaidIsFalse :
      numericHamiltonianDiagonalizationPaid ≡ false
    symbolicHamiltonianEqualsExactBornOppenheimerSolution : Bool
    symbolicHamiltonianEqualsExactBornOppenheimerSolutionIsFalse :
      symbolicHamiltonianEqualsExactBornOppenheimerSolution ≡ false
    citedPESCreatesWavefunction : Bool
    citedPESCreatesWavefunctionIsFalse : citedPESCreatesWavefunction ≡ false

open HamiltonianWavefunctionBoundary public

canonicalHamiltonianWavefunctionBoundary : HamiltonianWavefunctionBoundary
canonicalHamiltonianWavefunctionBoundary =
  hamiltonianWavefunctionBoundary
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
