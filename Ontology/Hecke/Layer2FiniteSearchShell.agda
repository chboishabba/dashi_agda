module Ontology.Hecke.Layer2FiniteSearchShell where

------------------------------------------------------------------------
-- Thin shell: no heavy histogram imports, only names and structure.

record PairTarget : Set₁ where
  field
    SectorSeparates : Set
    PackageSeparates : Set
    CorrelationSeparates : Set

open PairTarget public

record FiniteSearchShell : Set₁ where
  field
    first : PairTarget
    second : PairTarget
    third : PairTarget

open FiniteSearchShell public

------------------------------------------------------------------------
-- Postulated current Layer 2 targets.

postulate
  FirstPairSectorSeparates : Set
  FirstPairTriadPackageSeparates : Set
  FirstPairCorrelationSeparates : Set

  SecondPairSectorSeparates : Set
  SecondPairTriadPackageSeparates : Set
  SecondPairCorrelationSeparates : Set

  ThirdPairSectorSeparates : Set
  ThirdPairTriadPackageSeparates : Set
  ThirdPairCorrelationSeparates : Set

------------------------------------------------------------------------
-- Fixed finite search plans.

firstPairPlan : PairTarget
firstPairPlan = record
  { SectorSeparates = FirstPairSectorSeparates
  ; PackageSeparates = FirstPairTriadPackageSeparates
  ; CorrelationSeparates = FirstPairCorrelationSeparates
  }

secondPairPlan : PairTarget
secondPairPlan = record
  { SectorSeparates = SecondPairSectorSeparates
  ; PackageSeparates = SecondPairTriadPackageSeparates
  ; CorrelationSeparates = SecondPairCorrelationSeparates
  }

thirdPairPlan : PairTarget
thirdPairPlan = record
  { SectorSeparates = ThirdPairSectorSeparates
  ; PackageSeparates = ThirdPairTriadPackageSeparates
  ; CorrelationSeparates = ThirdPairCorrelationSeparates
  }

------------------------------------------------------------------------
-- Final bounded current-scope search shell.

finiteLayer2SearchShell : FiniteSearchShell
finiteLayer2SearchShell = record
  { first = firstPairPlan
  ; second = secondPairPlan
  ; third = thirdPairPlan
  }
