module DASHI.Biology.IITJFineD4H3RadicalSourceH6Exact where

------------------------------------------------------------------------
-- Source reuse: Monster3BFiniteHeisenbergCentralExtensionExact owns H6.
-- This implements a SAME-MODEL D4-stable H3 x C3^2 subcarrier; it is
-- neither the former extraspecial H4 nor a literal Monster 3B action.
-- Kernel/typecheck receipt for this new source is NOT yet supplied.
------------------------------------------------------------------------
open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; zer)
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H6

record SourceD4EightCentre : Set where
  constructor sourceD4EightCentre
  field
    centre tE tC bE bC XE YE XC YC : Trit
open SourceD4EightCentre public

-- Three Heisenberg pairs (tC,tE),(XC,XE),(YC,YE), with
-- unpaired central bE,bC; six-pair standard H6 source law is reused.
embedInH6 : SourceD4EightCentre → H6.Heisenberg6
embedInH6 (sourceD4EightCentre c te tc be bc xe ye xc yc) =
  H6.heisenberg6
    (H6.symplectic12
      (G.x6 tc zer zer xc yc zer)
      (G.x6 te be bc xe ye zer)) c

projectFromH6 : H6.Heisenberg6 → SourceD4EightCentre
projectFromH6
  (H6.heisenberg6 (H6.symplectic12
    (G.x6 tc ta tb xc yc td)
    (G.x6 te be bc xe ye md)) c) =
  sourceD4EightCentre c te tc be bc xe ye xc yc

projectEmbed : (s : SourceD4EightCentre) →
  projectFromH6 (embedInH6 s) ≡ s
projectEmbed (sourceD4EightCentre c te tc be bc xe ye xc yc) = refl

sourceProduct : SourceD4EightCentre → SourceD4EightCentre → SourceD4EightCentre
sourceProduct a b =
  projectFromH6 (H6.compose (embedInH6 a) (embedInH6 b))

-- The sourced zero-tail slot constraints are closed under the already
-- implemented H6 compose. This equality should reduce definitionally
-- via existing finite F3 tables (pending Agda kernel admission).
embeddedProduct : (a b : SourceD4EightCentre) →
  embedInH6 (sourceProduct a b)
  ≡ H6.compose (embedInH6 a) (embedInH6 b)
embeddedProduct
  (sourceD4EightCentre c te tc be bc xe ye xc yc)
  (sourceD4EightCentre d te2 tc2 be2 bc2 xe2 ye2 xc2 yc2) = refl

record Triple : Set where
  constructor triple
  field first second third : Trit
open Triple public

record RadicalPair : Set where
  constructor radicalPair
  field radicalFirst radicalSecond : Trit
open RadicalPair public

record H3TimesC3Squared : Set where
  constructor h3TimesC3Squared
  field
    translation3 : Triple
    modulation3 : Triple
    phase3 : Trit
    centralRadical2 : RadicalPair
open H3TimesC3Squared public

toH3TimesC3Squared : SourceD4EightCentre → H3TimesC3Squared
toH3TimesC3Squared (sourceD4EightCentre c te tc be bc xe ye xc yc) =
  h3TimesC3Squared (triple tc xc yc) (triple te xe ye)
    c (radicalPair be bc)

fromH3TimesC3Squared : H3TimesC3Squared → SourceD4EightCentre
fromH3TimesC3Squared
  (h3TimesC3Squared (triple tc xc yc) (triple te xe ye)
    c (radicalPair be bc)) =
  sourceD4EightCentre c te tc be bc xe ye xc yc

fromTo : (s : SourceD4EightCentre) →
  fromH3TimesC3Squared (toH3TimesC3Squared s) ≡ s
fromTo (sourceD4EightCentre c te tc be bc xe ye xc yc) = refl

toFrom : (h : H3TimesC3Squared) →
  toH3TimesC3Squared (fromH3TimesC3Squared h) ≡ h
toFrom
  (h3TimesC3Squared (triple tc xc yc) (triple te xe ye)
    c (radicalPair be bc)) = refl

-- Finite Python separately validates the concrete source D4 product action.
-- The H3 group laws follow by reusing the existing H6 group owner, rather
-- than silently promoting this source-written chart to a new kernel theorem.
record AdmissionBoundary : Set where
  constructor admissionBoundary
  field
    originalH6SourceReused : Bool
    concreteSource8CarrierConstructed : Bool
    sourceIntoH6ProductHomSourceWritten : Bool
    H3TimesC3SquaredTwoSidedCodecSourceWritten : Bool
    originalGaugeFourOneFourToCharacterMapKernelProved : Bool
    concreteD4AutomorphismAgdaKernelChecked : Bool
    universalD4RankBoundAgdaKernelChecked : Bool
    actualMonsterNormalizerRepresentationIdentified : Bool

currentBoundary : AdmissionBoundary
currentBoundary = admissionBoundary true true true true false false false false
