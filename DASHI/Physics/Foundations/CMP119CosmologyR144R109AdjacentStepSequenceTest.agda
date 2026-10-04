{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR144R109AdjacentStepSequenceTest where

import DASHI.Physics.Foundations.CMP119CosmologyR144R109AdjacentStepSequenceExact as Subject

open import Agda.Builtin.Bool using (Bool; true)

adjacentSignedStepsSuffice : Bool
adjacentSignedStepsSuffice = Subject.adjacentSignedStepIdentityIsSufficientWithOneEndpoint
