#!/usr/bin/env bash
set -euo pipefail

FILES=(
  DASHI/Moonshine/JInvariant369SignedSSPFRACTRANPhaseFibreExact.agda
  DASHI/Moonshine/JInvariant369SSPLevelDihedralIntertwinerExact.agda
  DASHI/Moonshine/JInvariant369JointFibredObserverExact.agda
  DASHI/Moonshine/JInvariant369JointFibreBifiltrationExact.agda
  DASHI/Moonshine/JInvariant369CanonicalInterpretationExact.agda
)

for file in "${FILES[@]}"; do
  echo "[j369-joint] checking ${file}"
  agda -i . "${file}"
done

grep -q 'signedSpectralConjugationCannotEqualLevel3Translation'   DASHI/Moonshine/JInvariant369SignedSSPFRACTRANPhaseFibreExact.agda
grep -q 'sspCycleIntertwinesLevel3Translation'   DASHI/Moonshine/JInvariant369SSPLevelDihedralIntertwinerExact.agda
grep -q 'sspAntipodeIntertwinesLevel3Inversion'   DASHI/Moonshine/JInvariant369SSPLevelDihedralIntertwinerExact.agda
grep -q 'signedMagnitudeCannotFactorThroughLevel3'   DASHI/Moonshine/JInvariant369SSPLevelDihedralIntertwinerExact.agda
grep -q 'canonicalJoint369DihedralLaw'   DASHI/Moonshine/JInvariant369JointFibredObserverExact.agda
grep -q 'level27CannotFactorThroughBase'   DASHI/Moonshine/JInvariant369JointFibredObserverExact.agda
grep -q 'coarseningCommutesWithTranslation'   DASHI/Moonshine/JInvariant369JointFibreBifiltrationExact.agda
grep -q 'oldRelational369HorizonEqualsPrincipalLevelTower : Bool'   DASHI/Moonshine/JInvariant369JointFibreBifiltrationExact.agda

echo "[j369-joint] OK"
