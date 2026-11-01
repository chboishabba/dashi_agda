# Diagrams Index

Date: `2026-06-10`
Declared surface level: `router`

This directory contains diagram sources and rendered assets. These are support
surfaces for navigation and exposition, not canonical theorem text.

Rendered Agda dependency graphs currently checked in here:

- `NSPaper1ClayTargetReceipt.svg`
- `YMPaper3ClayTargetReceipt.svg`
- `UnifiedPhysicsTheorem.svg`

They can be regenerated with `./scripts/render_agda_dependency_graph.sh <module>`.

Canonical interpretive-stack diagram source:

- `TaoQiPolarityMetasystem.puml`
  This is the normalized textual metasystem view for the Tao -> symbol
  geometry -> yin/yang -> Betti support -> Qi -> polarity/phase/field stack.
  It is a
  governance/support diagram, not a promoted theorem surface.

Publication-routing smoke checks:

- `python scripts/check_diagram_reproducibility.py`
- `python scripts/check_publication_readiness.py`
