# Sprint 159 Criteria Inventory

- SUPPORT_NOT_EXHAUSTIVE rows: `5`
- CLOSED_SCOPED_CLASS rows: `1`
- MechanismExhaustionForFullClayNS: `False`
- fullClay: `False`

| criterion_id | criterion_name | status |
| --- | --- | --- |
| bkm_continuation | BKM continuation | SUPPORT_NOT_EXHAUSTIVE |
| prodi_serrin_ladyzhenskaya | Prodi-Serrin/Ladyzhenskaya | SUPPORT_NOT_EXHAUSTIVE |
| escauriaza_seregin_sverak_critical_l3 | Escauriaza-Seregin-Sverak critical L3/L3inf-style criterion | SUPPORT_NOT_EXHAUSTIVE |
| caffarelli_kohn_nirenberg_partial_regularity | Caffarelli-Kohn-Nirenberg partial regularity | SUPPORT_NOT_EXHAUSTIVE |
| koch_tataru_small_data_critical_space | Koch-Tataru small-data critical-space | SUPPORT_NOT_EXHAUSTIVE |
| symmetric_hou_luo_sprint157_158_closure | Symmetric Hou-Luo Sprint157/158 closure | CLOSED_SCOPED_CLASS |

## O/R/C/S/L/P/G/F

- O: Worker 4 owns the Sprint159 criteria inventory emitter.
- R: Inventory known partial regularity and singularity-control criteria without promoting full Clay NS.
- C: Python stdlib emitter writes criteria rows to JSON, CSV, Markdown, and manifest.
- S: Class-specific symmetric Hou-Luo closure is available; general NS mechanism exhaustion is absent.
- L: criterion support -> non-exhaustive inventory guard -> scoped symmetric class closure -> full Clay flags false.
- P: Use this inventory as evidence of partial support and scoped closure boundaries.
- G: Every general criterion row must remain support-only; only the symmetric class row is closed in scope.
- F: MechanismExhaustionForFullClayNS remains false for full 3D Navier-Stokes.
