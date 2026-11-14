from __future__ import annotations


def _validate_action_table(states, actors, table, label):
    state_set = set(states)
    if set(table) != set(actors):
        raise ValueError(f"{label}: actor keys do not match declared actors")
    for actor in actors:
        row = table[actor]
        if set(row) != state_set:
            raise ValueError(
                f"{label}/{actor}: action row must be total on declared states"
            )
        bad = {out for out in row.values() if out not in state_set}
        if bad:
            raise ValueError(
                f"{label}/{actor}: outputs leave declared carrier: {sorted(bad)}"
            )


def compare_actions(
    states,
    residual_states,
    removed_state,
    actors,
    monster_action,
    f4_action,
):
    """Compare two supplied finite actions on one declared 54->53-style carrier.

    This is an execution diagnostic only. Even exact agreement on every supplied
    actor/state does not prove classical F4 recognition: the formal same-action
    theorem still requires the independently owned Albert/Jordan action,
    actor-map provenance, removed-invariant compatibility and residual
    restriction on the same object.
    """

    states = list(states)
    residual_states = list(residual_states)
    actors = list(actors)
    state_set = set(states)
    residual_set = set(residual_states)

    if removed_state not in state_set:
        raise ValueError("removed_state must lie in carrier")
    if removed_state in residual_set:
        raise ValueError("removed_state must not lie in residual carrier")
    if not residual_set <= state_set:
        raise ValueError("residual carrier must be a subset of carrier")

    _validate_action_table(states, actors, monster_action, "monster")
    _validate_action_table(states, actors, f4_action, "f4")

    mismatches = []
    residual_mismatches = []
    for actor in actors:
        for state in states:
            monster_image = monster_action[actor][state]
            f4_image = f4_action[actor][state]
            if monster_image != f4_image:
                mismatch = (actor, state, monster_image, f4_image)
                mismatches.append(mismatch)
                if state in residual_set:
                    residual_mismatches.append(mismatch)

    monster_removed = all(
        monster_action[actor][removed_state] == removed_state
        for actor in actors
    )
    f4_removed = all(
        f4_action[actor][removed_state] == removed_state
        for actor in actors
    )
    monster_residual_closed = all(
        monster_action[actor][state] in residual_set
        for actor in actors
        for state in residual_states
    )
    f4_residual_closed = all(
        f4_action[actor][state] in residual_set
        for actor in actors
        for state in residual_states
    )

    return {
        "carrier_size": len(states),
        "residual_size": len(residual_states),
        "actor_count": len(actors),
        "action_mismatch_count": len(mismatches),
        "residual_mismatch_count": len(residual_mismatches),
        "action_mismatches": mismatches,
        "residual_mismatches": residual_mismatches,
        "removed_invariant_preserved_monster": monster_removed,
        "removed_invariant_preserved_f4": f4_removed,
        "removed_invariant_preserved_both": monster_removed and f4_removed,
        "residual_closed_monster": monster_residual_closed,
        "residual_closed_f4": f4_residual_closed,
        "residual_closed_both": monster_residual_closed and f4_residual_closed,
        "extensionally_equal_on_supplied_actors": len(mismatches) == 0,
        # These remain fail-closed even if the supplied tables agree exactly.
        "classical_f4_recognition": False,
        "mechanism_identity": False,
        "phenomenal_identity": False,
    }
