from dashi_repo_history.history_axis import temporal_history_layout


def test_time_is_vertical_and_branch_lane_is_horizontal():
    commits = [
        {"commit": "A", "timestamp": 100, "parents": []},
        {"commit": "B", "timestamp": 200, "parents": ["A"]},
        {"commit": "C", "timestamp": 300, "parents": ["B"]},
        {"commit": "D", "timestamp": 250, "parents": ["B"]},
        {"commit": "M", "timestamp": 400, "parents": ["C", "D"]},
    ]

    layout = temporal_history_layout(commits)

    assert layout.positions["A"][1] < layout.positions["B"][1]
    assert layout.positions["B"][1] < layout.positions["C"][1]
    assert layout.positions["D"][0] != layout.positions["C"][0]
    assert layout.positions["M"][0] == layout.positions["C"][0]


def test_timestamp_gap_controls_vertical_gap():
    commits = [
        {"commit": "A", "timestamp": 0, "parents": []},
        {"commit": "B", "timestamp": 10, "parents": ["A"]},
        {"commit": "C", "timestamp": 1000, "parents": ["B"]},
    ]

    layout = temporal_history_layout(commits)
    early_gap = layout.positions["B"][1] - layout.positions["A"][1]
    late_gap = layout.positions["C"][1] - layout.positions["B"][1]

    assert late_gap > early_gap * 50


def test_axis_emits_real_date_labels():
    commits = [
        {"commit": "A", "timestamp": 0, "parents": []},
        {"commit": "B", "timestamp": 86400, "parents": ["A"]},
    ]

    layout = temporal_history_layout(commits)
    labels = [tick.label for tick in layout.ticks]

    assert labels == ["1970-01-01", "1970-01-02"]


def test_equal_timestamps_are_only_visually_tie_broken():
    commits = [
        {"commit": "A", "timestamp": 100, "parents": []},
        {"commit": "B", "timestamp": 100, "parents": ["A"]},
    ]

    layout = temporal_history_layout(commits)
    assert layout.positions["A"][1] != layout.positions["B"][1]
    assert abs(layout.positions["A"][1] - layout.positions["B"][1]) < 0.1
