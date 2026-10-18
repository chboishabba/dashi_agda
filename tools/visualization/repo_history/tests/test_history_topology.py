import dashi_repo_history.history_topology as topology
from dashi_repo_history.history_topology import derive_branch_episodes
from dashi_repo_history.model import CommitRecord


def test_branch_episode_recovers_fork_base_and_both_paths():
    commits = [
        CommitRecord("A", 0, ()),
        CommitRecord("B", 1, ("A",)),
        CommitRecord("C", 2, ("B",)),
        CommitRecord("D", 3, ("B",)),
        CommitRecord("E", 4, ("C",)),
        CommitRecord("F", 5, ("D",)),
        CommitRecord("M", 6, ("E", "F")),
    ]

    episodes = derive_branch_episodes(commits)

    assert len(episodes) == 1
    episode = episodes[0]
    assert episode.fork_base == "B"
    assert episode.left_tip == "E"
    assert episode.right_tip == "F"
    assert episode.merge_commit == "M"
    assert episode.left_path == ("B", "C", "E")
    assert episode.right_path == ("B", "D", "F")


def test_branch_episode_derivation_only_traces_requested_merges(monkeypatch):
    commits = [
        CommitRecord("A", 0, ()),
        CommitRecord("B", 1, ("A",)),
        CommitRecord("C", 2, ("B",)),
        CommitRecord("D", 3, ("B",)),
        CommitRecord("E", 4, ("C",)),
        CommitRecord("F", 5, ("D",)),
        CommitRecord("M1", 6, ("E", "F")),
        CommitRecord("G", 7, ("E",)),
        CommitRecord("H", 8, ("F",)),
        CommitRecord("M2", 9, ("G", "H")),
    ]
    original = topology.nearest_common_ancestor
    calls = []

    def record_call(left, right, parents):
        calls.append((left, right))
        return original(left, right, parents)

    monkeypatch.setattr(topology, "nearest_common_ancestor", record_call)

    episodes = derive_branch_episodes(commits, merge_commits={"M2"})

    assert [episode.merge_commit for episode in episodes] == ["M2"]
    assert calls == [("G", "H")]
