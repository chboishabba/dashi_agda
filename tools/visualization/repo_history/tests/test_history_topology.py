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
