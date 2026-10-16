## 2024-05-17 - Avoid Temporary Benchmark Scripts in Commits
**Learning:** Temporary benchmark or scratchpad scripts (e.g., `time_test.py`) used for profiling can inadvertently be committed, polluting the repository.
**Action:** Always delete temporary benchmark scripts immediately after use, or ensure they are added to `.gitignore`. Ensure `git status` or `list_files` reflects a clean state before submitting.
