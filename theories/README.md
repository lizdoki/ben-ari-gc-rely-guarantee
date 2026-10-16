# Theories

Start with `GC_Results.thy`: it restates the main results, each with the thesis sentence it
corresponds to and where its proof is.

| Folder | What it shows | Thesis |
|---|---|---|
| `0_Framework` | rely/guarantee in general: the parallel rule and the VDM rules, proved sound | §2.2, App. B.1 |
| `1_Specifications` | Part 1: the Collector's and the Mutator's specifications, and Collector ∥ Mutator for any processes meeting them | §4.2–4.6 |
| `2a_Collector` | Part 2: the Collector's code meets its specification | §4.7–4.8 |
| `2b_Mutator` | Part 2: the Mutator's code meets its specification | §4.6 |
| `3_System` | Part 3: the two together, for the code | §4.5.5 |

Each folder has a README saying what is in it and the order to read it.
