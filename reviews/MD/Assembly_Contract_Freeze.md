# Independent freeze of the fixed-mesh assembly contract

The independent reviewer approved **MD-C, MD-K and MD-U** as written at `0e1f9fbb9602a89daf6f9ce371f085ef3e8cb3a1`,
parent `15bc99d29bc7f97f15fa678f4d88d6093283d84f`. The [contract](../../specifications/MD-fixed-mesh-assembly-proposal.md)
has SHA-256 `5b6bce040efd03297411149d9e93497900f07e4aeea853156e17aff765806b14`. The reviewer found no mathematical
change necessary and conditioned the freeze on clearing the failing hosted job or demonstrating that it was unrelated.

GitHub's [check-run annotation](https://api.github.com/repos/rois1995/CFD_Lean/check-runs/140950639344/annotations)
identified an account billing or Actions spending-limit block. The [job](https://github.com/rois1995/CFD_Lean/actions/runs/46135777547/job/140950639344)
reported `steps: []`. The runner never started. This satisfies the reviewer's infrastructure condition. The hosted check
retains its failure status. The [proposal PR](https://github.com/rois1995/CFD_Lean/pull/68) carries the local replay record.

The freeze covers signed incidence assembly, compatible constant-state flux with per-cell closure, and a single common
Forward Euler amount balance with positive fixed cell measures. In particular, each interior transfer is evaluated in
one orientation and its negative enters the second cell. The hand-computed two-triangle check distinguishes cellwise
errors that the global sum hides. Array refinement, Euler, machine arithmetic and reconstruction require later work.
The [standing authorization](../Standing_Authorization.md) permits implementation. PR B has a separate implementation review.
