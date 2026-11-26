# QPainleve Challenges

Each challenge is a single file `Challenge/<Name>.lean` with a configuration
`comparator/<Name>.json` for [`lake comparator`](https://github.com/leanprover/comparator), which
is part of Lake since Lean v4.35.0.

A challenge file is the trusted specification: it imports only Tau Ceti and Mathlib, defines
everything its statement uses, and states the challenge theorem with `sorry`. Reference solutions
can use the public API of [QPainleve](https://github.com/q-painleve-lean/QPainleve). The Lake
configuration and manifest pin the library and its dependencies.

To submit a solution, copy the challenge file to `Solution/<Name>.lean` and replace the `sorry` by
a proof. The proof may import anything, including `QPainleve`. If extra imports affect how the
copied definitions elaborate, keep the definitions and their original imports in a separate
solution module. Run comparator from a clean checkout (no `.lake` directory) with `bubblewrap`
installed:

```sh
lake comparator --config comparator/<Name>.json
```

Comparator checks that every theorem in `theorem_names` has the same statement in the solution as
in the challenge, uses only the permitted axioms, and is accepted by the kernel.

GitHub Actions builds both libraries on pull requests. Run the **Comparator** workflow on
`main` to verify the published solution against the published challenge and configuration. The
full replay can require more memory than the standard runner. Select a larger Ubuntu runner
label when one is available.

## Challenges

* `SignedClusterModularGroup`: for every toric presentation whose surface satisfies the
  target-pair conditions, the signed cluster modular group of its seed is isomorphic to the group
  of signed boundary isometries of its Picard lattice.
  The [solution](Solution/SignedClusterModularGroup.lean) uses the cyclic-ray comparison in
  `QPainleve.SignedClusterModularGroup.Realization.Presentation.CyclicRays`.
