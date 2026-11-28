# Getting started

Use the Lean version in the repository's [toolchain file](../lean-toolchain) and the dependencies in its [Lake manifest](../lake-manifest.json). From a checkout of the revision you want to study, build the library and run a small periodic Burgers case.

```bash
lake build
lake exe fv1d --model burgers 200 200 0.4
```

The [execution guide](../CFDLean/Exec/README.md) lists the driver arguments and refinement modules. The [FV1D benchmarks](../benchmarks/fv1d/README.md) describe an independent Euler density-wave control. Read the [Lean performance guide](LEAN_PERFORMANCE.md#6-run-lean-under-a-memory-cap) before a local Lean run.

For changes that affect capabilities or imports, regenerate and commit the affected files.

```bash
python3 scripts/generate_capabilities.py
python3 scripts/generate_import_graph.py
```

Run the following validation from the repository root. An agent working without hosted CI uses these same checks on each applicable candidate and records the exact parent, candidate, toolchain, exit statuses and hashes in its review record.

```bash
python3 -m pip install -r requirements-docs.txt
python3 scripts/generate_capabilities.py --check
python3 scripts/generate_import_graph.py --check
python3 scripts/verify.py
lake build
python3 -m mkdocs build --strict
```

See the [contributor workflow](../CONTRIBUTING.md#validation) for the repository's full checks, evidence conventions and release validation.
