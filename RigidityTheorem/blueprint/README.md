# RigidityTheorem Blueprint

This directory contains a lightweight Lean-style blueprint for the current
`Approximate_Rigidity` development.

The source files live in `src/`. The blueprint is organized around Chapter 11
of the QIC 890 notes and the Lean implementation in
`RigidityTheorem/Approximate_Rigidity`.

Typical local build commands:

```bash
cd RigidityTheorem/blueprint/src
latexmk -pdf print.tex
```

For an HTML build with a full blueprint toolchain installed, `web.tex` and
`plastex.cfg` provide the corresponding entry point.

From the repository root, you can also use the wrapper script:

```bash
bash scripts/blueprint.sh build-web
bash scripts/blueprint.sh serve
bash scripts/blueprint.sh checkdecls
```

This wrapper uses the local `plastex`, `latexmk`, and `checkdecls` commands
directly so it works with this repo's current layout, where the blueprint
sources live in `RigidityTheorem/blueprint`.

This directory intentionally contains source files only; generated `web/`
artifacts and PDFs can be built locally when needed.
