# Proof Folding Style

To keep theorem and lemma statements visible while making proofs easy to fold in
VS Code, this project uses a simple convention:

```lean
theorem some_result
    (h1 : ...)
    (h2 : ...) :
    goal := by
  ...
```

Guidelines:

- Put the full statement above `:= by`.
- Start the proof on the next indented line.
- Prefer one declaration per proof block instead of packing many local proofs into a single long term expression.
- Keep long proofs inside `by` blocks rather than inline proof terms when readability matters.

With the workspace settings in [.vscode/settings.json](/Volumes/Files/Research_New_chapter/RigidityTheorem/.vscode/settings.json), you can then fold proofs cleanly using VS Code's normal folding commands:

- `Fold`
- `Fold All`
- `Unfold All`

This does not hide proofs semantically in Lean; it just makes the editor view much closer to a “statements first” outline.
