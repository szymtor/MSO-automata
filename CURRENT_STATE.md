# Lean 4.33 draft migration

Original draft: lax-52. New local draft: lax-146103.
User authorized a separate draft with a link to the original, without supersedes.
Sources are copied from the original published commit; namespaces, toolchain,
mathlib and dependency names have been updated. Dependency commit pins for
other new drafts are pending their validation and publication. Full Lean 4.33 build and independent kernel replay passed (35s):
7 concepts and 4 annotated proofs. No archive submission or registration
performed. Concept code is unchanged apart from namespace renaming.
Compatibility edits in four proof modules restore dependent-index elaboration
and use simpa using! where the prior proof relied on definition unfolding.
Retain the original helper API for downstream tree-automata reuse; the new
linter reports 20 unused-helper warnings.

Next: push lean-4.33 and submit the validated draft, then repin tree automata.

## Historical record from the original (not validation of this port)

