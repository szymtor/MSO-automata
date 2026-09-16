# Registered final submission — lax-146103

Updated 2026-09-16. The user authorized final publication of the six current
Lean 4.33 submissions and normalization of AI author credits to GPT, retaining
version numbers. This supersedes earlier keep-draft restrictions for this release.

- Registered and citable: https://laxarchive.org/lax-146103/
- Frozen source: `a850aa03d9cb3bff8aec3990269c99942ac56aff` on `lean-4.33`.
- The release changes only `manifest.yaml` relative to the previous accepted
  Archive source; Lean sources and the previously replayed proofs are unchanged.
- Fresh full local Lax compilation and statement inspection passed. The Archive
  independently verified the author-only diff and reused its validated capture.
- After registration, the refreshed Archive record was verified against the
  exact source and capture provenance, GPT author credits, all concept source
  text, proof counts and complete proof closure, and registered dependency pins.
- Evidence: `../migration-tools/finalize-foundations-verification.log` and
  the corresponding `finalize-*-build.log`, `-submit.log`, and `-register.log`.

No further publication is needed. Downstream submissions must pin the frozen
source above. Local status documentation may advance after that immutable commit.

## Earlier history

# Lean 4.33 draft migration

Original draft: lax-52. New local draft: lax-146103.
User authorized a separate draft with a link to the original, without supersedes.
Sources are copied from the original published commit; namespaces, toolchain,
mathlib and dependency names have been updated. Dependency commit pins for
other new drafts are pending their validation and publication. Full Lean 4.33 build and independent kernel replay passed (35s):
7 concepts and 4 annotated proofs. Published as a new replaceable draft at https://laxarchive.org/lax-146103/
from b7b157e93741492b33a0fa84ec76e24a571e2a98 (issue 111).
Archive rebuild passed in 3m36s; public record publication succeeded.
No registration performed. Concept code is unchanged apart from namespace renaming.
Compatibility edits in four proof modules restore dependent-index elaboration
and use simpa using! where the prior proof relied on definition unfolding.
Retain the original helper API for downstream tree-automata reuse; the new
linter reports 20 unused-helper warnings.

Next: downstream tree-automata port pins this published commit.

## Historical record from the original (not validation of this port)

