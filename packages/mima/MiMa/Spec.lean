import MiMa.Keys

/-!
# `MiMa`: the specification at a glance

MiMa as a bridge between two versions of a library: its keys are what it compares, and a key
covers the linkage queries its comparison reads. A client that stops linking has a footprint query
whose answer changed, so every miss is a coverage gap (no key covers the query) or an abstraction
gap (a key covers it and its comparison passes).

* `MiMa.miss_changes_footprint`: by `Jvm.link_congr`, a client that links on the old library and
  not on the new one has a changed footprint query.
* `MiMa.check_nil_of_mima_nil`: when MiMa reports nothing, every key's comparison passes.

The witnesses (`MiMa.finalField`, `MiMa.shadowField`, `MiMa.ifaceField`,
`MiMa.protectedRemoved`, …) are the gaps filed as scala-garden/mima#993–#996.
-/

-- Each name below must exist: the build fails if a result this page states is renamed or removed.
example := @MiMa.miss_changes_footprint
example := @MiMa.check_nil_of_mima_nil
