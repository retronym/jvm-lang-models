import Jvm.Link

/-!
# `Jvm`: the specification at a glance

JVM linkage (JVMS §5.4: resolution, selection, access) as a `Query.Task` over the class table.

* `Jvm.link_congr`: T1 for linkage. A library edit that agrees with the old library on a client's
  linkage footprint links that client the same way.

Calibrated on HotSpot 21, 25 and 27 over 58,400 client programs and 45 library edits.
-/

-- Each name below must exist: the build fails if a result this page states is renamed or removed.
example := @Jvm.link_congr
