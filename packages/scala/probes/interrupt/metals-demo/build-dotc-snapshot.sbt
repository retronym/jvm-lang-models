// The dotc session spike on the compiler's own sources: a snapshot of compiler/src/dotty/tools/dotc at
// d168df2a76 (478 files), typed against the published patched compiler and its dependencies. The same
// package as the compiler jar on the classpath: the sources shadow the jar's classes for the file being
// typed, as in the x-ray. -Yinteractive-log prints one line per request to the Metals log.
scalaVersion := "3.10.2-RC1-bin-SNAPSHOT"
libraryDependencies += "org.scala-lang" %% "scala3-compiler" % "3.10.2-RC1-bin-SNAPSHOT"
scalacOptions ++= Seq("-Yexplicit-nulls", "-Wsafe-init", "-language:implicitConversions", "-Yinteractive-log")
