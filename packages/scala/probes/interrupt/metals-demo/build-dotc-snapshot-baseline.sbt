// Baseline for the dotc session spike: the same snapshot of compiler/src/dotty/tools/dotc (d168df2a76,
// 478 files), with the released Scala 3.10.0 as both the Scala version (so Metals uses the released
// presentation compiler) and the library the sources are typed against. Compare with ../dotc-session-dotc.
scalaVersion := "3.10.0"
libraryDependencies += "org.scala-lang" %% "scala3-compiler" % "3.10.0"
scalacOptions ++= Seq("-Yexplicit-nulls", "-Wsafe-init", "-language:implicitConversions")
