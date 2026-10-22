// A sample project for the dotc session spike (retronym/scala3#68) under VS Code + Metals:
// the patched compiler, published locally from the scratch worktree with
//   sbt "scala3-bootstrapped/publishLocal" "scala3-presentation-compiler/publishLocal"
// Metals fetches the presentation compiler of this Scala version through coursier, which
// resolves ~/.ivy2/local. -Yinteractive-log prints one line per request to the Metals log
// (View > Output > Metals, or .metals/metals.log); -Yno-targeted-requests turns targeting off.
scalaVersion := "3.10.2-RC1-bin-SNAPSHOT"
scalacOptions ++= Seq("-Yinteractive-log")
