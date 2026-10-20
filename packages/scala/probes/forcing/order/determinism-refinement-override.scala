// From scala/scala's DeterminismTest.testRefinementTypeOverride: a control.
// file: a.scala
class Global
trait Analyzer extends StdAttachments { val global: Global }
trait Context { val universe: Global }
trait StdAttachments {
  self: Analyzer =>
  type UnaffiliatedMacroContext = Context
  type MacroContext = UnaffiliatedMacroContext { val universe: self.global.type }
}
// file: b.scala
class Macros {
  self: Analyzer =>
  def foo = List.apply[MacroContext]()
}
