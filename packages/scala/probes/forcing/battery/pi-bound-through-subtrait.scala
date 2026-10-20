// expect: cycle cycle ok
// kind: spurious
// an abstract type's bound through a subtrait's alias of it
trait A { type T <: B#U }
trait B extends A { type U = T }
