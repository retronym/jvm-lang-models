// expect: cycle cycle cycle
// kind: true
// an alias whose expansion contains itself
trait T { type A = List[A] }
