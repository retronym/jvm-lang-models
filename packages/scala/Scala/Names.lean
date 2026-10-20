import ScalaTypes.Syntax
import Scala.Md5
/-!
# Binary names of classes and objects (Track N)

What a class, trait, case class or object that is not local or anonymous is called on the JVM, in
scalac 2.12 and 2.13 and dotc 3: the classfile's name, and the class's own `InnerClasses` entry
(outer class and simple name), which is what `javac` and reflection read back.

Neither specification says. JLS §13.1 fixes `Outer$Inner` for a Java member class; the SLS has no
binary names. The compilers agree on a scheme read from their sources (scalac's
`Symbol.javaBinaryNameString`, `Flatten`, `StdNames.compactify`, `NameTransformer`; dotc's
`SymDenotation.fullNameSeparated`, `NameOps.compactify`, `NameTransformer`,
`Desugar.packageObjectName`):

* a name is encoded: an operator character becomes `$plus` and the like, any other character that
  cannot be part of a Java identifier `$uXXXX` (`encode`);
* a member's flat name is its owner's flat name, `$`, and its own, where the owner's is taken
  without the module suffix (a member of `object O` is `O$C`, not `O$$C`); a package is a path, and
  a package object is an object called `package`;
* a flat name over a length limit is shortened to its first and last quarter around the MD5 of the
  whole (`compact`); the limit differs by version (`maxLen`) and a top-level name is never
  shortened;
* an object's module class adds `$`; a top-level object without a companion class also gets a
  mirror class without it; a case class has a module class even when no companion is written;
* Scala 3 wraps the top-level definitions that cannot stand alone (a `def`, an `implicit class`) in
  an object `<file>$package`, named after the source file.

`namesSpace` enumerates programs; `packages/scala/probes/names.py` compiles them and compares the
classfiles with `entries`.

Out of scope: local, anonymous and lambda classes and their numbering, members, specialisation.
-/

namespace Scala.Names

/-! ## Encoding -/

/-- The operator characters and their codes (`NameTransformer.enterOp`, the same in scalac and
dotc). -/
def opCode : Char → Option String
  | '~' => some "$tilde" | '=' => some "$eq" | '<' => some "$less" | '>' => some "$greater"
  | '!' => some "$bang" | '#' => some "$hash" | '%' => some "$percent" | '^' => some "$up"
  | '&' => some "$amp" | '|' => some "$bar" | '*' => some "$times" | '/' => some "$div"
  | '+' => some "$plus" | '-' => some "$minus" | ':' => some "$colon" | '\\' => some "$bslash"
  | '?' => some "$qmark" | '@' => some "$at"
  | _ => none

/-- `Character.isJavaIdentifierPart`, for ASCII; a non-ASCII character is taken for a letter (the
spaces only use letters there). -/
def javaIdentPart (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '$' || c.toNat ≥ 0x80

private def hex4 (n : Nat) : String :=
  let d (k : Nat) : Char := "0123456789ABCDEF".toList[(n / 16 ^ k) % 16]!
  String.ofList [d 3, d 2, d 1, d 0]

/-- `NameTransformer.encode`.

Spec: unspecified SLS §1.1: how an identifier that is not a Java identifier is spelled on the JVM;
calibrated against scalac 2.12.21, 2.13.18 and dotc 3.9.0 by `packages/scala/probes/names.py` (314
programs for Scala 2, 332 for Scala 3). -/
def encode (s : String) : String :=
  String.join (s.toList.map fun c =>
    match opCode c with
    | some code => code
    | none => if javaIdentPart c then c.toString else s!"$u{hex4 c.toNat}")

/-! ## Shortening -/

/-- The longest flat name kept as it is. scalac 2.12: `-Xmax-classfile-name` (255) less 8 for
`$.class` and a spare; 2.13: 240 less 7; dotc: 240 less 6 (the `min` with the second bound in 2.12
and dotc never binds). -/
def maxLen : Dialect → Nat
  | .s212 => 247
  | .s213 => 233
  | .s3 => 234

/-- `compactify`: a quarter of the limit from each end, around the MD5 of the whole between
`$$$$` markers.

Spec: unspecified JLS §13.1: a length limit on binary names, and how a longer one is shortened;
calibrated against scalac 2.12.21, 2.13.18 and dotc 3.9.0 by `packages/scala/probes/names.py` (314
programs for Scala 2, 332 for Scala 3). -/
def compact (dl : Dialect) (s : String) : String :=
  if s.length ≤ maxLen dl then s
  else
    let e := maxLen dl / 4
    String.ofList (s.toList.take e) ++ "$$$$" ++ Md5.ofString s ++ "$$$$" ++
      String.ofList (s.toList.drop (s.length - e))

/-! ## Definitions and their names -/

/-- A case class has a companion module class even when none is written. -/
inductive K | cls | trt | obj | ccls
  deriving DecidableEq, Repr

/-- A class-like definition with its source name (not encoded) and members. -/
inductive Node
  | mk (name : String) (kind : K) (body : List Node)
  deriving Repr

def Node.name : Node → String | .mk n _ _ => n
def Node.kind : Node → K | .mk _ k _ => k
def Node.body : Node → List Node | .mk _ _ b => b

/-- A source file: its package, its file name (without `.scala`) and its definitions. -/
structure Prog where
  pkg : List String := []
  file : String := "A"
  tops : List Node := []
  /-- `package object <last of pkg>` with these members. -/
  pkgObj : Option (List Node) := none
  /-- Scala 3: a top-level `def`, which goes in `<file>$package`. -/
  topDef : Bool := false
  /-- Scala 3: top-level implicit classes, which go in `<file>$package` too. -/
  implicits : List String := []
  /-- Only Scala 3 compiles it. -/
  only3 : Bool := false
  deriving Repr

/-- A classfile: its binary name (with `/`), and its own `InnerClasses` entry, outer class and
simple name, if it is a member class. -/
structure Entry where
  bin : String
  inner : Option (String × String) := none
  deriving DecidableEq, Repr

/-- The top level of a program, with the package object and Scala 3's wrapper as objects. -/
def Prog.topNodes (p : Prog) : List Node :=
  p.tops ++ (p.pkgObj.toList.map fun b => .mk "package" .obj b) ++
    (if p.topDef || !p.implicits.isEmpty then
      [.mk (p.file ++ "$package") .obj (p.implicits.map fun n => .mk n .cls [])]
     else [])

def pkgPrefix (pkg : List String) : String := String.join (pkg.map (encode · ++ "/"))

/-- Is `n` a companion of a class-like `.mk name _` among `sibs` of the kinds `ks`? -/
def hasSibling (sibs : List Node) (name : String) (ks : List K) : Bool :=
  sibs.any fun s => s.name == name && ks.contains s.kind

/-- How a file system measures a file name's length against its limit of 255: APFS (macOS, where the
probe runs) in UTF-16 units, ext4 (Linux) in UTF-8 bytes. The compilers' limits count characters, so
a non-ASCII name they keep can still be too long for ext4. -/
inductive Fs | apfs | ext4
  deriving DecidableEq, Repr

/-- Is a binary name too long for its classfile's name on `fs`? (The spaces' names are in the Basic
Multilingual Plane, so a character is one UTF-16 unit.) -/
def unwritable (fs : Fs) (bin : String) : Bool :=
  let f := (bin.splitOn "/").getLastD bin ++ ".class"
  (match fs with | .apfs => f.length | .ext4 => f.utf8ByteSize) > 255

/-- The flat name of a member `n` of a class-like whose flat name is `of`. scalac encodes names when it
parses them, so it shortens the encoded name; dotc encodes in the backend, so it shortens the source
name (its MD5 and its ends) and then encodes the result, which can be longer than any file name. -/
def memberFlat (dl : Dialect) (of n : String) : String :=
  if dl == .s3 then compact dl (of ++ "$" ++ n) else compact dl (of ++ "$" ++ encode n)

/-- The classfiles of a node and its members. `owner`: the enclosing flat name (without the module
suffix, decoded for Scala 3) and the class its members' `InnerClasses` entries name as outer: its
binary name, but for a top-level object its companion class or mirror class (scalac's
`buildNestedInfo`, "Java compatibility"). -/
partial def nodeEntries (dl : Dialect) (pre : String) (owner : Option (String × String))
    (sibs : List Node) (n : Node) : List Entry :=
  let flat := match owner with
    | none => if dl == .s3 then n.name else encode n.name
    | some (of, _) => memberFlat dl of n.name
  let clsBin := pre ++ (if dl == .s3 then encode flat else flat)
  let modBin := clsBin ++ "$"
  let inner (mod : Bool) : Option (String × String) :=
    owner.map fun (_, ob) => (ob, encode n.name ++ (if mod then "$" else ""))
  let own : List Entry := match n.kind with
    | .cls | .trt => [{ bin := clsBin, inner := inner false }]
    | .ccls => [{ bin := clsBin, inner := inner false }] ++
        (if hasSibling sibs n.name [.obj] then [] else [{ bin := modBin, inner := inner true }])
    | .obj => [{ bin := modBin, inner := inner true }] ++
        -- a top-level object without a companion class has a mirror class
        (if owner.isNone && !hasSibling sibs n.name [.cls, .trt, .ccls] then [{ bin := clsBin }] else [])
  let outerOfMembers := if n.kind == .obj && owner.isSome then modBin else clsBin
  own ++ n.body.flatMap (nodeEntries dl pre (some (flat, outerOfMembers)) n.body)

/-- The classfiles a program compiles to.

Spec: unspecified SLS §9.2: the binary names of classes, traits and objects, members and package
objects; JLS §13.1 fixes `Outer$Inner` for Java member classes and nothing for Scala's module
classes, mirror classes or `<file>$package`; calibrated against scalac 2.12.21, 2.13.18 and dotc 3.9.0
by `packages/scala/probes/names.py` (314 programs for Scala 2, 332 for Scala 3). -/
def entries (dl : Dialect) (p : Prog) : List Entry :=
  let tops := p.topNodes
  tops.flatMap (nodeEntries dl (pkgPrefix p.pkg) none tops)

/-! ## Printing -/

def K.kw : K → String | .cls => "class" | .trt => "trait" | .obj => "object" | .ccls => "case class"

/-- Every name is backquoted, so operators and spaces need no other care. -/
partial def Node.show (ind : String) : Node → String
  | .mk n k b =>
    let ps := if k == .ccls then "(x: Int)" else ""
    let body := String.join (b.map (Node.show (ind ++ "  ")))
    s!"{ind}{k.kw} `{n}`{ps} \{\n{body}{ind}}\n"

def Prog.show (p : Prog) : String :=
  let wrapIn (pkg : List String) (s : String) : String :=
    pkg.foldr (fun q acc => s!"package `{q}` \{\n{acc}}\n") s
  let tops := String.join (p.tops.map (Node.show "  ")) ++
    (if p.topDef then "  def topDef: Int = 1\n" else "") ++
    String.join (p.implicits.map fun n => s!"  implicit class `{n}`(val x: Int)\n")
  let po := match p.pkgObj, p.pkg.getLast? with
    | some b, some last =>
      wrapIn p.pkg.dropLast s!"package object `{last}` \{\n{String.join (b.map (Node.show "  "))}}\n"
    | _, _ => ""
  wrapIn p.pkg tops ++ po

/-! ## The space -/

/-- How a level of a chain holds the next: as a class, trait or object, or as one half of a
companion pair (the other half empty). -/
inductive Holder | cls | trt | obj | pairCls | pairObj
  deriving DecidableEq, Repr

/-- The innermost level: a class-like, or a companion pair. -/
inductive Leaf | one (k : K) | pair (k : K)
  deriving DecidableEq, Repr

def holders : List Holder := [.cls, .trt, .obj, .pairCls, .pairObj]
def leaves : List Leaf := [.one .cls, .one .trt, .one .obj, .one .ccls, .pair .cls, .pair .trt]

def Leaf.nodes (n : String) : Leaf → List Node
  | .one k => [.mk n k []]
  | .pair k => [.mk n k [], .mk n .obj []]

/-- A chain of holders around a leaf; level `i` is named `names[i]`. -/
def chain (names : List String) (hs : List Holder) (l : Leaf) : List Node :=
  match hs, names with
  | [], n :: _ => l.nodes n
  | h :: hs, n :: ns =>
    let inner := chain ns hs l
    match h with
    | .cls => [.mk n .cls inner]
    | .trt => [.mk n .trt inner]
    | .obj => [.mk n .obj inner]
    | .pairCls => [.mk n .cls inner, .mk n .obj []]
    | .pairObj => [.mk n .cls [], .mk n .obj inner]
  | _, [] => []

def levelNames : List String := ["A", "B", "C", "D"]

/-- Nestings: up to two holders in a package and a subpackage, three in a package. -/
def nestSpace : List Prog :=
  let pkgs : List (List String) := [[], ["p"], ["p", "q"]]
  -- the empty package only at the top level: each such program needs a compiler of its own
  let short := pkgs.flatMap fun pkg =>
    ([[]] ++ (if pkg.isEmpty then [] else holders.map ([·]))).flatMap fun hs => leaves.map fun l =>
      { pkg, tops := chain levelNames hs l }
  let deep := holders.flatMap fun h1 => holders.flatMap fun h2 => leaves.map fun l =>
    ({ pkg := ["p"], tops := chain levelNames [h1, h2] l } : Prog)
  short ++ deep

/-- Package objects and their members, in a package and a subpackage. -/
def pkgObjSpace : List Prog :=
  [["p"], ["p", "q"]].flatMap fun pkg =>
    (leaves.map fun l => ({ pkg, pkgObj := some (l.nodes "M") } : Prog)) ++
    [{ pkg, pkgObj := some [.mk "O" .obj [.mk "N" .cls []]] }, { pkg, pkgObj := some [.mk "C" .cls [.mk "N" .obj []]] }]

/-- Names that need encoding, at the top level and as members. -/
def encodeSpace : List Prog :=
  ["+", "::", "<>", "a b", "Ünï", "a_+", "x$y", "~=?"].flatMap fun n =>
    [{ pkg := ["p"], tops := [.mk n .cls []] },
     { pkg := ["p"], tops := [.mk n .obj []] },
     { pkg := ["p"], tops := [.mk "O" .obj [.mk n .cls []]] },
     { pkg := ["p"], tops := [.mk "C" .cls [.mk n .obj []]] },
     ({ pkg := ["p"], tops := [.mk n .cls [.mk n .cls []]] } : Prog)]

def rep (c : Char) (k : Nat) : String := String.ofList (List.replicate k c)

/-- Flat names around each version's limit: a 100-character owner and a member that brings the flat
name to `len`; a three-level chain whose middle level is shortened in some versions only; operator
names that are short in source and long encoded; non-ASCII names. -/
def longSpace : List Prog :=
  let o := rep 'O' 100
  let at_ (len : Nat) : List Prog :=
    let m := rep 'm' (len - 101)
    [{ pkg := ["p"], tops := [.mk o .obj [.mk m .cls []]] },
     { pkg := ["p"], tops := [.mk o .cls [.mk m .obj []]] },
     { pkg := ["p"], tops := [.mk o .cls [.mk m .ccls []]] }]
  ([232, 233, 234, 235, 246, 247, 248, 260].flatMap at_) ++
  [{ pkg := ["p"], tops := [.mk o .obj [.mk (rep 'm' 140) .obj [.mk "Leaf" .cls [], .mk "Leaf" .obj []]]] },
   { pkg := ["p"], tops := [.mk o .cls [.mk (rep 'm' 150) .cls [.mk (rep 'n' 120) .cls []]]] },
   { pkg := ["p"], tops := [.mk "O" .obj [.mk (rep '+' 50) .cls []]] },
   -- encoded over 2.13's limit, decoded under dotc's: only 2.13 shortens it
   { pkg := ["p"], tops := [.mk o .obj [.mk (rep 'm' 125 ++ "++") .cls []]] },
   -- decoded over dotc's limit with an operator in the kept suffix: dotc hashes the decoded name
   { pkg := ["p"], tops := [.mk o .obj [.mk (rep 'm' 140 ++ "+") .cls []]] },
   -- non-ASCII: the MD5 is of UTF-8 bytes; 2.12 keeps 241 characters (488 bytes: too long for ext4)
   { pkg := ["p"], tops := [.mk (rep 'Ü' 100) .obj [.mk (rep 'ü' 140) .cls []]] }]

/-- Scala 3's wrapper for top-level definitions, named after the file. -/
def s3TopSpace : List Prog :=
  [[], ["p"]].flatMap fun pkg => ["A", "my-file", "Ünï"].flatMap fun file =>
    [{ pkg, file, topDef := true, only3 := true },
     { pkg, file, implicits := ["I"], only3 := true },
     ({ pkg, file, topDef := true, implicits := ["I"], tops := [.mk "C" .cls []], only3 := true } : Prog)]

/-- Every program, with its family. -/
def namesSpace : List (String × Prog) :=
  (nestSpace.map ("nest", ·)) ++ (pkgObjSpace.map ("pkgobj", ·)) ++ (encodeSpace.map ("encode", ·)) ++
    (longSpace.map ("long", ·)) ++ (s3TopSpace.map ("s3top", ·))

#guard encode "a b" == "a$u0020b"
#guard (longSpace.getLast?.map fun p => (entries .s212 p).any (unwritable .ext4 ·.bin)) == some true
#guard (longSpace.getLast?.map fun p => (entries .s212 p).any (unwritable .apfs ·.bin)) == some false
#guard encode "::" == "$colon$colon"
#guard entries .s213 { pkg := ["p"], tops := [.mk "O" .obj [.mk "C" .cls []]] } ==
  [{ bin := "p/O$" }, { bin := "p/O" }, { bin := "p/O$C", inner := some ("p/O", "C") }]

end Scala.Names
