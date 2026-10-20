/-!
# MD5, as the compilers use it to shorten long class names

scalac and dotc shorten a flattened class name that is too long for a file name by replacing its
middle with the MD5 of the whole name (`compactify`, `Scala.Names`). The digest is RFC 1321's; the
compilers print it as each byte's `toHexString`, which drops a leading zero, so a digest is between
16 and 32 characters (`hexNoPad`).
-/

namespace Scala.Md5

private def shifts : Array UInt32 := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

/-- `⌊|sin (i + 1)| · 2³²⌋`. -/
private def table : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

private def rotl (x s : UInt32) : UInt32 := (x <<< s) ||| (x >>> (32 - s))

/-- The message padded to a multiple of 64 bytes: `0x80`, zeros, the bit length (little-endian). -/
private def pad (m : ByteArray) : ByteArray := Id.run do
  let mut b := m.push 0x80
  while b.size % 64 != 56 do b := b.push 0
  let bits : UInt64 := m.size.toUInt64 * 8
  for i in [0:8] do b := b.push (bits >>> (8 * i).toUInt64).toUInt8
  pure b

private def word (b : ByteArray) (o : Nat) : UInt32 :=
  b[o]!.toUInt32 ||| (b[o + 1]!.toUInt32 <<< 8) ||| (b[o + 2]!.toUInt32 <<< 16) ||| (b[o + 3]!.toUInt32 <<< 24)

/-- The 16-byte digest. -/
def digest (m : ByteArray) : List UInt8 := Id.run do
  let b := pad m
  let mut h : Array UInt32 := #[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476]
  for c in [0:b.size / 64] do
    let mut a := h[0]!
    let mut bb := h[1]!
    let mut cc := h[2]!
    let mut d := h[3]!
    for i in [0:64] do
      let (f, g) :=
        if i < 16 then ((bb &&& cc) ||| (~~~bb &&& d), i)
        else if i < 32 then ((d &&& bb) ||| (~~~d &&& cc), (5 * i + 1) % 16)
        else if i < 48 then (bb ^^^ cc ^^^ d, (3 * i + 5) % 16)
        else (cc ^^^ (bb ||| ~~~d), (7 * i) % 16)
      let f' := f + a + table[i]! + word b (64 * c + 4 * g)
      a := d
      d := cc
      cc := bb
      bb := bb + rotl f' shifts[i]!
    h := #[h[0]! + a, h[1]! + bb, h[2]! + cc, h[3]! + d]
  pure (h.toList.flatMap fun w => (List.range 4).map fun i => (w >>> (8 * i).toUInt32).toUInt8)

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!

/-- Each byte as Java's `Integer.toHexString`: no leading zero. -/
def hexNoPad (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let n := b.toNat
    if n < 16 then (hexDigit n).toString else s!"{hexDigit (n / 16)}{hexDigit (n % 16)}")

/-- The compilers' rendering of the MD5 of a string's UTF-8 bytes. -/
def ofString (s : String) : String := hexNoPad (digest s.toUTF8)

-- RFC 1321's test suite, unpadded: `d41d8cd98f00b204e9800998ecf8427e` has a leading-zero byte (`04`)
#guard ofString "" == "d41d8cd98f0b24e980998ecf8427e"
#guard ofString "abc" == "90150983cd24fb0d6963f7d28e17f72"
#guard ofString "message digest" == "f96b697d7cb7938d525a2f31aaf161d0"
#guard ofString "12345678901234567890123456789012345678901234567890123456789012345678901234567890" ==
  "57edf4a22be3c955ac49da2e217b67a"

end Scala.Md5
