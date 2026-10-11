ghost function Hash(s: string): int {
  SumChars(s) % 137
}

ghost function SumChars(s: string): int {
  if |s| == 0 then 0 else
  var last := |s| - 1;
  SumChars(s[..last]) + s[last] as int
}



class ChecksumMachine {

  ghost var data : string

  var cs : int

  ghost predicate Valid()
    reads this
  {
    cs == Hash(data)
  }

  constructor ()
    ensures data == ""
  {
    data, cs := "", 0;
  }

  method Append(d : string)
    requires Valid()
    modifies this
    ensures Valid() && data == old(data) + d
  {
    var i := 0;
    while i != |d|
      invariant 0 <= i <= |d|
      invariant Valid()
      invariant data == old(data) + d[..i]
    {
      cs := (cs + d[i] as int) % 137;
      data := data + [d[i]];
      i := i + 1;
    }
  }

  function Checksum() : int
    requires Valid()
    reads this
    ensures Checksum() == Hash(data)
  {
    cs
  }
}

datatype Category = Identifier | Number | Operator
                  | Whitespace | Error | End

predicate Is(ch: char, cat: Category)
  requires cat != End
  decreases cat == Error
{
  match cat
  case Whitespace => ch in " \t\r\n"
  case Identifier => 'A' <= ch <= 'Z' || 'a' <= ch <= 'z'
  case Number => '0' <= ch <= '9'
  case Operator => ch in "+-*/%!=><~^&|"
  case Error =>
    !Is(ch, Identifier) && !Is(ch, Number) &&
    !Is(ch, Operator) && !Is(ch, Whitespace)
}

class Tokenizer {
  const source : string
  var n : nat

  ghost predicate Valid()
    reads this
  {
    n <= |source|
  }

  constructor (s: string)
    ensures Valid() && source == s && n == 0
  {
    source, n := s, 0;
  }
}