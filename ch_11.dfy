function F(x: int): int

ghost function SumUp(lo: int, hi: int): int
  requires lo <= hi
  decreases hi - lo
{
  if lo == hi then 0 else F(lo) + SumUp(lo + 1, hi)
}

ghost function SumDown(lo: int, hi: int): int
  requires lo <= hi
  decreases hi - lo
{
  if lo == hi then 0 else SumDown(lo, hi - 1) + F(hi - 1)
}

lemma SameSums(lo: int, hi: int)
  requires lo <= hi
  ensures SumUp(lo, hi) == SumDown(lo, hi)
  decreases hi - lo
{
  if lo != hi {
    PrependSumDown(lo, hi);
  }
}

lemma {:induction false} PrependSumDown(lo: int, hi: int)
  requires lo < hi
  ensures F(lo) + SumDown(lo + 1, hi) == SumDown(lo, hi)
  decreases hi - lo
{
  if hi == lo {
    //vacuos
  }else{
    assert hi > lo;
    //F(lo) + SumDown(lo + 1, hi)
    if hi == lo + 1{
      calc{
        F(lo) + SumDown(lo + 1, hi);
      ==
        F(lo) + 0;
      ==
        SumDown(lo, hi);
      }
    }else{
      assert lo + 1 < hi;
      calc{
        F(lo) + SumDown(lo + 1, hi);
      ==
        F(lo) + SumDown(lo + 1, hi - 1) + F(hi - 1);
      ==
        {
          PrependSumDown(lo, hi -1);
        }
        SumDown(lo, hi - 1) + F(hi - 1);
      ==
        SumDown(lo,hi);
      }
    }
  }
}

lemma {:induction false} AppendSumUp(lo: int, hi: int)
  requires lo < hi
  ensures SumUp(lo, hi - 1) + F(hi - 1) == SumUp(lo, hi)
  decreases hi - lo
{
  if lo == hi - 1 {
  } else {
    AppendSumUp(lo + 1, hi);
  }
}

// Loop Up

method LoopUp0(lo: int, hi: int) returns (s: int)
  requires lo <= hi
  ensures s == SumUp(lo, hi)
{
  s := 0;
  var i := lo;
  while i != hi
    invariant lo <= i <= hi
    invariant s == SumUp(lo, i)
  {
    s := s + F(i);
    i := i + 1;
    AppendSumUp(lo, i);
  }
}

method LoopUp1(lo: int, hi: int) returns (s: int)
  requires lo <= hi
  ensures s == SumDown(lo, hi)
{
  s := 0;
  var i := lo;
  while i != hi
    invariant lo <= i <= hi
    invariant s == SumDown(lo, i)
  {
    s := s + F(i);
    i := i + 1;
  }
}

method LoopUp2(lo: int, hi: int) returns (s: int)
  requires lo <= hi
  ensures s == SumUp(lo, hi)
{
  s := 0;
  var i := lo;
  while i != hi
    invariant lo <= i <= hi
    invariant s + SumUp(i, hi)
           == SumUp(lo, hi)
  {
    s := s + F(i);
    i := i + 1;
  }
}

// Loop Down

method LoopDown0(lo: int, hi: int) returns (s: int)
  requires lo <= hi
  ensures s == SumDown(lo, hi)
{
  s := 0;
  var i := hi;
  while i != lo
    invariant lo <= i <= hi
    invariant s == SumDown(i, hi)
  {
    i := i - 1;
    s := s + F(i);
    PrependSumDown(i, hi);
  }
}

method LoopDown1(lo: int, hi: int) returns (s: int)
  requires lo <= hi
  ensures s == SumUp(lo, hi)
{
  s := 0;
  var i := hi;
  while i != lo
    invariant lo <= i <= hi
    invariant s == SumUp(i, hi)
  {
    i := i - 1;
    s := s + F(i);
  }
}

method LoopDown2(lo: int, hi: int) returns (s: int)
  requires lo <= hi
  ensures s == SumDown(lo, hi)
{
  s := 0;
  var i := hi;
  while i != lo
    invariant lo <= i <= hi
    invariant SumDown(lo, i) + s
    == SumDown(lo, hi)
  {
    i := i - 1;
    s := s + F(i);
  }
}