function F(i : int) : int

ghost function SumUp(lo : int, hi : int): int
  requires lo <= hi
  decreases hi - lo
{
  if lo == hi then
    0
  else
    F(lo) + SumUp(lo + 1,hi)
}

ghost function SumDown(lo: int, hi: int): int
  requires lo <= hi
  decreases hi - lo
{
  if lo == hi then 0 else SumDown(lo, hi - 1) + F(hi - 1)
}

lemma PrependSumDown(lo: int, hi: int)
  requires lo < hi
  ensures F(lo) + SumDown(lo + 1, hi) == SumDown(lo, hi)
  decreases hi - lo
{
  if lo == hi {

  }
  else{
    if lo < hi -1 {
      calc {
        SumDown(lo, hi);
      ==
        SumDown(lo, hi - 1) + F(hi - 1);
      ==
        {PrependSumDown(lo,hi -1);}
        F(lo) + SumDown(lo + 1, hi - 1) + F(hi - 1);
      ==
        F(lo) + SumDown(lo + 1, hi);
      }
    }else{
      calc {
        SumDown(lo, hi);
      ==
        SumDown(lo, hi - 1) + F(hi - 1);
      ==
        { assert hi - 1 == lo;}
        0 + F(hi - 1);
      ==
        F(lo) + SumDown(lo + 1,hi);
      }
    }
  }
}

lemma AppendSumUp(lo : int,hi : int)
  requires lo < hi
  ensures SumUp(lo,hi) == SumUp(lo,hi - 1) + F(hi - 1)
  decreases hi - lo
{
  if lo == hi {

  }else{
    if lo + 1 < hi {
      calc {
        SumUp(lo,hi);
      ==
        F(lo) + SumUp(lo + 1,hi);
      ==
        {AppendSumUp(lo + 1,hi);}
        F(lo) + SumUp(lo + 1,hi - 1) + F(hi - 1);
      }
    }
  }
}

method LoopUp0(lo : int, hi : int)
  returns (s : int)
  requires lo <= hi
  ensures s == SumUp(lo,hi)
{
  s := 0;
  var i := lo;

  while i != hi
    invariant lo <= i <= hi
    invariant s == SumUp(lo,i)
  {
    s := s + F(i);
    i := i + 1;
    AppendSumUp(lo,i);
  }
}

method LoopUp1(lo : int, hi : int)
    returns (s : int)
  requires lo <= hi
  ensures s == SumDown(lo,hi)
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

method LoopUp2(lo : int, hi : int)
    returns (s : int)
  requires lo <= hi
  ensures s == SumUp(lo,hi)
{
  s := 0;
  var i := lo;

  while i != hi
    invariant lo <= i <= hi
    invariant s + SumUp(i,hi) == SumUp(lo,hi)
  {
    s := s + F(i);
    i := i + 1;
  }
}