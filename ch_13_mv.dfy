function Count<T(==)>(a : seq<T>, lo : int, hi : int, x : T) : nat
  requires 0 <= lo <= hi <= |a|
{
  if lo == hi then
    0
  else
    (if a[hi - 1] == x then 1 else 0) + Count(a, lo,hi - 1,x)
}

lemma {:induction false} SplitCount<T>(a : seq<T>, lo : int, mid : int, hi : int, x : T)
  requires 0 <= lo <= mid <= hi <= |a|
  ensures Count(a, lo, mid, x) + Count(a, mid, hi, x)
       == Count(a,lo,hi,x)
{
  if lo == hi {
    assert mid == hi;
    calc {
      Count(a, lo, mid, x) + Count(a, mid, hi, x);
    ==
      0 + 0;
    ==
      Count(a,lo,hi,x);
    }
  }else{
    if mid == lo {

    }
    else if mid == hi {

    }
    else{
      calc {
        Count(a, lo, mid, x) + Count(a, mid, hi, x);
      ==
        Count(a, lo, mid, x)
        + (if a[hi - 1] == x then 1 else 0) + Count(a, mid,hi - 1,x);
      ==
        (if a[hi - 1] == x then 1 else 0) + Count(a, lo, mid, x)
        + Count(a, mid,hi - 1,x);
      ==
        { SplitCount(a,lo,mid,hi-1,x);}
        (if a[hi - 1] == x then 1 else 0) + Count(a,lo,hi-1,x);
      ==
        Count(a,lo,hi,x);
      }
    }
  }
}

lemma DistinctCounts<T>(a : seq<T>, lo : int, hi : int, x : T, y : T)
  requires 0 <= lo <= hi <= |a|
  ensures x != y ==> 
    Count(a,lo,hi,x) + Count(a,lo,hi,y) <= hi - lo
{
  
}
