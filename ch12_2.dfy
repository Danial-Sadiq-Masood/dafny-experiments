function sumSeq1(s : seq<int>, lo : nat, hi : nat) : int 
  requires lo <= hi < |s|
  decreases hi - lo
{
  if lo == hi then 0 else s[lo] + sumSeq1(s,lo + 1, hi)
}

function sumSeq(s : seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sumSeq(s[1..])
}

lemma SumSeqWithPrependedVal(s : seq<int>, v : int)
  ensures sumSeq([v] + s) == sumSeq(s) + v
{
  if |s| == 0 {

  }else{
    calc{
      sumSeq([v] + s);
    ==
      v + sumSeq(s);
    }
  }
}

function sumSeqBackward(s : seq<int>) : int {
  if |s| == 0 then 0 else s[|s| - 1] + sumSeqBackward(s[0..|s|-1])
}

lemma SumSeqWithAppendedVal(s : seq<int>, v : int)
  ensures sumSeqBackward(s + [v]) == sumSeqBackward(s) + v
{
  if |s| == 0 {

  }else{
    var combined := s + [v]; 
    calc{
      sumSeqBackward(combined);
    ==
      sumSeqBackward(s + [v]);
    ==
      combined[|combined| - 1] + sumSeqBackward(combined[0..|combined|-1]);
    ==
      v + sumSeqBackward(s);
    }
  }
}

method sumSeq_iter(s : seq<int>) returns (sum : int)
  ensures sum == sumSeq(s)
{
  sum := 0;
  var i := |s|;

  while i != 0
    invariant 0 <= i <= |s|
    invariant sum == sumSeq(s[i..])
  {
    i := i - 1;
    sum := sum + s[i];
    
    SumSeqWithPrependedVal(s[i+1..],s[i]);
  }  
}

lemma SliceFullLength(s : seq<int>)
  ensures s[..|s|] == s
{

}

method sumSeq_iter2(s : seq<int>) returns (sum : int)
  ensures sum == sumSeqBackward(s)
{
  sum := 0;
  var i := 0;

  while i != |s|
    invariant 0 <= i <= |s|
    invariant sum == sumSeqBackward(s[..i])
  {
    sum := sum + s[i];

    i := i + 1;

    assert s[..i-1] + [s[i-1]] == s[..i];
    SumSeqWithAppendedVal(s[..i-1], s[i-1]);

    assert sumSeqBackward(s[..i-1]) + s[i-1] == sumSeqBackward(s[..i-1] + [s[i-1]]);
  }

  assert i == |s|;
  calc{
    sumSeqBackward(s[..i]);
  ==
    sumSeqBackward(s[..|s|]); 
  ==
    {SliceFullLength(s);}
    sumSeqBackward(s);
  }
}