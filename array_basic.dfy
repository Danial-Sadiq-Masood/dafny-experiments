function SeqSum(s : seq<int>) : int
{
  if |s| == 0 then 0 else s[0] + SeqSum(s[1..])
}

lemma ApendSeqSum(s : seq<int>)
  requires |s| > 0
  ensures SeqSum(s[0..|s|-1]) + s[|s| - 1] ==  SeqSum(s)
{
  if |s| == 0 {

  }else{
    if |s| > 1 {
      var tl := s[1..];
      calc{
        SeqSum(s);
      ==
        s[0] + SeqSum(tl);
      ==
        {ApendSeqSum(tl);}
        s[0] + SeqSum(tl[0..|tl|-1]) + tl[|tl| - 1];
      ==
        { assert tl[0..|tl| - 1] == s[1..|s| - 1];}
        s[0] + SeqSum(s[1..|s|-1]) + tl[|tl| - 1];
      ==
        {assert tl[|tl| - 1] == s[|s|-1];}
        s[0] + SeqSum(s[1..|s|-1]) + s[|s| - 1];
      ==
        SeqSum(s[0..|s| - 1]) + s[|s| - 1];
      }
    }
  }
}

// sum down approach
method iterSeqSum(s : seq<int>) returns (sum : int)
  ensures sum == SeqSum(s)
{
  sum := 0;
  var i := |s|;

  while i != 0
    invariant 0 <= i <= |s|
    invariant sum == SeqSum(s[i..|s|])
    decreases i
  {
    i := i - 1;
    sum := sum + s[i];
  }

  assert s[0..|s|] == s;
}