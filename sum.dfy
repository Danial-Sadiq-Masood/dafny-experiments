function SumHead(xs : seq<int>): int {
  if |xs| == 0 then 0 else xs[0] + SumHead(xs[1..])
}

function SumTail(xs : seq<int>): int {
  if |xs| == 0 then 0 else xs[|xs| - 1] + SumTail(xs[..|xs| - 1])
}


lemma AppendTailSum(xs : seq<int>, i : int)
  ensures SumTail(xs + [i]) == SumTail(xs) + i
{
  var appended := xs + [i];
  if |xs| == 0 {
    calc{
      SumTail(xs + [i]);
    ==
      {
        assert xs + [i] == [i];
      }
      SumTail([i]);
    ==
      i;
    ==
      0 + i;
    ==
      SumTail(xs) + i;
    }
  }else{
    calc{
      SumTail(xs + [i]);
    ==
      SumTail(appended);
    ==
      appended[|appended| - 1] + SumTail(appended[..|appended| - 1]);
    ==
      i + SumTail(appended[..|appended| - 1]);
    ==
      i + SumTail(xs);
    ==
      SumTail(xs) + i;
    }
  }
}

method Sum1(xs : seq<int>) returns (s : int)
  ensures s == SumTail(xs)
{
  var i := 0;
  s := 0;

  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant s == SumTail(xs[..i])
  {
    s := s + xs[i];
    ghost var old_i := i; 
    i := i + 1;
    
    AppendTailSum(xs[..old_i], xs[old_i]);
    assert SumTail(xs[..old_i] + [xs[old_i]]) == SumTail(xs[..old_i]) + xs[old_i];
    assert xs[..old_i] + [xs[old_i]] == xs[..i];
    
    calc{
      SumTail(xs[..old_i] + [xs[old_i]]); 
    == 
      SumTail(xs[..i]);
    ==
      SumTail(xs[..old_i]) + xs[old_i];
    ==
      s;
    }
  }

  assert i == |xs|;
  assert xs[..i] == xs;
  assert s == SumTail(xs[..i]);
}