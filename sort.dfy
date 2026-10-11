predicate isSorted(s : seq<int>){
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma SortedTransitive(a: array<int>, i: int, j: int)
  requires forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k+1]
  requires 0 <= i <= j < a.Length
  ensures a[i] <= a[j]
{
  if j <= 1 {

  }else{
    assert a[j] >= a[j -1];
    assert j >= i;
    if j == i {

    }else{
      assert j > i;
      if i == j - 1 {

      }else{
        SortedTransitive(a,i,j-1);
        assert a[j-1] >= a[i];
        assert a[j] >= a[i];
      }
    }
  }
}

lemma AppendLargerItem(s : seq<int>, d : int)
  requires forall i :: 0 <= i < |s| ==> d >= s[i]
  requires isSorted(s)
  ensures isSorted(s + [d])
{

}

function Min(a: int, b: int): int {
    if a <= b then a else b
}

lemma MultisetAppend<T(==)>(s: seq<T>, x: T)
  ensures multiset(s + [x]) == multiset(s) + multiset{x}
{
}

method {:isolate_assertions} MergeSortedIter(a : seq<int>, b : seq<int>) returns (c : seq<int>)
  requires isSorted(a)
  requires isSorted(b)
  ensures isSorted(c)
  ensures multiset(c) == multiset(a + b)
{
  c := [];
  
  var a_p := 0;
  var b_p := 0;

  while a_p < |a| && b_p < |b|
    invariant 0 <= a_p <= |a|
    invariant 0 <= b_p <= |b|
    invariant isSorted(c)
    invariant a_p < |a| ==> forall i :: 0 <= i < |c| ==> c[i] <= a[a_p]
    invariant b_p < |b| ==> forall i :: 0 <= i < |c| ==> c[i] <= b[b_p]
    invariant multiset(c) == multiset(a[0..a_p] + b[0..b_p])
  {
    ghost var c' := c;

    if a[a_p] < b[b_p] {
      c := c + [a[a_p]];

      ghost var a_p' := a_p;
      a_p := a_p + 1;

      assert multiset(c') == multiset(a[0..a_p'] + b[0..b_p]);
      assert a[0..a_p'] + [a[a_p']] == a[0..a_p'+1];
      assert multiset(a[0..a_p'] + [a[a_p']]) == multiset(a[0..a_p'+1]);
      assert multiset(a[0..a_p'] + [a[a_p']]) == multiset(a[0..a_p]);
      MultisetAppend(c,a[a_p']);
      assert multiset(c' + [a[a_p']]) == multiset(a[0..a_p'] + b[0..b_p] + [a[a_p']]);
      assert multiset(c' + [a[a_p']]) == multiset(a[0..a_p'] + [a[a_p']] + b[0..b_p]);
      assert multiset(c' + [a[a_p']]) == multiset(a[0..a_p] + b[0..b_p]);
      assert multiset(c) == multiset(a[0..a_p] + b[0..b_p]);
    }else{
      c := c + [b[b_p]];
      
      ghost var b_p' := b_p;
      b_p := b_p + 1;

      assert multiset(c') == multiset(a[0..a_p] + b[0..b_p']);
      assert b[0..b_p'] + [b[b_p']] == b[0..b_p'+1];
      assert multiset(b[0..b_p'] + [b[b_p']]) == multiset(b[0..b_p'+1]);
      assert multiset(b[0..b_p'] + [b[b_p']]) == multiset(b[0..b_p]);
      MultisetAppend(c,b[b_p']);
      assert multiset(c' + [b[b_p']]) == multiset(a[0..a_p] + b[0..b_p'] + [b[b_p']]);
      assert multiset(c' + [b[b_p']]) == multiset(a[0..a_p] + b[0..b_p]);
      assert multiset(c) == multiset(a[0..a_p] + b[0..b_p]);
    }
  }

  assert !(a_p < |a| && b_p < |b|);
  assert a_p >= |a| || b_p >= |b|;
  assert a_p == |a| || b_p == |b|;

  if a_p < |a| {
    assert multiset(c) == multiset(a[0..a_p] + b[0..b_p]);
    assert b_p == |b|;
    assert b[0..b_p] == b[0..|b|];
    assert b[0..|b|] == b;
    assert multiset(c) == multiset(a[0..a_p] + b);
    ghost var c' := c;
    c := c + a[a_p..];
    assert multiset(c) == multiset(c' + a[a_p..]);
    assert multiset(c) == multiset(a[0..a_p] + b + a[a_p..]);
    assert multiset(c) == multiset((a[0..a_p] + a[a_p..]) + b);
    assert a[0..a_p] + a[a_p..] == a;
    assert multiset(c) == multiset(a + b);
  }else{
    assert a_p == |a|;
    assert multiset(c) == multiset(a[0..a_p] + b[0..b_p]);
    assert a_p == |a|;
    assert a[0..a_p] == a[0..|a|];
    assert a[0..|a|] == a;
    assert multiset(c) == multiset(a + b[0..b_p]);
    ghost var c' := c;
    c := c + b[b_p..];
    assert multiset(c) == multiset(c' + b[b_p..]);
    assert multiset(c) == multiset(a + b[0..b_p] + b[b_p..]);
    assert b[0..b_p] + b[b_p..] == b;
    assert multiset(c) == multiset(a + b);
  }
}



