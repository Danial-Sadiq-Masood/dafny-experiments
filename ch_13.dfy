method LinearSearch0<T>(a : array<T>, P : T -> bool) returns (n : int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  ensures forall i :: 0 <= i < n ==> !P(a[i])
{
  n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> !P(a[i])
  {
    if P(a[n]) {
      break;
    }
    n := n + 1;
  }
}

method Min1(a : array<int>) returns (m : int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
  ensures exists i :: 0 <= i < a.Length && m == a[i]
{
  var n := 1;
  m := a[0];
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> m <= a[i]
    invariant exists i :: 0 <= i < n && m == a[i]
  {
    if a[n] < m {
      m := a[n];
    }
    n := n + 1;
  }
}

method Min2(a : array<int>) returns (m : int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
  ensures exists i :: 0 <= i < a.Length && m == a[i]
{
  var n := a.Length - 1;
  m := a[a.Length - 1];

  n := n - 1;

  while n >= 0
    invariant -1 <= n < a.Length
    invariant forall i :: n < i < a.Length ==> m <= a[i]
    invariant exists i :: n < i < a.Length &&  m == a[i]
  {
    if a[n] < m {
      m := a[n];
    }

    n := n - 1;
  }

  assert -1 <= n < a.Length && n < 0;
  assert n == -1;

}

method Min3(a : array<int>) returns (m : int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
  ensures exists i :: 0 <= i < a.Length && m == a[i]
{
  var n := a.Length - 1;
  m := a[a.Length - 1];

  while n > 0
    invariant 0 <= n < a.Length
    invariant forall i :: n <= i < a.Length ==> m <= a[i]
    invariant exists i :: n <= i < a.Length &&  m == a[i]
  {
    n := n - 1;

    if a[n] < m {
      m := a[n];
    }
  }

  assert n == 0;
}

function CountTail<T(==)>(s : seq<T>, x : T) : nat {
  if |s| == 0 then 0 else
  (if (s[|s| - 1] == x) then 1 else 0) + CountTail(s[0..|s|-1], x)
}

lemma AppendCount <T>(s : seq<T>, x : T, y : T)
  decreases |s|
  ensures
    var additionalCount := if (y == x) then 1 else 0;
    CountTail(s + [y], x) == CountTail(s,x) + additionalCount
{
  var additionalCount := if (y == x) then 1 else 0;

  if |s| == 0 {

    calc{
      CountTail(s + [y],x);
    ==
      CountTail([y],x);
    ==
      additionalCount;
    }
  }else{
    var appended := s + [y];

    calc{
      CountTail(s + [y], x);
    ==
      CountTail(appended, x);
    ==
      (if (appended[|appended| - 1] == x) then 1 else 0) + CountTail(appended[0..|appended| - 1], x);
    ==
      {
        assert appended[|appended| - 1] == y;
      }
      (if y == x then 1 else 0) + CountTail(appended[0..|appended| - 1], x);
    ==
      {
        assert appended[0..|appended| - 1] == s;
      }
      (if y == x then 1 else 0) + CountTail(s, x);
    ==
      CountTail(s,x) + additionalCount;
    }
  }
}

/*method CountIter<T(==)>(s : seq<T>, x : T) returns (c : nat) 
  ensures c == CountTail(s, x)
{
  var i := 0;
  c := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant c == CountTail(s[..i], x)
  {
    if(s[i] == x){
      c := c + 1;
    }
    
    i := i + 1;
    
    ghost var old_i := i - 1;
    ghost var additionalCount := if s[old_i] == x then 1 else 0;
    AppendCount(s[..old_i], x, s[old_i]);
    assert s[..old_i] + [s[old_i]] == s[0..i];
    assert CountTail(s[..i], x) == CountTail(s[..old_i],x) + additionalCount;
  }

  assert c == CountTail(s[..i], x);
  calc {
    i;
  ==
    {assert !(i < |s|) && 0 <= i <= |s|;}
    |s|;
  }
  assert c == CountTail(s, x); 
}*/

lemma MultisetIntersectionPrefix(a: array<int>, b: array<int>,
                                 m: nat, n: nat)
  requires m < a.Length && n < b.Length
  requires a[m] == b[n]
  ensures multiset(a[m..]) * multiset(b[n..])
       == multiset{a[m]} + (multiset(a[m+1..]) * multiset(b[n+1..]))
{
  if a.Length == 0 {

  }
  else if b.Length == 0 {

  }else{
    var E := multiset{a[m]};
    calc{
      multiset(a[m..]) * multiset(b[n..]);
    ==
      {
        assert a[m..] == [a[m]] +a[m+1..];
        assert E + multiset(a[m+1..]) == multiset(a[m..]);
        assert b[n..] == [b[n]] +b[n+1..];
        assert E + multiset(b[n+1..]) == multiset(b[n..]);
      }
      (E + multiset(a[m+1..])) * (E + multiset(b[n+1..]));
    }
  }
}

lemma MultiSetCons(xs : seq<int>)
  requires |xs| > 1
  ensures multiset(xs) == multiset{xs[0]} + multiset(xs[1..])
{
  assert xs == [xs[0]] + xs[1..];
}

lemma MultisetIntersectionAdvanceA(a: array<int>, m: nat,
                                  B: multiset<int>)
  requires m < a.Length && a[m] !in B
  ensures multiset(a[m..]) * B == multiset(a[m+1..]) * B
{
  var E := multiset{a[m]};
  calc {
    multiset(a[m..]) * B;
  ==
    {
      assert [a[m]] + a[m+1..] == a[m..];
      assert multiset(a[m..]) == multiset{a[m]} + multiset(a[m+1..]);
    }
    (multiset{a[m]} + multiset(a[m+1..])) * B;
  ==
    (multiset{a[m]} * B) + (multiset(a[m+1..]) * B);
  ==
    multiset{} + (multiset(a[m+1..]) * B);
  ==
    (multiset(a[m+1..]) * B);
  }
}

method CoincedenceCount(a : array<int>, b : array<int>) returns (c : nat)
  requires forall i,j :: 0 <= i < j < a.Length ==> a[j] >= a[i]
  requires forall i,j :: 0 <= i < j < b.Length ==> b[j] >= b[i]
  ensures c == |multiset(a[..]) * multiset(b[..])|
{
  c := 0;
  var m,n := 0,0;

  while m < a.Length && n < b.Length
    invariant 0 <= m <= a.Length
    invariant 0 <= n <= b.Length
    invariant c + |multiset(a[m..]) * multiset(b[n..])|
           == |multiset(a[..]) * multiset(b[..])|
    decreases (a.Length - m + b.Length - n)
  {
    if
    case a[m] == b[n] => {
      {
        MultisetIntersectionPrefix(a,b,m,n);
      }
      //multiset(a[m..]) * multiset(b[n..]) == multiset{a[m]} + (multiset(a[m+1..]) * multiset(b[n+1..]))
      calc{
        multiset(a[m..]) * multiset(b[n..]);
      ==
        multiset{a[m]} + (multiset(a[m+1..]) * multiset(b[n+1..]));
      }
      c := c + 1;
      m := m + 1;
      n := n + 1;
    }
    case a[m] < b[n] => {
      {
        MultisetIntersectionAdvanceA(a,m,multiset(b[n..]));
      }
      calc{
        multiset(a[m..]) * multiset(b[n..]);
      ==
        multiset(a[m+1..]) * multiset(b[n..]);
      }
      m := m + 1;
    }
    case a[m] > b[n] => {
      calc {
        multiset(a[m..]) * multiset(b[n..]);
      ==
        multiset(b[n..]) * multiset(a[m..]);
      ==
        {
          MultisetIntersectionAdvanceA(b,n,multiset(a[m..]));
        }
        multiset(b[n+1..]) * multiset(a[m..]);
      ==
        multiset(a[m..]) * multiset(b[n+1..]);
      }
      n := n + 1;
    }
  }
}