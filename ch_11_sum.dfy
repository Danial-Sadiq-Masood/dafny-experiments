ghost function sum(a : array<int>, hi : int): int
  requires -1 <= hi < a.Length
  decreases hi
  reads a
{
  if hi == -1 then
    0
  else
    sum(a,hi - 1) + a[hi]
}

method iterSum(a : array<int>) returns (s : int)
{
  var acc := 0;
  var i := 0;

  while i != a.Length
    invariant 0 <= i <= a.Length
    invariant acc == sum(a, i - 1)
  {
    ghost var prev_acc := acc;
    acc := acc + a[i];
    ghost var prev_i := i;
    i := i + 1;
    calc{
      acc;
    ==
      prev_acc + a[prev_i];
    ==
      { assert prev_acc == sum(a, prev_i - 1);}
      sum(a, prev_i - 1) + a[prev_i];
    ==
      sum(a, i - 2) + a[i - 1];
    ==
      sum(a,i - 1);
    }
  }
  s := acc;
}

ghost function sum1(a : array<int>, lo : int): int
  requires 0 <= lo <= a.Length
  decreases a.Length - lo
  reads a
{
  if lo == a.Length then
    0
  else
    a[lo] + sum1(a,lo + 1)
}

method iterSum1(a : array<int>) returns (s : int)
{
  var i := a.Length;
  var acc := 0;

  while i != 0
    invariant 0 <= i <= a.Length
    invariant acc == sum1(a, i)
  {
    var prev_i := i;
    i := i - 1;
    var prev_acc := acc;
    acc := acc + a[i];

    calc{
      acc;
    ==
      prev_acc + a[i];
    ==
      {
        assert prev_acc == sum1(a, prev_i);
      }
      sum1(a, prev_i) + a[i];
    ==
      sum1(a, i);
    }
  }
  s := acc;
}

function contains(a : array<int>, i: nat, k : int) : bool
  requires 0 <= i <= a.Length
  decreases a.Length - i
  reads a
{
  if i == a.Length then
    false
  else if a[i] == k then
    true
  else
    contains(a, i + 1, k)
}

/*lemma correctExistsCase(a : array<int>, k : int)
  requires a.Length > 0
  ensures (exists i: int :: 0 <= i < a.Length && a[i] == k)
        ==> contains(a, 0, k)
{

}*/

lemma correctExistsCase(a: array<int>, k: int)
  ensures (exists i: int :: 0 <= i < a.Length && a[i] == k)
          ==> contains(a, 0, k)
{
  if exists i: int :: 0 <= i < a.Length && a[i] == k {
    var i : int :| 0 <= i < a.Length && a[i] == k;

    containsFromWitness(a, 0, i, k);
  }
}

lemma containsFromWitness(a: array<int>, current: int, target: int, k: int)
  requires 0 <= current <= target < a.Length
  requires a[target] == k
  ensures contains(a, current, k)
  decreases target - current
{
  if current == target {
    // contains(a, target, k) evaluates to true
  } else {
    // current < target
    containsFromWitness(a, current + 1, target, k);
  }
}

function Reverse<T>(s: seq<T>): seq<T>
{
  if s == [] then [] else Reverse(s[1..]) + [s[0]]
}

lemma ReversedHeadEqualsLast(s : seq<int>)
  requires |s| > 0
  ensures Reverse(s)[0] == s[|s| - 1]
{
}

/*method isPalindrome(a : seq<int>) returns (b : bool)
{
  var i := 0;
  var j:= |a| - 1;
  var res := true;

  while i < j
    invariant 0 <= i <= j + 1 <= |a|
    invariant a[0..i] == Reverse(a[j+1..|a|])
  {
    if a[i] != a[j] {
      res := false;
      break;
    }
    i := i + 1;
    j := j - 1;
  }

  b := res;
}*/

/*function isPalindrome(a : seq<int>,i : nat, j : nat): bool 
  decreases j - i
  requires j > i ==> j < |a|
{
  if i >= j then
    true
  else
    a[i] == a[j] && isPalindrome(a, i + 1, j - 1)
}*/

function isPalindrome(a : seq<int>): bool
  decreases |a|
{
  if |a| <= 1 then
    true
  else
    a[0] == a[|a|-1] && isPalindrome(a[1..|a| - 1])
}

lemma palindromeIndexMirror(a : seq<int>) 
  requires isPalindrome(a)
  requires |a| > 0
  ensures forall i :: 0 <= i < |a| ==> a[i] == a[|a| - 1 - i]
{

}

function palindromeSplit<T>(a : seq<T>) : (int, int)
{
  ((|a| + 1) / 2, |a|/2)
}

lemma palindromeSplitHighLow<T>(a : seq<T>)
  requires |a| > 0
  ensures (var (hi,lo) := palindromeSplit(a);
    hi >= lo
  )
{}

function pointless<T>(a : seq<T>) : int{
  0
}

method iterPalindrome(a : seq<int>) returns (b: bool)
  requires |a| > 1
{
  var hi, lo := (|a| + 1) / 2, |a|/2;
  
  var lo_to_check := lo - 1;
  var hi_to_check := hi;

  assert hi_to_check >= lo_to_check + 1;

  assert isPalindrome(a[lo_to_check + 1..hi_to_check]);

  while lo_to_check >= 0 && hi_to_check < |a|
    invariant lo_to_check + 1 <= hi_to_check
    invariant lo_to_check + 1 >= 0
    invariant hi_to_check <= |a|
    invariant isPalindrome(a[lo_to_check+1..hi_to_check])
  {
    if(a[lo_to_check] != a[hi_to_check]){
      break;
    }
    ghost var lo_to_check' := lo_to_check;
    lo_to_check := lo_to_check - 1;
    ghost var hi_to_check' := hi_to_check;
    hi_to_check := hi_to_check + 1;

    assert a[lo_to_check'] == a[hi_to_check'];
    assert isPalindrome(a[lo_to_check'+1..hi_to_check']);  

    ghost var new_pal := a[lo_to_check+1..hi_to_check];
    assert new_pal[0..|new_pal|-1] == a[lo_to_check+1..hi_to_check-1];
    calc{
      a[lo_to_check'] == a[hi_to_check'] && isPalindrome(a[lo_to_check'+1..hi_to_check']);
    ==
      a[lo_to_check+1] == a[hi_to_check-1] && isPalindrome(a[lo_to_check'+1..hi_to_check']);
    }
    assert new_pal[0] == a[lo_to_check+1];
    assert new_pal[|new_pal|-1] == a[hi_to_check-1];
    assert new_pal[1..|new_pal|] == a[lo_to_check'+1..hi_to_check];
    assert new_pal[1..|new_pal|-1] == a[lo_to_check'+1..hi_to_check-1];

    assert hi_to_check >= lo_to_check + 1;
    assert lo_to_check+1 >= 0;
  }

  assert isPalindrome(a[lo_to_check+1..hi_to_check]);
  assert lo_to_check+1 == 0 && hi_to_check == |a| ==> a[lo_to_check+1..hi_to_check] == a;
  b := lo_to_check+1 == 0 && hi_to_check == |a|;
}

/*lemma reversedHalvesPalindrome(a : seq<int>)
  requires |a| > 1
  requires isPalindrome(a)
  /*ensures (var hi, lo := (|a| + 1) / 2, |a|/2; 
    a[0..lo] == Reverse(a[hi..|a|]))*/
{
  if |a| == 1{
    
  }else{
    var hi,lo := (|a| + 1)/2, |a|/2;
    if |a| % 2 == 0 {
      assert lo == hi;
      palindromeIndexMirror(a);
      calc{
        a[lo - 1] == a[|a| - 1 - (lo - 1)];
      ==
        a[lo - 1] == a[|a| - lo];
      ==
        a[lo - 1] == a[|a| - hi];
      }
      assert hi == |a|/2;
      calc{
        |a| - hi;
      ==
        |a| - |a|/2;
      ==
        |a|/2;
      }
      assert a[|a| - hi] == a[|a|/2];
      assert a[|a| - hi] == a[hi];

    }
  }
}*/

method test(){
  var a := [1,2,3,4,3,2,1];
  assert isPalindrome([]);
}