function searchFunctional(s : seq<int>, t : int, i : nat) : nat
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then
    |s|
  else if s[i] == t then
    i
  else
    searchFunctional(s, t, i + 1)
}

function searchFunctionalAux(s : seq<int>, t : int) : int
{
  searchFunctional(s, t, 0)
}

method search1(s : seq<int>, t : int) returns (i : int)
  ensures -1 <= i < |s|
  ensures i == -1 ==> (forall j :: 0 <= j < |s| ==> s[j] != t)
  ensures 0 <= i < |s| ==> s[i] == t
{
  var j := 0;

  while j != |s| && s[j] != t
    invariant 0 <= j <= |s|
    invariant forall k :: 0 <= k < j ==> s[k] != t
  {
    j := j + 1;
  }

  i := if j < |s| then j else -1;
}

predicate isFirstMatch(s : seq<int>, t : int, index : nat)
  requires 0 <= index < |s|
{
  s[index] == t &&
  forall i :: 0 <= i < index ==> s[i] != t
}

predicate containsTarget(s : seq<int>, t : int){
  exists i :: 0 <= i < |s| && s[i] == t
}

method search(s : seq<int>, t : int) returns (i : int)
  ensures 0 <= i <= |s|
  ensures i == |s| || s[i] == t
  ensures i < |s| ==> (forall j :: 0<= j < i ==> s[j] != t) && s[i] == t
  ensures containsTarget(s,t) ==> i < |s|
{
  i := 0;

  while i < |s| && s[i] != t
    invariant 0 <= i <= |s|
    invariant forall j :: 0<= j < i ==> s[j] != t
  {
    i := i + 1;
  }
}

lemma searchFunctionalReturnsLenWhenNoMatch(s : seq<int>, t : int, i : nat)
  requires 0 <= i <= |s|
  requires !containsTarget(s,t)
  ensures searchFunctional(s,t,i) == |s|
  decreases |s| - i
{
  if i == |s| {

  }else{
    assert s[i] != t;
    searchFunctionalReturnsLenWhenNoMatch(s,t,i+1);
  }
}

lemma SearchFunctionalLengthWhenContains(s : seq<int>, t : int, i : nat)
  requires 0 <= i < |s|
  requires containsTarget(s[i..],t)
  ensures searchFunctional(s,t,i) < |s|
  decreases |s| - i
{
  if i == 0 {

  }else{
    if s[i] == t {

    }else if i < |s| - 1{
      SearchFunctionalLengthWhenContains(s,t,i+1);
    }
  }
}

lemma SearchFunctionalFirstMatch(s : seq<int>, t : int, i : nat)
  requires 0 <= i < |s|
  requires containsTarget(s,t)
  requires containsTarget(s[i..],t)
  requires !containsTarget(s[0..i],t)
  ensures (
    var res := searchFunctional(s,t,i);
    SearchFunctionalLengthWhenContains(s,t,i);
    isFirstMatch(s,t,res)
  )
  decreases |s| - i
{
  var res := searchFunctional(s,t,i);
  if 0 <= res < |s| {

  }
}


method test(s: seq<int>, t : int){
  if !containsTarget(s,t) {
    var r1 := search(s,t);
    var r2 := searchFunctional(s,t,0);
    searchFunctionalReturnsLenWhenNoMatch(s,t,0);
    assert r2 == |s|;
    assert r1 == |s|;
  }else{
    var r1 := search(s,t);
    var r2 := searchFunctional(s,t,0);
    assert r1 < |s|;
    SearchFunctionalLengthWhenContains(s,t,0);
    assert r2 < |s|;
    assert isFirstMatch(s,t,r1);
    SearchFunctionalFirstMatch(s,t,0);
    assert isFirstMatch(s,t,r2);
  }
}