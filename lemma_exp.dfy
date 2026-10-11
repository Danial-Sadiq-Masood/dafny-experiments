method FindZero_v1(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures index > 0 ==> index < a.Length && a[index] == 0
{
  index := -1;
  var i := 0;
  
  while i < a.Length
    invariant i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != 0
  {
    if a[i] == 0{
      index := i;
      return;
    }
    i := i + 1;
  }
}

method containsDuplicate(a : seq<int>) returns (containsDuplicate : bool)
  requires |a| > 2
  ensures containsDuplicate ==> exists i, j :: 0 <= i < j < |a| && i != j && a[i] == a[j]
{
  var s: set<int> := {};

  var i := 0;
  while i < |a| 
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> a[j] in s
    invariant forall x :: x in s ==> x in a[0..i]
  {
    if a[i] in s {
      containsDuplicate := true;
      return;
    }
    s := s + {a[i]};
    i := i + 1;
  }

  containsDuplicate := false;
}

function LongestCommonPrefix(a : string, b : string) : string
{
  if |a| == 0 || |b| == 0 then
    ""
  else if a[0] != b[0] then
    ""
  else
    [a[0]] + LongestCommonPrefix(a[1..], b[1..])
}

lemma LCPLength(a : string, b : string)
  ensures (
    var lcp := LongestCommonPrefix(a,b);
    |lcp| <= |a| && |lcp| <= |b| 
  )
{
}

lemma {:induction false} LCPCharsMatch(a : string, b : string)
  ensures (
    var lcp:= LongestCommonPrefix(a,b);
    LCPLength(a,b);
    assert |lcp| <= |a|;
    assert |lcp| <= |b|;
    forall i :: 0 <= i < |lcp| ==> a[i] == b[i]
  )
{
  if |a| == 0 {

  }else if |b| == 0 {

  }else{
    LCPCharsMatch(a[1..],b[1..]);
    var lcp:= LongestCommonPrefix(a[1..],b[1..]);

    LCPLength(a[1..],b[1..]);
    assert |lcp| <= |a[1..]|;
    assert |lcp| <= |b[1..]|;
    assert forall i :: 0 <= i < |lcp| ==> a[1..][i] == b[1..][i];
    assert forall i :: 1 <= i < |lcp| + 1 ==> a[i] == b[i];

    if a[0] == b[0]{
      var lcp' := LongestCommonPrefix(a,b);
      calc{
        LongestCommonPrefix(a,b);
      ==
        [a[0]] + LongestCommonPrefix(a[1..],b[1..]);
      }

      assert |lcp'| == |lcp| + 1;
      assert forall i :: 0 <= i < |lcp'| ==> a[i] == b[i];
    }
  }
}

predicate isCommonPrefix(p : string, a : string, b : string)
{
  |p| <= |a| && 
  |p| <= |b| && 
  forall j :: 0 <= j < |p| ==> a[j] == b[j]
}

predicate IsLongestCommonPrefix(p : string, a : string, b : string)
{
  isCommonPrefix(p,a,b) &&
  (
    |p| == |a| ||
    |p| == |b| ||
    a[|p|] != b[|p|]
  )
}

lemma RecursiveIsCommonPrefix(a : string, b : string)
  ensures isCommonPrefix(LongestCommonPrefix(a,b),a,b)
{}

lemma RecursiveIsLongestCommonPrefix(a : string, b : string)
  ensures IsLongestCommonPrefix(LongestCommonPrefix(a,b),a,b)
{}

function recursiveGeneralLCP(s : seq<string>) : string
  decreases |s|
{
  if |s| == 0
    then ""
  else if |s| == 1
    then s[0]
  else
    recursiveGeneralLCP([LongestCommonPrefix(s[0], s[1])] + s[2..])
}

predicate isGeneralCommonPrefix(lcp: string, s : seq<string>)
{
  forall i,j :: 0 <= i < j < |s| ==> isCommonPrefix(lcp, s[i], s[j])
}

lemma RecursiveGeneralStepCorrect(a : string, b : string, c : string)
  ensures recursiveGeneralLCP([a,b,c]) == recursiveGeneralLCP([recursiveGeneralLCP([a,b])] + [c])
{
}

/*lemma RecursiveGeneralStepTest(a : string, b : string, c : seq<string>)
  ensures recursiveGeneralLCP([a,b] + c) == recursiveGeneralLCP([a,b] + [recursiveGeneralLCP(c)])
{

}*/

/*lemma GeneralLCPReturnsCommonPrefix(s : seq<string>)
  decreases |s|
  ensures isGeneralCommonPrefix(recursiveGeneralLCP(s), s)
{
  if |s| == 0 {

  }else if |s| == 1{

  }else{

    var lcp1_2 := LongestCommonPrefix(s[0], s[1]);
    calc{
      recursiveGeneralLCP(s);
    ==
      recursiveGeneralLCP([LongestCommonPrefix(s[0], s[1])] + s[2..]);
    ==
      {
        GeneralLCPReturnsCommonPrefix([lcp1_2] + s[2..]);
        var lcp_rest := recursiveGeneralLCP(s[2..]); 
        assert isGeneralCommonPrefix(lcp_rest, s[2..]);
      }
      recursiveGeneralLCP([lcp1_2] + s[2..]);
    }
  }

}*/

method LCPIterative(a : string, b : string) returns (lcp: string)
  ensures isCommonPrefix(lcp,a,b)
  ensures IsLongestCommonPrefix(lcp, a, b)
{
  var res := "";

  var i := 0;
  while i < |a| && i < |b|
    invariant 0 <= i <= |a|
    invariant 0 <= i <= |b|
    invariant IsLongestCommonPrefix(res, a[0..i], b[0..i])
    invariant isCommonPrefix(res,a[0..i], b[0..i])
    invariant forall j :: 0 <= j < i ==> a[j] == b[j]
  {
    if a[i] != b[i] {
      break;
    }
    res := res + [a[i]];
    i := i + 1;
  }

  lcp := res;
}
