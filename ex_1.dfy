predicate negativeExists(a : array<int>, lo : int, hi : int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    exists i :: lo <= i < hi && a[i] < 0
}

method test(a : array<int>) returns (b :bool)
    ensures b == negativeExists(a, 0, a.Length)
{
    b := false;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant b == negativeExists(a,0,i)
        {
            if a[i] < 0 {
                b := true;
                break;
            }
            i := i + 1;
        }
}

predicate zeroExists(a : array<int>, lo : int,hi : int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    exists i :: lo <= i < hi && a[i] == 0
}

method HasZero(a: array<int>) returns (b: bool)
  ensures b == zeroExists(a, 0, a.Length)
{
    var i := 0;
    b := false;

    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant b == zeroExists(a,0,i)
    {
        if a[i] == 0 {
            b := true;
            break;
        }
        i := i + 1;
    }
}

predicate allPositive(a : array<int>, lo : int, hi : int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    forall i :: lo <= i < hi ==> a[i] >= 0    
}

method checkAllPositive(a : array<int>) returns (b : bool)
    ensures b == allPositive(a, 0, a.Length)
{
    var i := 0;
    b := true;

    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant b == allPositive(a,0,i)
    {
        if(a[i] < 0){
            b := false;
            break;
        }
        i := i + 1;
    }
}

predicate evenExists(a : array<int>, lo : int, hi : int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    exists i :: lo <= i < hi && a[i] % 2 == 0
}

method checkEvenExists(a : array<int>) returns (b : bool)
    ensures b == evenExists(a, 0, a.Length)
{
    var i := 0;
    b := false;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant b == evenExists(a,0,i)
    {
        if(a[i] % 2 == 0){
            b := true;
            break;
        }
        i := i + 1;
    }
}

function seqSum(a : seq<int>, n : int) : int
    requires 0 <= n <= |a|
    decreases n
{
    if n == 0 then 0 else seqSum(a, n - 1) + a[n - 1]
}

method prefixSum(a : seq<int>) returns (s : int)
    ensures s == seqSum(a, |a|)
{
    var i := 0;
    s := 0;

    while i < |a|
        invariant 0 <= i <= |a|
        invariant s == seqSum(a, i)
    {
        s := s + a[i];
        i := i + 1;
    }
}